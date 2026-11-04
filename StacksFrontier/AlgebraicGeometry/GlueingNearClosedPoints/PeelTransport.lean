module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Peel

/-!
# Transporting the glueing data of a subfamily across the peeled square

The induction which proves [Stacks, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q) peels
one square off a family of commutative squares indexed by `Option J`.  The family is read over
an intermediate ambient scheme `W` sitting between the open `U` and the base `T`, and
`AlgebraicGeometry.assembleGlueingData` turns *nested* glueing data — glueing data for the
subfamily whose component over `W` has itself been decomposed by the square at `none` — into
glueing data for the whole family.

What is still missing is that glueing data for the subfamily, taken in its own right over `W`,
*is* nested glueing data.  The two differ only in the overlaps: the subfamily's own overlap at
`some j` sits over `W`, while the nested datum records the overlap `O (some j)` of the whole
family.  In the geometric situation these two opens coincide, and this file transports glueing
data across an abstract family of isomorphisms `τ j : O (some j) ≅ OW j` identifying them.

The transport is `AlgebraicGeometry.isoCommaMap` along the identity on both outer categories and
base change along the `τ j` on the category of overlaps, so it is an equivalence.

With that in hand the whole induction step falls out: the canonical functor of the subfamily,
followed by the transport and by `AlgebraicGeometry.assembleGlueingData`, is the canonical
functor of the whole family, so the latter is an equivalence as soon as the canonical functor
of the subfamily and the canonical functor of the square at `none` both are.

## Main definitions

* `AlgebraicGeometry.finitePresentationBaseChangeCompOfEq`: base change along two composable
  morphisms whose composite is a given morphism.
* `AlgebraicGeometry.peelTransport`: glueing data for the subfamily over `W` read as nested
  glueing data for the whole family.
* `AlgebraicGeometry.peelTransportAssembleIso`: the canonical functor of the subfamily,
  transported and assembled, is the canonical functor of the whole family.

## Main results

* `AlgebraicGeometry.peelTransport_isEquivalence`: that reading is an equivalence of categories.
* `AlgebraicGeometry.restrictionFunctorOf_isEquivalence_of_peel`: the induction step of
  Tag 0E8Q for a family of commutative squares indexed by `Option J`.

## Implementation notes

The comparison isomorphisms of the coherence are the base-change comparison for a composite,
once over the open and once over the local scheme at the peeled point, and the identity over
the remaining local schemes.  Both compatibilities are instances of one pasting coherence for
`AlgebraicGeometry.finitePresentationPullbackSquareIso`, and both are checked by composing with
the projections down to the scheme being restricted, where each side becomes the same triple
projection out of the iterated pullback along `cW`, `cUW` and the overlap map.

## References

* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Base change along two composable morphisms whose composite is a given morphism. -/
noncomputable def finitePresentationBaseChangeCompOfEq {S T W : Scheme.{u}} {f : W ⟶ T}
    {g : T ⟶ S} {k : W ⟶ S} (hk : f ≫ g = k) :
    finitePresentationBaseChange g ⋙ finitePresentationBaseChange f ≅
      finitePresentationBaseChange k := by
  subst hk
  exact finitePresentationBaseChangeComp f g

/-- The comparison isomorphism for base change along a composite commutes with the projections
to the scheme being restricted. -/
@[reassoc]
theorem finitePresentationBaseChangeCompOfEq_hom_app_hom_left_fst {S T W : Scheme.{u}}
    {f : W ⟶ T} {g : T ⟶ S} {k : W ⟶ S} (hk : f ≫ g = k) (X : FinitePresentationOver S) :
    ((finitePresentationBaseChangeCompOfEq hk).hom.app X).hom.left ≫ pullback.fst X.obj.hom k =
      pullback.fst (pullback.snd X.obj.hom g) f ≫ pullback.fst X.obj.hom g := by
  subst hk
  exact finitePresentationBaseChangeComp_hom_app_hom_left_fst f g X

/-! ### Transporting glueing data of the subfamily -/

section PeelTransport

variable {U W : Scheme.{u}} {J : Type u} {L O : Option J → Scheme.{u}} {OW : J → Scheme.{u}}
  {cUW : U ⟶ W} {a : ∀ i, O i ⟶ U} {b : ∀ i, O i ⟶ L i} {aW : ∀ j, OW j ⟶ W}
  {bW : ∀ j, OW j ⟶ L (some j)} (τ : ∀ j, O (some j) ≅ OW j)

/-- Comparison of the two restrictions of a scheme over `W` to the overlaps of the whole
family. -/
noncomputable def peelTransportLeftIso
    (hτa : ∀ j, (τ j).hom ≫ aW j = a (some j) ≫ cUW) :
    𝟭 (FinitePresentationOver W) ⋙
        (finitePresentationBaseChange cUW ⋙
          Functor.pi' fun j ↦ finitePresentationBaseChange (a (some j))) ≅
      (Functor.pi' fun j ↦ finitePresentationBaseChange (aW j)) ⋙
        Functor.pi fun j ↦ finitePresentationBaseChange (τ j).hom :=
  NatIso.pi' fun j ↦ (finitePresentationPullbackSquareIso (hτa j)).symm

/-- Comparison of the two restrictions of a family of schemes over the `L (some j)` to the
overlaps of the whole family. -/
noncomputable def peelTransportRightIso (hτb : ∀ j, (τ j).hom ≫ bW j = b (some j)) :
    (Functor.pi fun j ↦ finitePresentationBaseChange (bW j)) ⋙
        (Functor.pi fun j ↦ finitePresentationBaseChange (τ j).hom) ≅
      𝟭 ((j : J) → FinitePresentationOver (L (some j))) ⋙
        (Functor.pi fun j ↦ finitePresentationBaseChange (b (some j))) :=
  NatIso.pi' fun j ↦ Functor.isoWhiskerLeft
    (Pi.eval (fun j ↦ FinitePresentationOver (L (some j))) j)
    (finitePresentationBaseChangeCompOfEq (hτb j))

/-- The transport of the glueing data of the subfamily, read over the intermediate ambient
scheme `W`, into nested glueing data: the overlaps of the subfamily are identified with the
overlaps of the whole family. -/
noncomputable def peelTransport (hτa : ∀ j, (τ j).hom ≫ aW j = a (some j) ≫ cUW)
    (hτb : ∀ j, (τ j).hom ≫ bW j = b (some j)) :
    glueingDataOf aW bW ⥤ nestedGlueingData cUW a b :=
  isoCommaMap (F₁ := 𝟭 _) (F₂ := 𝟭 _)
    (F := Functor.pi fun j ↦ finitePresentationBaseChange (τ j).hom)
    (peelTransportLeftIso τ hτa).hom (peelTransportRightIso τ hτb).hom

/-- The transport of glueing data along an isomorphism of the overlaps is an equivalence. -/
theorem peelTransport_isEquivalence (hτa : ∀ j, (τ j).hom ≫ aW j = a (some j) ≫ cUW)
    (hτb : ∀ j, (τ j).hom ≫ bW j = b (some j)) :
    (peelTransport τ hτa hτb).IsEquivalence := by
  have : ∀ j, (finitePresentationBaseChange (τ j).hom).IsEquivalence :=
    fun j ↦ finitePresentationBaseChange_isEquivalence_of_isIso (τ j).hom
  exact isoCommaMap_isEquivalence _ _

end PeelTransport

/-! ### The canonical functor of the whole family, through the subfamily -/

section Coherence

variable {T U W : Scheme.{u}} {J : Type u} {L O : Option J → Scheme.{u}} {OW : J → Scheme.{u}}
  {c : U ⟶ T} {cW : W ⟶ T} {cUW : U ⟶ W} {d : ∀ i, L i ⟶ T} {d₀ : L none ⟶ W}
  {a : ∀ i, O i ⟶ U} {b : ∀ i, O i ⟶ L i} {aW : ∀ j, OW j ⟶ W} {bW : ∀ j, OW j ⟶ L (some j)}
  (τ : ∀ j, O (some j) ≅ OW j)
  (hτa : ∀ j, (τ j).hom ≫ aW j = a (some j) ≫ cUW)
  (hτb : ∀ j, (τ j).hom ≫ bW j = b (some j))
  (hc : cUW ≫ cW = c) (hd₀ : d₀ ≫ cW = d none)
  (h₀ : a none ≫ cUW = b none ≫ d₀)
  (hW : ∀ j, aW j ≫ cW = bW j ≫ d (some j))
  (h : ∀ i, a i ≫ c = b i ≫ d i)

/-- The canonical functor of the subfamily of commutative squares, followed by the reading of
its glueing data as nested glueing data and the assembly of that into glueing data for the whole
family, is the canonical functor of the whole family. -/
noncomputable def peelTransportAssembleIso :
    restrictionFunctorOf cW (fun j ↦ d (some j)) aW bW hW ⋙
        (peelTransport τ hτa hτb ⋙ assembleGlueingData cUW d₀ a b h₀) ≅
      restrictionFunctorOf c d a b h := by
  refine NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ (Comma.isoMk
    ((finitePresentationBaseChangeCompOfEq hc).app X)
    (Pi.isoMk (optionIso ((finitePresentationBaseChangeCompOfEq hd₀).app X)
      (fun j ↦ Iso.refl _))) (funext fun i ↦ ?_))) ?_
  · cases i with
    | none =>
      change (finitePresentationBaseChange (a none)).map
            ((finitePresentationBaseChangeCompOfEq hc).hom.app X) ≫
          (finitePresentationPullbackSquareIso (h none)).hom.app X =
        (finitePresentationPullbackSquareIso h₀).hom.app
            ((finitePresentationBaseChange cW).obj X) ≫
          (finitePresentationBaseChange (b none)).map
            ((finitePresentationBaseChangeCompOfEq hd₀).hom.app X)
      have hf : ((finitePresentationBaseChange (a none)).map
              ((finitePresentationBaseChangeCompOfEq hc).hom.app X) ≫
            (finitePresentationPullbackSquareIso (h none)).hom.app X).hom.left ≫
          pullback.fst (pullback.snd X.obj.hom (d none)) (b none) ≫
            pullback.fst X.obj.hom (d none) =
          pullback.fst (pullback.snd (pullback.snd X.obj.hom cW) cUW) (a none) ≫
            pullback.fst (pullback.snd X.obj.hom cW) cUW ≫ pullback.fst X.obj.hom cW := by
        simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc,
          finitePresentationPullbackSquareIso_hom_app_hom_left_fst]
        exact (finitePresentationBaseChange_map_hom_left_fst_assoc (a none)
            ((finitePresentationBaseChangeCompOfEq hc).hom.app X)
            (pullback.fst X.obj.hom c)).trans
          (whisker_eq _ (finitePresentationBaseChangeCompOfEq_hom_app_hom_left_fst hc X))
      have hg : ((finitePresentationPullbackSquareIso h₀).hom.app
              ((finitePresentationBaseChange cW).obj X) ≫
            (finitePresentationBaseChange (b none)).map
              ((finitePresentationBaseChangeCompOfEq hd₀).hom.app X)).hom.left ≫
          pullback.fst (pullback.snd X.obj.hom (d none)) (b none) ≫
            pullback.fst X.obj.hom (d none) =
          pullback.fst (pullback.snd (pullback.snd X.obj.hom cW) cUW) (a none) ≫
            pullback.fst (pullback.snd X.obj.hom cW) cUW ≫ pullback.fst X.obj.hom cW := by
        simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc]
        have step1 := (finitePresentationBaseChange_map_hom_left_fst_assoc (b none)
            ((finitePresentationBaseChangeCompOfEq hd₀).hom.app X)
            (pullback.fst X.obj.hom (d none))).trans
          (whisker_eq (pullback.fst (pullback.snd (pullback.snd X.obj.hom cW) d₀) (b none))
            (finitePresentationBaseChangeCompOfEq_hom_app_hom_left_fst hd₀ X))
        exact (whisker_eq _ step1).trans
          (finitePresentationPullbackSquareIso_hom_app_hom_left_fst_assoc h₀
            ((finitePresentationBaseChange cW).obj X) (pullback.fst X.obj.hom cW))
      exact ObjectProperty.hom_ext _
        (over_hom_ext_of_pullbackSquare (h none) X.obj _ _ (hf.trans hg.symm))
    | some j =>
      change (finitePresentationBaseChange (a (some j))).map
            ((finitePresentationBaseChangeCompOfEq hc).hom.app X) ≫
          (finitePresentationPullbackSquareIso (h (some j))).hom.app X =
        ((finitePresentationPullbackSquareIso (hτa j)).inv.app
              ((finitePresentationBaseChange cW).obj X) ≫
            (finitePresentationBaseChange (τ j).hom).map
              ((finitePresentationPullbackSquareIso (hW j)).hom.app X) ≫
            (finitePresentationBaseChangeCompOfEq (hτb j)).hom.app
              ((finitePresentationBaseChange (d (some j))).obj X)) ≫
          (finitePresentationBaseChange (b (some j))).map (𝟙 _)
      rw [CategoryTheory.Functor.map_id]
      refine Eq.trans ?_ (Category.comp_id _).symm
      have hf : ((finitePresentationBaseChange (a (some j))).map
              ((finitePresentationBaseChangeCompOfEq hc).hom.app X) ≫
            (finitePresentationPullbackSquareIso (h (some j))).hom.app X).hom.left ≫
          pullback.fst (pullback.snd X.obj.hom (d (some j))) (b (some j)) ≫
            pullback.fst X.obj.hom (d (some j)) =
          pullback.fst (pullback.snd (pullback.snd X.obj.hom cW) cUW) (a (some j)) ≫
            pullback.fst (pullback.snd X.obj.hom cW) cUW ≫ pullback.fst X.obj.hom cW := by
        simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc,
          finitePresentationPullbackSquareIso_hom_app_hom_left_fst]
        exact (finitePresentationBaseChange_map_hom_left_fst_assoc (a (some j))
            ((finitePresentationBaseChangeCompOfEq hc).hom.app X)
            (pullback.fst X.obj.hom c)).trans
          (whisker_eq _ (finitePresentationBaseChangeCompOfEq_hom_app_hom_left_fst hc X))
      have hg : ((finitePresentationPullbackSquareIso (hτa j)).inv.app
                ((finitePresentationBaseChange cW).obj X) ≫
              (finitePresentationBaseChange (τ j).hom).map
                ((finitePresentationPullbackSquareIso (hW j)).hom.app X) ≫
              (finitePresentationBaseChangeCompOfEq (hτb j)).hom.app
                ((finitePresentationBaseChange (d (some j))).obj X)).hom.left ≫
          pullback.fst (pullback.snd X.obj.hom (d (some j))) (b (some j)) ≫
            pullback.fst X.obj.hom (d (some j)) =
          pullback.fst (pullback.snd (pullback.snd X.obj.hom cW) cUW) (a (some j)) ≫
            pullback.fst (pullback.snd X.obj.hom cW) cUW ≫ pullback.fst X.obj.hom cW := by
        simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc]
        have stepA := finitePresentationBaseChangeCompOfEq_hom_app_hom_left_fst_assoc (hτb j)
          ((finitePresentationBaseChange (d (some j))).obj X)
          (pullback.fst X.obj.hom (d (some j)))
        have stepB := finitePresentationBaseChange_map_hom_left_fst_assoc (τ j).hom
          ((finitePresentationPullbackSquareIso (hW j)).hom.app X)
          (pullback.fst (pullback.snd X.obj.hom (d (some j))) (bW j) ≫
            pullback.fst X.obj.hom (d (some j)))
        have stepC := finitePresentationPullbackSquareIso_hom_app_hom_left_fst (hW j) X
        have stepD := finitePresentationPullbackSquareIso_inv_app_hom_left_fst_assoc (hτa j)
          ((finitePresentationBaseChange cW).obj X) (pullback.fst X.obj.hom cW)
        exact (whisker_eq _ (whisker_eq _ stepA)).trans
          ((whisker_eq _ stepB).trans ((whisker_eq _ (whisker_eq _ stepC)).trans stepD))
      exact ObjectProperty.hom_ext _
        (over_hom_ext_of_pullbackSquare (h (some j)) X.obj _ _ (hf.trans hg.symm))
  · intro X Y f
    refine ObjectProperty.hom_ext _ (Comma.hom_ext _ _ ?_ (funext fun i ↦ ?_))
    · exact (finitePresentationBaseChangeCompOfEq hc).hom.naturality f
    · cases i with
      | none => exact (finitePresentationBaseChangeCompOfEq hd₀).hom.naturality f
      | some j =>
        change (finitePresentationBaseChange (d (some j))).map f ≫ 𝟙 _ =
          𝟙 _ ≫ (finitePresentationBaseChange (d (some j))).map f
        exact (Category.comp_id _).trans (Category.id_comp _).symm

include τ hτa hτb hc hd₀ in
/-- One step of the induction proving **Stacks Project, Tag 0E8Q** for a family of commutative
squares indexed by `Option J`: the canonical functor of the whole family is an equivalence as
soon as the canonical functor of the square at `none`, read over the intermediate ambient scheme
`W`, and the canonical functor of the subfamily, read over the base, both are. -/
theorem restrictionFunctorOf_isEquivalence_of_peel
    (hH : (restrictionFunctorOfSquare cUW d₀ h₀).IsEquivalence)
    (hG : (restrictionFunctorOf cW (fun j ↦ d (some j)) aW bW hW).IsEquivalence) :
    (restrictionFunctorOf c d a b h).IsEquivalence := by
  have := hG
  have := peelTransport_isEquivalence τ hτa hτb
  have := assembleGlueingData_isEquivalence cUW d₀ a b h₀ hH
  exact Functor.isEquivalence_of_iso (peelTransportAssembleIso τ hτa hτb hc hd₀ h₀ hW h)

end Coherence

end AlgebraicGeometry

end
