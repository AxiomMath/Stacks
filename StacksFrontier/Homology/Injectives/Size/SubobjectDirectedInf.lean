module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Connected
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject

/-!
# Intersection distributes over a directed supremum of subobjects

Let `C` be a Grothendieck abelian category, `X` an object of `C`, and `s` a family of subobjects
of `X` indexed by a filtered category and monotone along its morphisms. Then intersecting with a
fixed subobject `T` of `X` commutes with the supremum of the family:

`(⨆ j, s j) ⊓ T = ⨆ j, (s j ⊓ T)`

This is the upper continuity of the subobject lattice, and it is exactly AB5: it fails for an
arbitrary family, and the directed hypothesis is what makes the supremum a filtered colimit.

## Main results

* `Stacks.Injectives.iSup_inf_of_monotone`.

## Implementation notes

The supremum of the family is its filtered colimit, by
`CategoryTheory.IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup`. Intersecting with
`T` means pulling back along the arrow of `T`, and
`CategoryTheory.Limits.IsColimit.pullbackOfHasExactColimitsOfShape` — the statement that a
colimit of a connected shape along which colimits are exact is preserved by pullback — turns the
colimit of the `s j` into a colimit whose vertex is the pullback of `T` along the arrow of
`⨆ j, s j`. Only the inequality `≤` needs this; the reverse one is formal.

The resulting colimit is used through its universal property rather than through a second
appeal to `subobjectMk_of_isColimit_eq_iSup`: the morphism witnessing
`(⨆ j, s j) ⊓ T ≤ ⨆ j, (s j ⊓ T)` is assembled from the factorizations of the legs through the
individual `s j ⊓ T`, which exist because each leg factors both through `s j`, by the pullback
projection, and through `T`, by the defining square of the pullback subobject. This avoids
having to know that the legs of the pullback colimit are monomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.Injectives

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {J : Type w} [SmallCategory J] [IsFiltered J] {X : C}

/-- A monotone family of subobjects, read as a diagram of monomorphisms over the ambient
object. -/
private def monoOverDiagram (s : J → Subobject X) (hs : ∀ {i j : J}, (i ⟶ j) → s i ≤ s j) :
    J ⥤ MonoOver X where
  obj j := MonoOver.mk (s j).arrow
  map {i j} g := MonoOver.homMk (Subobject.ofLE (s i) (s j) (hs g)) (Subobject.ofLE_arrow _)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The supremum of a monotone family of subobjects, read as a cocone on the diagram of the
family. -/
private def monoOverCocone (s : J → Subobject X) (hs : ∀ {i j : J}, (i ⟶ j) → s i ≤ s j) :
    Cocone (monoOverDiagram s hs) where
  pt := MonoOver.mk (⨆ j, s j).arrow
  ι :=
    { app j := MonoOver.homMk (Subobject.ofLE (s j) (⨆ k, s k) (le_iSup s j))
        (Subobject.ofLE_arrow _)
      naturality _ _ _ := Subsingleton.elim _ _ }

/-- **Intersection distributes over a directed supremum of subobjects.** In a Grothendieck
abelian category, for a family of subobjects of `X` indexed by a filtered category and monotone
along its morphisms, and for a fixed subobject `T` of `X`,
`(⨆ j, s j) ⊓ T = ⨆ j, (s j ⊓ T)`.

This is the upper continuity of the subobject lattice; it is AB5, and it is false for a family
that is not directed. -/
theorem iSup_inf_of_monotone (s : J → Subobject X) (hs : ∀ {i j : J}, (i ⟶ j) → s i ≤ s j)
    (T : Subobject X) : (⨆ j, s j) ⊓ T = ⨆ j, (s j ⊓ T) := by
  refine le_antisymm ?_ (iSup_le fun j => inf_le_inf_right T (le_iSup s j))
  have hmono : Mono ((MonoOver.forget X).mapCocone (monoOverCocone s hs)).pt.hom :=
    Subobject.arrow_mono _
  have hsup : Subobject.mk ((MonoOver.forget X).mapCocone (monoOverCocone s hs)).pt.hom =
      ⨆ j, Subobject.mk ((monoOverDiagram s hs).obj j).obj.hom := by
    simp [monoOverDiagram, monoOverCocone]
  have hcB := IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup
    (monoOverDiagram s hs) ((MonoOver.forget X).mapCocone (monoOverCocone s hs)) hsup
  have : IsConnected J := IsFiltered.isConnected J
  set S : Subobject X := ⨆ j, s j with hS
  set R : Subobject X := ⨆ j, (s j ⊓ T) with hR
  set P : Subobject (Subobject.underlying.obj S) := (Subobject.pullback S.arrow).obj T with hP
  have hpb := IsColimit.pullbackOfHasExactColimitsOfShape hcB P.arrow
  set c := (Over.forget X).mapCocone ((MonoOver.forget X).mapCocone (monoOverCocone s hs))
    with hc
  set fstN := pullback.fst c.ι ((Functor.const J).map P.arrow) with hfst
  set sndN := pullback.snd c.ι ((Functor.const J).map P.arrow) with hsnd
  have hleg : ∀ j, c.ι.app j ≫ S.arrow = (s j).arrow := fun j => Subobject.ofLE_arrow _
  have hcond : ∀ j, fstN.app j ≫ c.ι.app j = sndN.app j ≫ P.arrow := fun j =>
    NatTrans.congr_app (pullback.condition (f := c.ι)
      (g := (Functor.const J).map P.arrow)) j
  have hsq : ∀ j, fstN.app j ≫ (s j).arrow = sndN.app j ≫ P.arrow ≫ S.arrow := fun j =>
    ((congrArg (fun t => fstN.app j ≫ t) (hleg j)).symm.trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ S.arrow) (hcond j)).trans (Category.assoc _ _ _))))
  have hPS : Subobject.pullbackπ S.arrow T ≫ T.arrow = P.arrow ≫ S.arrow :=
    (Subobject.isPullback S.arrow T).w
  have hfac : ∀ j, (s j ⊓ T).Factors (fstN.app j ≫ (s j).arrow) := by
    intro j
    have heq : fstN.app j ≫ (s j).arrow
        = (sndN.app j ≫ Subobject.pullbackπ S.arrow T) ≫ T.arrow := by
      rw [hsq, ← hPS, Category.assoc]
    refine (Subobject.inf_factors _).2 ⟨Subobject.factors_comp_arrow _, ?_⟩
    rw [heq]
    exact Subobject.factors_comp_arrow _
  set k : ∀ j, (pullback c.ι ((Functor.const J).map P.arrow)).obj j ⟶
      Subobject.underlying.obj R :=
    fun j => (s j ⊓ T).factorThru _ (hfac j) ≫
      Subobject.ofLE (s j ⊓ T) R (le_iSup (fun j => s j ⊓ T) j) with hk
  have hkR : ∀ j, k j ≫ R.arrow = fstN.app j ≫ (s j).arrow := by
    intro j
    rw [hk, Category.assoc, Subobject.ofLE_arrow, Subobject.factorThru_arrow]
  set cR : Cocone (pullback c.ι ((Functor.const J).map P.arrow)) :=
    { pt := Subobject.underlying.obj R
      ι :=
        { app := k
          naturality := by
            intro i j g
            have key : (pullback c.ι ((Functor.const J).map P.arrow)).map g ≫ k j = k i := by
              rw [← cancel_mono R.arrow, Category.assoc, hkR, hkR]
              exact (Category.assoc _ _ _).symm.trans
                ((congrArg (fun t => t ≫ (s j).arrow) (fstN.naturality g)).trans
                  ((Category.assoc _ _ _).trans
                    (congrArg (fun t => fstN.app i ≫ t) (Subobject.ofLE_arrow _))))
            simpa using key } } with hcR
  have hdesc : hpb.desc cR ≫ R.arrow = P.arrow ≫ S.arrow := by
    refine hpb.hom_ext fun j => ?_
    have h1 : sndN.app j ≫ hpb.desc cR ≫ R.arrow = k j ≫ R.arrow := by
      rw [← Category.assoc]
      exact congrArg (fun t => t ≫ R.arrow) (hpb.fac cR j)
    rw [h1, hkR, hsq]
  refine Subobject.le_of_comm (Y := R)
    ((Subobject.isPullback S.arrow T).lift (Subobject.ofLE (S ⊓ T) T inf_le_right)
      (Subobject.ofLE (S ⊓ T) S inf_le_left)
      (by rw [Subobject.ofLE_arrow, Subobject.ofLE_arrow]) ≫ hpb.desc cR) ?_
  rw [Category.assoc, hdesc, ← Category.assoc, IsPullback.lift_snd, Subobject.ofLE_arrow]

end Stacks.Injectives

end
