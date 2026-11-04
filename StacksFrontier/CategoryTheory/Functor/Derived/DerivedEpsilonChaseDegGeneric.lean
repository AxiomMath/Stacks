module

public import StacksFrontier.CategoryTheory.Functor.Derived.DerivedEpsilonChaseComplexCocycle
public import StacksFrontier.CategoryTheory.Functor.Derived.PastedBaseChangeCocycle

/-!
# The pasted base change cocycle on complexes, from the pasting itself

`StacksDraft.ComparisonSquare.mapHomologicalComplexCompIso_cocycle_trans` takes as its hypothesis
the base change cocycle *at an object*, which
`Stacks.CategoryTheory.BaseChange.pastedBaseChangeIso_hom_app_of_eq` derives from the pasting of
the two base change isomorphisms along the two contractions.  This file composes the two, so that
the degreewise cocycle follows from the pasting in one step, and records two transport lemmas a
consumer of it needs.

Composing them here rather than at the consumer is what makes the concrete instance affordable.
Handed the cocycle at an object as a last argument, against isomorphisms already fixed by the
earlier ones, the elaborator must identify two four-factor cocycles that print character for
character identically and differ only in their invisible instances; at degreewise inverse images of
sheaves of modules on algebraic spaces that `isDefEq` does not terminate inside the heartbeat
budget, in either argument order and with the category, preadditive and additivity instances
supplied by hand on either side.  Handed the pasting first, with the five isomorphisms implicit,
nothing is checked at all: the pasting *determines* the nine functors, the five isomorphisms and
every instance in them by matching.

No hypotheses are carried: the statement is unconditional, with the pasting as its one
mathematical input.

## Main results

* `StacksDraft.ComparisonSquare.mapHomologicalComplexCompIso_cocycle_trans_pasted`: the degreewise
  cocycle, from the pasting of the two underived base change isomorphisms along the two
  contractions.
* `StacksDraft.ComparisonSquare.inv_app_congr` and
  `StacksDraft.ComparisonSquare.functor_map_congr`: an equation of isomorphisms read backwards at
  an object, and an equation of morphisms read under a functor.  Both exist so that a consumer can
  transport along an equation of *isomorphisms* instead of asking the elaborator to identify two
  spellings of one isomorphism underneath an `CategoryTheory.Iso.inv` projection: projecting forces
  the isomorphism to a constructor application, which at inverse images of sheaves of modules
  unfolds their construction and costs more than the whole heartbeat budget, while the equation of
  the two isomorphisms themselves is a single delta step.

## Implementation notes

The cocycle's conclusion keeps the ascribed spelling

`mapHomologicalComplexCompIso ρ c ≪≫ (mapHomologicalComplexCompIso (Iso.refl _) c).symm`

of each of its three base change isomorphisms, rather than taking them as arguments pinned by
equations to the named definitions a consumer holds.  Pinning them was tried and does not help: the
equations themselves are cheap, but identifying the resulting conclusion with any locally written
statement of the same proposition is the check that diverges, and it diverges at either spelling.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace StacksDraft.ComparisonSquare

/-- **Two equal isomorphisms of functors have equal inverse components.**  The companion of
`StacksDraft.ComparisonSquare.hom_app_congr`. -/
theorem inv_app_congr {D E : Type*} [Category* D] [Category* E] {F G : D ⥤ E} {e₁ e₂ : F ≅ G}
    (he : e₁ = e₂) (X : D) : e₁.inv.app X = e₂.inv.app X := by rw [he]

/-- **Two equal morphisms have equal images under a functor.** -/
theorem functor_map_congr {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E) {X Y : D}
    {φ ψ : X ⟶ Y} (hφ : φ = ψ) : F.map φ = F.map ψ := by rw [hφ]

variable {A A' Bc Bc' D D' : Type*} [instCatA : Category* A] [instCatA' : Category* A']
  [instCatBc : Category* Bc] [instCatBc' : Category* Bc'] [instCatD : Category* D]
  [instCatD' : Category* D'] [instPreA : Preadditive A] [instPreA' : Preadditive A']
  [instPreBc : Preadditive Bc] [instPreBc' : Preadditive Bc'] [instPreD : Preadditive D]
  [instPreD' : Preadditive D']
  {tR : A ⥤ A'} {tS : Bc ⥤ Bc'} {tT : D ⥤ D'} {pf : A' ⥤ Bc'} {pg : Bc' ⥤ D'} {pk : A' ⥤ D'}
  {ef : A ⥤ Bc} {eg : Bc ⥤ D} {ek : A ⥤ D}
  [instTR : tR.Additive] [instTS : tS.Additive] [instTT : tT.Additive] [instPF : pf.Additive]
  [instPG : pg.Additive] [instPK : pk.Additive] [instEF : ef.Additive] [instEG : eg.Additive]
  [instEK : ek.Additive]

/-- **The pasted base change cocycle on complexes, from the pasting itself.**
`StacksDraft.ComparisonSquare.mapHomologicalComplexCompIso_cocycle_trans` with its hypothesis
replaced by the pasting of the two base change isomorphisms along the two contractions — the
hypothesis of `Stacks.CategoryTheory.BaseChange.pastedBaseChangeIso_hom_app_of_eq`, which this
declaration applies — and with that pasting as the *first* argument, the five isomorphisms it
mentions left implicit.

Both choices are load-bearing; see the implementation note at the head of this file. -/
theorem mapHomologicalComplexCompIso_cocycle_trans_pasted (c : ComplexShape ℤ)
    {cU : pf ⋙ pg ≅ pk} {ρ : tR ⋙ pf ≅ ef ⋙ tS} {σ : tS ⋙ pg ≅ eg ⋙ tT} {δ : ef ⋙ eg ≅ ek}
    {κ : tR ⋙ pk ≅ ek ⋙ tT}
    (hcoh : Functor.isoWhiskerLeft tR cU.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ρ pg ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft ef σ ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight δ tT = κ)
    (M : HomologicalComplex A c) :
    (Functor.mapHomologicalComplexCompIso cU c).inv.app ((tR.mapHomologicalComplex c).obj M) ≫
        (pg.mapHomologicalComplex c).map
          ((Functor.mapHomologicalComplexCompIso ρ c ≪≫
            (Functor.mapHomologicalComplexCompIso (F := ef) (G := tS)
              (Iso.refl _) c).symm).hom.app M) ≫
        (Functor.mapHomologicalComplexCompIso σ c ≪≫
            (Functor.mapHomologicalComplexCompIso (F := eg) (G := tT)
              (Iso.refl _) c).symm).hom.app ((ef.mapHomologicalComplex c).obj M) ≫
        (tT.mapHomologicalComplex c).map
          ((Functor.mapHomologicalComplexCompIso δ c).hom.app M) =
      (Functor.mapHomologicalComplexCompIso κ c ≪≫
        (Functor.mapHomologicalComplexCompIso (F := ek) (G := tT)
          (Iso.refl _) c).symm).hom.app M :=
  mapHomologicalComplexCompIso_cocycle_trans c cU ρ σ δ κ
    (Stacks.CategoryTheory.BaseChange.pastedBaseChangeIso_hom_app_of_eq cU δ ρ σ κ hcoh) M

end StacksDraft.ComparisonSquare

end
