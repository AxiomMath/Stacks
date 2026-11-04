module

public import StacksFrontier.CategoryTheory.Functor.Derived.ComparisonSquareChaseHomotopy

/-!
# A pasted base change cocycle on complexes, with every factor ascribed

A cocycle of four natural isomorphisms between composites of functors — a contraction `cU` of two
pullbacks, two base change isomorphisms `ρ` and `σ`, a contraction `δ` of two extensions of
scalars, and a base change isomorphism `κ` for the composite — passes to complexes degreewise.
This file records that passage with **every factor in the ascribed spelling** of
`CategoryTheory.Functor.mapHomologicalComplexCompIso`: a base change isomorphism
`ρ : tR ⋙ pf ≅ ef ⋙ tS` is read on complexes not as
`CategoryTheory.NatIso.mapHomologicalComplex ρ c`, whose type is `(tR ⋙ pf)^• ≅ (ef ⋙ tS)^•`, but
as

`mapHomologicalComplexCompIso ρ c ≪≫ (mapHomologicalComplexCompIso (Iso.refl (ef ⋙ tS)) c).symm`,

whose type is `tR^• ⋙ pf^• ≅ ef^• ⋙ tS^•`.  That is the spelling in which a degreewise base change
isomorphism of sheaves of modules on an algebraic space is actually constructed, because the two
conversions identifying `(F ⋙ G)^•` with `F^• ⋙ G^•` are then performed once, in Mathlib, where
the functors are variables; written at the concrete functors each such conversion unfolds the
construction of an inverse image of sheaves of modules and costs more than the whole heartbeat
budget.

Everything here is stated for arbitrary categories and functors, and that is the point: the
degreewise check needs the identification of the term of degree `n` of a degreewise image of a
complex with the image of the term of degree `n`, together with the cancellation of the identity
that the ascribed spelling leaves behind.  With the functors kept as variables nothing can unfold
and both are structural; attempted on the concrete functors, every spelling of the same step —
`rw` of the three degreewise lemmas, a rewrite by the contracted lemma, an `exact` of it with all
instances pinned — costs between 200,000 and 285,000 heartbeats and fails.

## Main results

* `StacksDraft.ComparisonSquare.compIso_trans_refl_symm_hom_app_f`: the ascribed spelling of a
  base change isomorphism, read in a single degree, is the component of the isomorphism itself.
* `StacksDraft.ComparisonSquare.mapHomologicalComplexCompIso_cocycle_trans`: the cocycle passes to
  complexes, with every factor in the ascribed spelling.

## Implementation notes

The hypothesis of
`StacksDraft.ComparisonSquare.mapHomologicalComplexCompIso_cocycle_trans` is the cocycle at an
object, in exactly the shape
`Stacks.CategoryTheory.BaseChange.pastedBaseChangeIso_hom_app_of_eq` concludes it, so that a
pasting of two underived base change isomorphisms discharges it with no reformulation.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace StacksDraft.ComparisonSquare

section Degree

variable {V W W' V' : Type*} [Category* V] [Category* W] [Category* W'] [Category* V']
  [Preadditive V] [Preadditive W] [Preadditive W'] [Preadditive V']

/-- **A base change isomorphism in the ascribed spelling, read in a single degree.**  The
comparison of the induced functors for `e`, followed by the inverse of the comparison at an
identity, is at every complex and in every degree the component of `e`.

The second factor is the one that reconciles `(E ⋙ A)^•` with `E^• ⋙ A^•`; it is an identity in
every degree, and cancelling it is the only content here. -/
theorem compIso_trans_refl_symm_hom_app_f {F : V ⥤ W} {G : W ⥤ W'} {E : V ⥤ V'} {A : V' ⥤ W'}
    [instF : F.Additive] [instG : G.Additive] [instE : E.Additive] [instA : A.Additive]
    [instEA : (E ⋙ A).Additive] (e : F ⋙ G ≅ E ⋙ A) (c : ComplexShape ℤ)
    (M : HomologicalComplex V c) (n : ℤ) :
    ((Functor.mapHomologicalComplexCompIso e c ≪≫
          (Functor.mapHomologicalComplexCompIso (F := E) (G := A)
            (Iso.refl _) c).symm).hom.app M).f n =
      e.hom.app (M.X n) := by
  rw [Iso.trans_hom, NatTrans.comp_app, HomologicalComplex.comp_f, Iso.symm_hom,
    mapHomologicalComplexCompIso_refl_inv_app_f, Category.comp_id,
    mapHomologicalComplexCompIso_hom_app_f]

end Degree

section Cocycle

variable {A A' Bc Bc' D D' : Type*} [Category* A] [Category* A'] [Category* Bc] [Category* Bc']
  [Category* D] [Category* D'] [Preadditive A] [Preadditive A'] [Preadditive Bc]
  [Preadditive Bc'] [Preadditive D] [Preadditive D']
  {tR : A ⥤ A'} {tS : Bc ⥤ Bc'} {tT : D ⥤ D'} {pf : A' ⥤ Bc'} {pg : Bc' ⥤ D'} {pk : A' ⥤ D'}
  {ef : A ⥤ Bc} {eg : Bc ⥤ D} {ek : A ⥤ D}
  [instTR : tR.Additive] [instTS : tS.Additive] [instTT : tT.Additive] [instPF : pf.Additive]
  [instPG : pg.Additive] [instPK : pk.Additive] [instEF : ef.Additive] [instEG : eg.Additive]
  [instEK : ek.Additive]

/-- **A pasted base change cocycle passes to complexes, with every factor in the ascribed
spelling.**  If at every object the contraction `cU` of the two pullbacks, the base change
isomorphism `ρ`, the base change isomorphism `σ` and the contraction `δ` of the two extensions of
scalars compose to the base change isomorphism `κ` of the composite, then the same holds on
complexes, with each of `ρ`, `σ` and `κ` read in the ascribed spelling and `cU` and `δ` read as
comparisons of the induced functors.

The hypothesis is the cocycle at an object in the shape
`Stacks.CategoryTheory.BaseChange.pastedBaseChangeIso_hom_app_of_eq` concludes it. -/
theorem mapHomologicalComplexCompIso_cocycle_trans (c : ComplexShape ℤ) (cU : pf ⋙ pg ≅ pk)
    (ρ : tR ⋙ pf ≅ ef ⋙ tS) (σ : tS ⋙ pg ≅ eg ⋙ tT) (δ : ef ⋙ eg ≅ ek)
    (κ : tR ⋙ pk ≅ ek ⋙ tT)
    (h : ∀ N : A, cU.inv.app (tR.obj N) ≫ pg.map (ρ.hom.app N) ≫ σ.hom.app (ef.obj N) ≫
      tT.map (δ.hom.app N) = κ.hom.app N)
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
  comp_four_hom_ext _ _ _ _ _ fun n => by
    rw [mapHomologicalComplexCompIso_inv_app_f, Functor.mapHomologicalComplex_map_f,
      compIso_trans_refl_symm_hom_app_f, compIso_trans_refl_symm_hom_app_f,
      Functor.mapHomologicalComplex_map_f, mapHomologicalComplexCompIso_hom_app_f,
      compIso_trans_refl_symm_hom_app_f]
    exact h (M.X n)

end Cocycle

end StacksDraft.ComparisonSquare

end
