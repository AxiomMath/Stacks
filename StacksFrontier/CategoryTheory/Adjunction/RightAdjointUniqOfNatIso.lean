module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Transporting an adjunction along an isomorphism of its right adjoint

Transporting an adjunction along an isomorphism of its right adjoint
(`CategoryTheory.Adjunction.ofNatIsoRight`) changes neither the left adjoint nor, therefore, the
comparison of that left adjoint with any other.  This file records the bookkeeping identities
that let a formula written for the untransported adjunction be read for the transported one: the
transports on the two sides of an adjunction commute, and the comparison of two right adjoints
changes by the transporting isomorphism.

They are needed where one functor carries two descriptions — a construction and a comparison
isomorphism to it — and the adjunction is given for one description while a comparison of
left adjoints is given for the other.

## Main results

* `CategoryTheory.Adjunction.ofNatIsoRight_ofNatIsoLeft`
* `CategoryTheory.Adjunction.rightAdjointUniq_ofNatIsoRight_left`
* `CategoryTheory.Adjunction.rightAdjointUniq_comp_ofNatIsoRight_symm_ofNatIsoLeft_eq`: both of
  them applied in sequence, which is the form the application uses.

## Implementation notes

The identities are stated in the generality in which they are proved and then applied, once and
for all, in `rightAdjointUniq_comp_ofNatIsoRight_symm_ofNatIsoLeft_eq`.  The transport of the
second factor of a composite adjunction, which that lemma also needs, is
`CategoryTheory.Adjunction.comp_ofNatIsoRight_isoWhiskerRight` of
`StacksFrontier/CategoryTheory/Sites/Continuous/FreeAbelianLowerShriekComp.lean`; it is reproved
there as a one-line `have` rather than imported, that file being a module about sheaves which an
module about adjunctions should not depend on.  At the application
the two spellings of a category of sheaves on a simplicial component differ by their category
instance, which makes the target of the rewrite ill-typed at `instances` transparency, so
`rewrite` cannot find a pattern that is visibly present; here, where the categories are
variables, there is nothing for the transparency to get wrong.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- **The transports on the two sides of an adjunction commute.** -/
theorem ofNatIsoRight_ofNatIsoLeft {F F' : C ⥤ D} {G G' : D ⥤ C}
    (adj : F ⊣ G) (e : G ≅ G') (c : F ≅ F') :
    (adj.ofNatIsoRight e).ofNatIsoLeft c = (adj.ofNatIsoLeft c).ofNatIsoRight e :=
  Adjunction.ext (NatTrans.ext (funext fun X => by simp))

/-- **The comparison of two right adjoints, with the first adjunction transported.**  Reading the
right adjoint of the first adjunction through an isomorphism prepends the inverse of that
isomorphism to the canonical comparison with any second right adjoint of the same functor. -/
theorem rightAdjointUniq_ofNatIsoRight_left {F : C ⥤ D} {G G' G'' : D ⥤ C}
    (adj : F ⊣ G) (e : G ≅ G') (adj₂ : F ⊣ G'') :
    rightAdjointUniq (adj.ofNatIsoRight e) adj₂ = e.symm ≪≫ rightAdjointUniq adj adj₂ := by
  refine (Iso.ext (NatTrans.ext (funext fun X => ?_))).symm
  refine (adj₂.homEquiv _ X).symm.injective ?_
  rw [homEquiv_symm_rightAdjointUniq_hom_app]
  rw [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, adj₂.homEquiv_naturality_left_symm,
    homEquiv_symm_rightAdjointUniq_hom_app]
  simp

/-- **The three identities applied in sequence.**  Let `adj : F ⊣ G` and `adj' : F' ⊣ G'` be
adjunctions, `e : G'' ≅ G'` an isomorphism reading `G''` as the right adjoint of `F'`, and
`c : F ⋙ F' ≅ L` a comparison of the composite left adjoint with a functor `L` that has a right
adjoint `R` of its own.  If the comparison of the two right adjoints of `L` built from the
untransported composite is `ρ`, then the one built from the transported composite is `ρ` preceded
by `e` whiskered by `G`.

This is what reads a comparison of right adjoints, built by uniqueness against an adjunction
whose middle factor is given through a comparison isomorphism, as the explicit comparison that
the untransported adjunction yields. -/
theorem rightAdjointUniq_comp_ofNatIsoRight_symm_ofNatIsoLeft_eq {F : C ⥤ D} {G : D ⥤ C}
    {F' : D ⥤ E} {G' G'' : E ⥤ D} {L : C ⥤ E} {R : E ⥤ C}
    (adj : F ⊣ G) (adj' : F' ⊣ G') (e : G'' ≅ G') (c : F ⋙ F' ≅ L) (adjL : L ⊣ R)
    (ρ : G' ⋙ G ≅ R)
    (hρ : rightAdjointUniq ((adj.comp adj').ofNatIsoLeft c) adjL = ρ) :
    rightAdjointUniq ((adj.comp (adj'.ofNatIsoRight e.symm)).ofNatIsoLeft c) adjL =
      Functor.isoWhiskerRight e G ≪≫ ρ := by
  have hc : adj.comp (adj'.ofNatIsoRight e.symm) =
      (adj.comp adj').ofNatIsoRight (Functor.isoWhiskerRight e.symm G) :=
    Adjunction.ext (NatTrans.ext (funext fun X => by
      simp [Adjunction.comp_unit_app, G.map_comp]))
  rw [hc, ofNatIsoRight_ofNatIsoLeft, rightAdjointUniq_ofNatIsoRight_left, hρ]
  rfl

end CategoryTheory.Adjunction

end
