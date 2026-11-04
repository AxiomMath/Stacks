module

public import StacksFrontier.Algebra.Homology.RightDerivedCoEdgeIso

/-!
# Invertibility of the co-edge morphism for a reflective inclusion

Let `Q : B ⥤ D` be a fully faithful additive functor with a left adjoint `L`, so that `B` is a
reflective subcategory of `D`, and assume `Q` is left exact.  The co-edge morphism
`Stacks.Cohomology.RightDerivedCoEdge.secondEdge` of a pair `(P, Q)` is the edge
`H^n ⟶ E₂^{0,n}` of the Grothendieck spectral sequence, and
`Stacks.Cohomology.RightDerivedCoEdge.homologyToMapHomology` is the degreewise comparison
`Hⁿ(Q C) ⟶ Q (Hⁿ C)` it is built from.  In general neither is invertible in positive degrees.

This file proves that **both become invertible as soon as the object they start from lies in the
reflective subcategory**, that is, as soon as the unit of the adjunction is invertible there:

* `homologyToMapHomology Q C n` is invertible once `adj.unit` is invertible at `Hⁿ(Q C)`;
* `(secondEdge P Q n).app X` is invertible once `adj.unit` is invertible at `Rⁿ(Q ∘ P) X`.

Nothing about `L` beyond additivity and the preservation of epimorphisms is used, and no
vanishing hypothesis of any kind appears.  The point is purely formal: `Q (Hⁿ C)` lies in the
subcategory, so a morphism into it from `Hⁿ(Q C)` is the same thing as a morphism
`L (Hⁿ(Q C)) ⟶ Hⁿ C`, and *that* morphism is always invertible, being the comparison of two
cokernels of one and the same morphism.

## Construction

Write `QC` for `Q` applied to `C` degreewise.  Left exactness of `Q` makes the comparison of
cycles `Q (Zⁿ C) ⟶ Zⁿ (QC)` invertible, and the counit of the adjunction is invertible because
`Q` is fully faithful; composing them gives an isomorphism
`cyclesCounitIso : L (Zⁿ (QC)) ≅ Zⁿ C`.  The adjoint transpose of the comparison on homology is
`homologyCounitHom : L (Hⁿ(QC)) ⟶ Hⁿ C`, and `cyclesCounitIso` conjugates the projection
`Zⁿ(QC) ⟶ Hⁿ(QC)` into the projection `Zⁿ C ⟶ Hⁿ C` compatibly with the inclusions of the
boundaries.  Since both projections are epimorphisms and `L` preserves epimorphisms, the
two-sided inverse of `homologyCounitHom` can be written down directly out of the cokernel
property of the projection `Zⁿ C ⟶ Hⁿ C`; no colimit needs to be transported.

## Main definitions

* `Stacks.Cohomology.RightDerivedCoEdge.cyclesCounitIso`: the isomorphism
  `L (Zⁿ (Q C)) ≅ Zⁿ C`.
* `Stacks.Cohomology.RightDerivedCoEdge.homologyCounitHom`: the adjoint transpose
  `L (Hⁿ(Q C)) ⟶ Hⁿ C` of the comparison on homology.

## Main results

* `Stacks.Cohomology.RightDerivedCoEdge.isIso_homologyCounitHom`: the adjoint transpose is
  always an isomorphism.
* `Stacks.Cohomology.RightDerivedCoEdge.isIso_homologyToMapHomology_of_isIso_unit`: the
  comparison `Hⁿ(Q C) ⟶ Q (Hⁿ C)` is invertible when the unit is invertible at `Hⁿ(Q C)`.
* `Stacks.Cohomology.RightDerivedCoEdge.isIso_secondEdge_app_of_isIso_unit`: the co-edge
  morphism is invertible at `X` in degree `n` when the unit is invertible at `Rⁿ(Q ∘ P) X`.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 0EZA](https://stacks.math.columbia.edu/tag/0EZA)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.Cohomology.RightDerivedCoEdge

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]

section Reflective

variable {L : D ⥤ B} {Q : B ⥤ D} (adj : L ⊣ Q)
  [Q.Additive] [PreservesFiniteLimits Q] [Q.Full] [Q.Faithful]
  [L.Additive] [L.PreservesEpimorphisms]

/-- **The cycles of `Q C` reflect to the cycles of `C`.**  Left exactness of `Q` makes
`Q (Zⁿ C) ⟶ Zⁿ (Q C)` invertible, and the counit of the adjunction is invertible because `Q` is
fully faithful; the composite of the two is an isomorphism `L (Zⁿ (Q C)) ≅ Zⁿ C`. -/
def cyclesCounitIso (C : CochainComplex B ℕ) (n : ℕ) :
    L.obj (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).cycles n) ≅ C.cycles n :=
  L.mapIso (mapCyclesIso Q C n).symm ≪≫ asIso (adj.counit.app (C.cycles n))

/-- **The adjoint transpose of the comparison on homology**, a morphism
`L (Hⁿ(Q C)) ⟶ Hⁿ C`.  It is always an isomorphism
(`Stacks.Cohomology.RightDerivedCoEdge.isIso_homologyCounitHom`); invertibility of the
comparison itself is the extra condition that `Hⁿ(Q C)` lie in the reflective subcategory. -/
def homologyCounitHom (C : CochainComplex B ℕ) (n : ℕ) :
    L.obj (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) ⟶ C.homology n :=
  L.map (homologyToMapHomology Q C n) ≫ adj.counit.app (C.homology n)

omit [Q.Full] [Q.Faithful] [L.Additive] [L.PreservesEpimorphisms] in
/-- The comparison on homology recovers the adjoint transpose: `Hⁿ(Q C) ⟶ Q (Hⁿ C)` is the unit
followed by `Q` applied to `Stacks.Cohomology.RightDerivedCoEdge.homologyCounitHom`. -/
theorem homologyToMapHomology_eq_unit_comp (C : CochainComplex B ℕ) (n : ℕ) :
    homologyToMapHomology Q C n =
      adj.unit.app (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) ≫
        Q.map (homologyCounitHom adj C n) :=
  ((adj.unit_comp_map_eq_iff (homologyCounitHom adj C n)
    (homologyToMapHomology Q C n)).2 rfl).symm

omit [L.Additive] [L.PreservesEpimorphisms] in
/-- The projection onto homology, transported by the adjoint transpose, is the projection onto
homology of `C` read through the isomorphism on cycles. -/
@[reassoc]
theorem map_homologyπ_comp_homologyCounitHom (C : CochainComplex B ℕ) (n : ℕ) :
    L.map (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homologyπ n) ≫
        homologyCounitHom adj C n =
      (cyclesCounitIso adj C n).hom ≫ C.homologyπ n := by
  rw [homologyCounitHom, ← Category.assoc, ← L.map_comp,
    homologyπ_comp_homologyToMapHomology, L.map_comp, Category.assoc,
    adj.counit_naturality (C.homologyπ n)]
  simp [cyclesCounitIso]

omit [L.Additive] [L.PreservesEpimorphisms] in
/-- The inclusion of the boundaries into the cycles, transported by the isomorphism on cycles. -/
@[reassoc]
theorem map_toCycles_comp_cyclesCounitIso (C : CochainComplex B ℕ) (i n : ℕ) :
    L.map (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).toCycles i n) ≫
        (cyclesCounitIso adj C n).hom =
      adj.counit.app (C.X i) ≫ C.toCycles i n := by
  simp [cyclesCounitIso, ← L.map_comp_assoc, toCycles_comp_mapCyclesIso_inv]

/-- The inverse of the adjoint transpose, built out of the cokernel property of the projection
`Zⁿ C ⟶ Hⁿ C`. -/
def homologyCounitInv (C : CochainComplex B ℕ) (n : ℕ) :
    C.homology n ⟶
      L.obj (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) :=
  (C.homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl).desc
    (CokernelCofork.ofπ ((cyclesCounitIso adj C n).inv ≫
      L.map (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homologyπ n)) (by
      rw [← cancel_epi (adj.counit.app (C.X ((ComplexShape.up ℕ).prev n))), comp_zero,
        ← Category.assoc, ← map_toCycles_comp_cyclesCounitIso adj C, Category.assoc,
        Iso.hom_inv_id_assoc, ← L.map_comp, HomologicalComplex.toCycles_comp_homologyπ]
      simp))

omit [L.PreservesEpimorphisms] in
/-- The defining property of `Stacks.Cohomology.RightDerivedCoEdge.homologyCounitInv`: on the
projection onto homology it is the inverse of the isomorphism on cycles followed by the image
under `L` of the projection onto homology of `Q C`. -/
@[reassoc]
theorem homologyπ_comp_homologyCounitInv (C : CochainComplex B ℕ) (n : ℕ) :
    C.homologyπ n ≫ homologyCounitInv adj C n =
      (cyclesCounitIso adj C n).inv ≫
        L.map (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homologyπ n) :=
  Cofork.IsColimit.π_desc (C.homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl)

/-- **The adjoint transpose of the comparison on homology is always an isomorphism.**  Both
`L (Hⁿ(Q C))` and `Hⁿ C` are cokernels of the same morphism, up to the isomorphism on cycles,
and the two projections onto them are epimorphisms, so the explicit inverse built from the
cokernel property is two-sided. -/
instance isIso_homologyCounitHom (C : CochainComplex B ℕ) (n : ℕ) :
    IsIso (homologyCounitHom adj C n) := by
  refine ⟨homologyCounitInv adj C n, ?_, ?_⟩
  · rw [← cancel_epi (L.map (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homologyπ n)),
      Category.comp_id, map_homologyπ_comp_homologyCounitHom_assoc,
      homologyπ_comp_homologyCounitInv, Iso.hom_inv_id_assoc]
  · rw [← cancel_epi (C.homologyπ n), Category.comp_id, homologyπ_comp_homologyCounitInv_assoc,
      map_homologyπ_comp_homologyCounitHom, Iso.inv_hom_id_assoc]

/-- **The comparison `Hⁿ(Q C) ⟶ Q (Hⁿ C)` is invertible as soon as its source lies in the
reflective subcategory**, that is, as soon as the unit of the adjunction is invertible
there. -/
theorem isIso_homologyToMapHomology_of_isIso_unit (C : CochainComplex B ℕ) (n : ℕ)
    (h : IsIso (adj.unit.app
      (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n))) :
    IsIso (homologyToMapHomology Q C n) := by
  rw [homologyToMapHomology_eq_unit_comp adj C n]
  have := h
  infer_instance

/-- `isIso_homologyToMapHomology_of_isIso_unit` in the spelling of
`homologyFunctorToMapHomology`. -/
theorem isIso_homologyFunctorToMapHomology_of_isIso_unit (C : CochainComplex B ℕ) (n : ℕ)
    (h : IsIso (adj.unit.app
      (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n))) :
    IsIso (homologyFunctorToMapHomology Q C n) :=
  isIso_homologyToMapHomology_of_isIso_unit adj C n h

end Reflective

section CoEdgeReflective

variable [HasInjectiveResolutions A] [HasInjectiveResolutions B]
  (P : A ⥤ B) [P.Additive] [P.PreservesInjectiveObjects]
  {L : D ⥤ B} {Q : B ⥤ D} (adj : L ⊣ Q)
  [Q.Additive] [PreservesFiniteLimits Q] [Q.Full] [Q.Faithful]
  [L.Additive] [L.PreservesEpimorphisms]

omit [HasInjectiveResolutions B] [P.PreservesInjectiveObjects] in
/-- **The co-edge morphism is invertible at `X` in degree `n` as soon as `Rⁿ(Q ∘ P) X` lies in
the reflective subcategory**, that is, as soon as the unit of the adjunction is invertible
there.  No vanishing hypothesis is used: the whole content is that a morphism into an object of
the subcategory is determined by its adjoint transpose, and the transpose here is the comparison
of two cokernels of one morphism. -/
theorem isIso_secondEdge_app_of_isIso_unit (n : ℕ) (X : A)
    (h : IsIso (adj.unit.app (((P ⋙ Q).rightDerived n).obj X))) :
    IsIso ((secondEdge P Q n).app X) := by
  have h' : IsIso (adj.unit.app
      (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution X).cocomplex)).homology n)) :=
    (NatTrans.isIso_app_iff_of_iso adj.unit
      (RightDerivedEdge.isoRightDerivedObjComp P Q (injectiveResolution X) n)).1 h
  have h₁ : IsIso (homologyFunctorToMapHomology Q
      ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution X).cocomplex) n) :=
    isIso_homologyFunctorToMapHomology_of_isIso_unit adj _ n h'
  have h₂ : IsIso (Q.map ((injectiveResolution X).isoRightDerivedObj P n).inv) := inferInstance
  have h₃ : IsIso ((RightDerivedEdge.isoRightDerivedObjComp P Q
      (injectiveResolution X) n).hom) := inferInstance
  change IsIso (secondEdgeApp P Q n X)
  rw [secondEdgeApp]
  exact IsIso.comp_isIso' h₃ (IsIso.comp_isIso' h₁ h₂)

end CoEdgeReflective

end Stacks.Cohomology.RightDerivedCoEdge

end
