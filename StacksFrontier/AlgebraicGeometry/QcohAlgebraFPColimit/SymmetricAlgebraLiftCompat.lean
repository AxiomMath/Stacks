module

public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraSheafUniversal
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraSheafFunctorial

/-!
# The ungraded lift out of `Sym(ℱ)` is compatible with `Sym(f)`

Let `X` be a scheme, `𝒜` a sheaf of commutative `𝒪_X`-algebras, `f : ℱ ⟶ 𝒢` a morphism of
`𝒪_X`-modules and `φ : 𝒢 ⟶ 𝒜` a morphism of module sheaves. There are then two morphisms of
algebra sheaves `Sym(ℱ) ⟶ 𝒜`: the lift of `f ≫ φ`, and `Sym(f)` followed by the lift of `φ`.
**They agree.**

`Stacks.SymAlgSheaf.algebraLift` is not claimed unique — see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraSheafUniversal` — so this is not an
instance of a uniqueness principle for ungraded morphisms out of `Sym(ℱ)`, and it is proved here
instead from uniqueness at the *graded* level.

## Main results

* `Stacks.SymAlgSheaf.algebraLift_comp`: **the compatibility above.**

## Implementation notes

Both morphisms are descents across the same sheafification. `Stacks.SymAlgSheaf.ungradedLift` is
by construction `Stacks.GradedAlgebra.totalSheafLift` of
`Stacks.SymAlgSheaf.psiPresheafHom`, and
`SheafOfModules.GradedAlgebra.ungradedSheafMap` is `totalSheafLift` of
`Stacks.GradedAlgebra.totalPresheafMap`; a morphism out of a sheafification is determined by its
composite with the unit (`CategoryTheory.sheafify_hom_ext`), so the statement reduces to the
corresponding equation between morphisms of *presheaves* of rings out of
`Stacks.GradedAlgebra.totalPresheaf`.

That equation is checked on elements, and `Stacks.GradedAlgebra.incl_induction` reduces it to the
homogeneous sections, where both sides are the degree-`n` component of a unital homomorphism of
sheaves of graded algebras into `Stacks.SymAlgSheaf.constGraded 𝒜`. The two homomorphisms agree
because the graded universal property of `Sym(ℱ)` *does* come with uniqueness
(`SheafOfModules.GradedAlgebra.IsUniversal.desc_unique`): the composite of
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebraUnitalHom` with
`Stacks.SymAlgSheaf.descHom` of `φ` extends `f ≫ φ` in degree one, so it is
`Stacks.SymAlgSheaf.descHom` of `f ≫ φ`.

The passage from the sheaf of rings to the sheaf of *commutative* rings underlying an algebra
sheaf is made once, by `algebraLift_right_app`, which is `rfl`: the two carry the same sections
and the same ring operations, `Stacks.CommRingSheaf.sheafMap` and
`Stacks.SymAlgSheaf.commLift` keeping the underlying maps.

**No `@[stacks]` attribute.** This is a compatibility of two constructions, not the assertion of
a tag; it is the naturality input for the directed system of [Stacks, Tag 05JS].

## References

* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.SymAlgSheaf

variable {X : Scheme.{u}} (𝒜 : X.QuasicoherentAlgebra)
  {F G : SheafOfModules.{u} X.ringCatSheaf}

/-- A morphism out of the ungraded realization of a sheaf of graded algebras is determined by its
composite with the sheafification unit. -/
theorem totalSheaf_hom_ext {S : Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u}}
    (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (α β : A.ungradedSheaf ⟶ S)
    (h : A.toPresheafGradedAlgebra.toTotalSheaf (Opens.grothendieckTopology (X : TopCat)) ≫ α.hom =
      A.toPresheafGradedAlgebra.toTotalSheaf (Opens.grothendieckTopology (X : TopCat)) ≫ β.hom) :
    α = β :=
  Sheaf.hom_ext (sheafify_hom_ext _ _ _ S.property h)

/-- The degreewise comparison of the lift of `f ≫ φ` is the composite of `Sym(f)` with the
degreewise comparison of the lift of `φ`.

This is uniqueness in the graded universal property of `Sym(ℱ)`: the composite extends `f ≫ φ`
in degree one, and so does `descHom` of `f ≫ φ`. -/
theorem symmetricAlgebraUnitalHom_comp_descHom (f : F ⟶ G)
    (φ : G ⟶ Scheme.QuasicoherentAlgebra.underlyingModule 𝒜) :
    (Scheme.Modules.symmetricAlgebraUnitalHom X f).comp (descHom 𝒜 G φ) =
      descHom 𝒜 F (f ≫ φ) :=
  SheafOfModules.GradedAlgebra.IsUniversal.desc_unique
    (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X F) (constGraded 𝒜) (f ≫ φ)
    (pairwiseCommutes_constGraded 𝒜 F (f ≫ φ)) <| by
  rw [SheafOfModules.GradedAlgebra.UnitalHom.comp_app, ← Category.assoc,
    Scheme.Modules.symmetricAlgebraGen_comp_symmetricAlgebraUnitalHom, Category.assoc,
    symmetricAlgebraGen_comp_descHom]

/-- The degree-`n` component of the comparison on sections is the degree-`n` component of the
degreewise comparison. -/
theorem psiAdd_apply (F : SheafOfModules.{u} X.ringCatSheaf)
    (φ : F ⟶ Scheme.QuasicoherentAlgebra.underlyingModule 𝒜) (n : ℤ) (W : (Opens ↥X)ᵒᵖ)
    (x : ((Scheme.Modules.symmetricAlgebra X F).piece n).val.obj W) :
    psiAdd 𝒜 F φ n W x = ((descHom 𝒜 F φ).app n).val.app W x :=
  rfl

/-- The comparison on sections of the lift of `f ≫ φ` is the presheaf-level realization of
`Sym(f)` followed by the comparison of the lift of `φ`, on every section. -/
theorem psiTotal_totalPresheafMap (f : F ⟶ G)
    (φ : G ⟶ Scheme.QuasicoherentAlgebra.underlyingModule 𝒜) (W : (Opens ↥X)ᵒᵖ)
    (z : (symPre F).Total W) :
    psiTotal 𝒜 F (f ≫ φ) W z =
      psiTotal 𝒜 G φ W (((Stacks.GradedAlgebra.totalPresheafMap
        (Scheme.Modules.symmetricAlgebraUnitalHom X f).toPresheafGradedAlgebraHom).app W).hom
          z) := by
  induction z using Stacks.GradedAlgebra.incl_induction with
  | zero => exact (map_zero _).trans ((congrArg _ (map_zero _)).trans (map_zero _)).symm
  | incl n x =>
      rw [Stacks.GradedAlgebra.totalPresheafMap_app_incl, psiTotal_incl, psiTotal_incl,
        psiAdd_apply, psiAdd_apply, ← symmetricAlgebraUnitalHom_comp_descHom 𝒜 f φ,
        SheafOfModules.GradedAlgebra.UnitalHom.comp_app]
      rfl
  | add a b ha hb =>
      exact (map_add _ a b).trans ((congrArg₂ (· + ·) ha hb).trans
        ((map_add _ _ _).symm.trans (congrArg _ (map_add _ a b).symm)))

/-- The presheaf-level comparison of the lift of `f ≫ φ` is the presheaf-level realization of
`Sym(f)` followed by the comparison of the lift of `φ`. -/
theorem psiPresheafHom_comp (f : F ⟶ G)
    (φ : G ⟶ Scheme.QuasicoherentAlgebra.underlyingModule 𝒜) :
    psiPresheafHom 𝒜 F (f ≫ φ) =
      Stacks.GradedAlgebra.totalPresheafMap
          (Scheme.Modules.symmetricAlgebraUnitalHom X f).toPresheafGradedAlgebraHom ≫
        psiPresheafHom 𝒜 G φ :=
  NatTrans.ext (funext fun W => RingCat.hom_ext (RingHom.ext fun z =>
    psiTotal_totalPresheafMap 𝒜 f φ W z))

/-- The defining property of the lift out of the ungraded realization, as an equation between
morphisms of presheaves of rings. -/
theorem toTotalSheaf_comp_ungradedLift (F : SheafOfModules.{u} X.ringCatSheaf)
    (φ : F ⟶ Scheme.QuasicoherentAlgebra.underlyingModule 𝒜) :
    (symPre F).toTotalSheaf (Opens.grothendieckTopology (X : TopCat)) ≫
        (ungradedLift 𝒜 F φ).hom =
      psiPresheafHom 𝒜 F φ :=
  (symPre F).toTotalSheaf_totalSheafLift _ _ (psiPresheafHom 𝒜 F φ)

/-- The lift out of the ungraded realization is compatible with `Sym(f)`, as a morphism of
sheaves of rings. -/
theorem ungradedLift_comp (f : F ⟶ G)
    (φ : G ⟶ Scheme.QuasicoherentAlgebra.underlyingModule 𝒜) :
    ungradedLift 𝒜 F (f ≫ φ) =
      SheafOfModules.GradedAlgebra.ungradedSheafMap (Scheme.Modules.symmetricAlgebraUnitalHom X f)
        ≫ ungradedLift 𝒜 G φ := by
  refine totalSheaf_hom_ext (Scheme.Modules.symmetricAlgebra X F) _ _ ?_
  rw [toTotalSheaf_comp_ungradedLift, psiPresheafHom_comp,
    ← toTotalSheaf_comp_ungradedLift 𝒜 G φ, ← Category.assoc,
    ← Stacks.GradedAlgebra.toTotalSheaf_totalSheafMap (Opens.grothendieckTopology (X : TopCat)),
    Category.assoc]
  rfl

/-- The lift of `f ≫ φ` out of `Sym(ℱ)` on sections is the lift out of the ungraded realization;
the sheaf of commutative rings underlying `Sym(ℱ)` as an algebra sheaf is the ungraded
realization itself. -/
theorem algebraLift_right_app (F : SheafOfModules.{u} X.ringCatSheaf)
    (φ : F ⟶ Scheme.QuasicoherentAlgebra.underlyingModule 𝒜) (W : (Opens ↥X)ᵒᵖ)
    (z : ((Scheme.Modules.symmetricAlgebra X F).ungradedSheaf).obj.obj W) :
    ((algebraLift 𝒜 F φ).right.hom.app W).hom z = ((ungradedLift 𝒜 F φ).hom.app W).hom z :=
  rfl

/-- **The lift out of `Sym(ℱ)` is compatible with `Sym(f)`**: the morphism of algebra sheaves
`Sym(ℱ) ⟶ 𝒜` lifting `f ≫ φ` is `Sym(f)` followed by the morphism lifting `φ`.

This is the naturality the cocone of a directed system of symmetric algebras needs, and it does
not follow from the defining degree-one equation of the lift alone: it is uniqueness in the
*graded* universal property, transported across the sheafification. -/
theorem algebraLift_comp (f : F ⟶ G)
    (φ : G ⟶ Scheme.QuasicoherentAlgebra.underlyingModule 𝒜) :
    algebraLift 𝒜 F (f ≫ φ) = Scheme.Modules.symmetricAlgebraSheafMap X f ≫ algebraLift 𝒜 G φ :=
  Under.UnderMorphism.ext (Sheaf.hom_ext (NatTrans.ext (funext fun W =>
    CommRingCat.hom_ext (RingHom.ext fun z =>
      (algebraLift_right_app 𝒜 F (f ≫ φ) W z).trans
        (congrArg (fun t : (Scheme.Modules.symmetricAlgebra X F).ungradedSheaf ⟶
            Scheme.QuasicoherentAlgebra.ringSheaf 𝒜 => (t.hom.app W).hom z)
          (ungradedLift_comp 𝒜 f φ))))))

end Stacks.SymAlgSheaf

end
