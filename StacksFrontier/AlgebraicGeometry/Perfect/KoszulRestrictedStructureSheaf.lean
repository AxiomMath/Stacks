module

public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximationLocal
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCechDerivedComparison

/-!
# The structure sheaf of a union of basic opens, in the derived category

Let `A` be a commutative ring, let `f = (f₁, …, f_r)` be a finite sequence of elements of `A`,
let `X = Spec A` and let `U = D(f₁) ∪ ⋯ ∪ D(f_r) ⊆ X`.  The restriction of `𝒪_X` to `U`, read
as an object of `D(𝒪_U)`, is the structure sheaf of `U` placed in degree zero, so its
endomorphism ring is the ring of sections `𝒪_X(U)`.  In particular an endomorphism of it with a
one-sided inverse has a two-sided one.

This is the input that turns an abstract isomorphism between two functors out of `D(𝒪_X)` into a
statement about a *named* comparison map: a natural transformation between functors represented
by `𝒪_X|_U` differs from another by precomposition with an endomorphism of `𝒪_X|_U`, and such an
endomorphism that is invertible on one side is invertible.

## Main definitions

* `Koszul.DerivedSystem.unitValue` is the value at `1` of an endomorphism of the unit object of
  a category of sheaves of modules; an endomorphism is multiplication by that section.

## Main results

* `Koszul.DerivedSystem.unitValue_comp` and `Koszul.DerivedSystem.unitValue_injective`: the
  endomorphisms of the unit object form a ring under composition, identified with the ring of
  sections by `unitValue`.
* `Koszul.DerivedSystem.unit_comp_eq_id_symm`: over a sheaf of *commutative* rings, a one-sided
  inverse of an endomorphism of the unit is a two-sided inverse.
* `Koszul.DerivedSystem.restrictStructureSheafIso`: the restriction of `𝒪_X` to `U` is the
  structure sheaf of `U` in degree zero.
* `Koszul.DerivedSystem.isIso_of_comp_eq_id_restrictStructureSheaf`: an endomorphism of `𝒪_X|_U`
  in `D(𝒪_U)` with a right inverse is an isomorphism.

## Implementation notes

An endomorphism `c` of the unit object is determined by the sections `c(1)`, because `c` is
linear over the sheaf of rings: `c(a) = a · c(1)`.  Composition is multiplication of those
sections, so the commutativity of the sections of `𝒪_X` is what makes a one-sided inverse
two-sided.  The sections of the structure sheaf of `U` are sections of `𝒪_X` over an open of
`X`, hence a commutative ring, although the sheaf of rings is spelled in `RingCat` and carries
no commutativity.

The identification of `𝒪_X|_U` with the structure sheaf of `U` in degree zero runs through the
four steps used for the same statement on `X` in
`Koszul.DerivedSystem.derivedRingObjectIso`: derived restriction is the functor induced by
restriction, that functor commutes with the passage to the derived category, restriction of a
complex concentrated in degree zero is concentrated in degree zero, and restriction carries the
unit object to the unit object, the last by `Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit`
for the identity morphism of sheaves of rings.

## References

* [Stacks Project, Tag 08CZ](https://stacks.math.columbia.edu/tag/08CZ)
* [Stacks Project, Tag 08DC](https://stacks.math.columbia.edu/tag/08DC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open ExtensionByZeroModules Stacks.Cohomology.OpenSubspace

universe u

namespace Koszul.DerivedSystem

/-! ### Endomorphisms of the unit object -/

section Unit

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

/-- The value at `1` of an endomorphism of the unit object of the sheaves of `R`-modules. -/
public def unitValue (c : SheafOfModules.unit R ⟶ SheafOfModules.unit R) (X : Cᵒᵖ) :
    R.obj.obj X :=
  c.val.app X (1 : R.obj.obj X)

/-- **An endomorphism of the unit object is multiplication by its value at `1`.** -/
public theorem unitValue_apply (d : SheafOfModules.unit R ⟶ SheafOfModules.unit R) (X : Cᵒᵖ)
    (a : R.obj.obj X) : d.val.app X a = a * unitValue d X :=
  Eq.trans (congrArg (d.val.app X).hom (mul_one a).symm)
    (map_smul (d.val.app X).hom a (1 : R.obj.obj X))

/-- Composition of endomorphisms of the unit object multiplies their values at `1`. -/
public theorem unitValue_comp (c d : SheafOfModules.unit R ⟶ SheafOfModules.unit R) (X : Cᵒᵖ) :
    unitValue (c ≫ d) X = unitValue c X * unitValue d X :=
  unitValue_apply d X (unitValue c X)

/-- The identity endomorphism of the unit object has value `1`. -/
public theorem unitValue_id (X : Cᵒᵖ) : unitValue (𝟙 (SheafOfModules.unit R)) X = 1 := rfl

/-- An endomorphism of the unit object is determined by its values at `1`. -/
public theorem unitValue_injective {c d : SheafOfModules.unit R ⟶ SheafOfModules.unit R}
    (h : ∀ X, unitValue c X = unitValue d X) : c = d :=
  (SheafOfModules.unitHomEquiv _).injective (Subtype.ext (funext h))

/-- **Over a sheaf of commutative rings a one-sided inverse of an endomorphism of the unit
object is a two-sided inverse.** -/
public theorem unit_comp_eq_id_symm
    (hR : ∀ (X : Cᵒᵖ) (a b : R.obj.obj X), a * b = b * a)
    (c d : SheafOfModules.unit R ⟶ SheafOfModules.unit R) (h : c ≫ d = 𝟙 _) :
    d ≫ c = 𝟙 _ := by
  refine unitValue_injective fun X ↦ ?_
  have hX : unitValue c X * unitValue d X = 1 := by
    rw [← unitValue_comp, h, unitValue_id]
  rw [unitValue_comp, unitValue_id, hR, hX]

end Unit

/-! ### The restriction of the structure sheaf to a union of basic opens -/

section Restrict

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : CommRingCat.{u}} {r : ℕ} (f : Fin r → A)

/-- **The restriction of `𝒪_X` to `U = D(f₁) ∪ ⋯ ∪ D(f_r)` is the structure sheaf of `U`,
placed in degree zero.** -/
public def restrictStructureSheafIso :
    (restrictionToUnion f).obj (structureSheafObject A) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (unionRingSheaf f)) 0).obj
        (SheafOfModules.unit (unionRingSheaf f)) := by
  letI O := (Spec A).ringCatSheaf
  letI U := unionOfBasicOpens f
  letI T := jStar U O
  letI M := SheafOfModules.unit O
  letI K := (CochainComplex.singleFunctor (SheafOfModules.{u} O) 0).obj M
  haveI : IsIso (SheafOfModules.unitToPushforwardObjUnit (𝟙 (resRing U O))) :=
    Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit (𝟙 (resRing U O))
  exact (restrictionToUnion f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} O) 0).app M) ≪≫
    (derivedRestrictionIso O U).app (DerivedCategory.Q.obj K) ≪≫
    T.mapDerivedCategoryFactors.app K ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex T (up ℤ) 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (resRing U O)) 0).app
      (T.obj M)).symm ≪≫
    (DerivedCategory.singleFunctor (SheafOfModules.{u} (resRing U O)) 0).mapIso
      (asIso (SheafOfModules.unitToPushforwardObjUnit (𝟙 (resRing U O)))).symm

/-- **The sections of the structure sheaf of `U` commute**: they are sections of `𝒪_X` over an
open of `X`. -/
public theorem mul_comm_unionRingSheaf (X : (Opens (unionSpace f))ᵒᵖ)
    (a b : (unionRingSheaf f).obj.obj X) : a * b = b * a := by
  let : CommRing ↥((unionRingSheaf f).obj.obj X) :=
    inferInstanceAs (CommRing ↥((Spec A).presheaf.obj
      (op ((TopCat.Presheaf.imF (unionOfBasicOpens f)).obj X.unop))))
  exact mul_comm a b

/-- **An endomorphism of `𝒪_X|_U` in `D(𝒪_U)` with a right inverse is an isomorphism.**  It is
an endomorphism of the structure sheaf of `U` in degree zero, hence multiplication by a section
of `𝒪_X` over `U`, and a section with a one-sided inverse is invertible. -/
public theorem isIso_of_comp_eq_id_restrictStructureSheaf
    (c d : (restrictionToUnion f).obj (structureSheafObject A) ⟶
      (restrictionToUnion f).obj (structureSheafObject A)) (h : c ≫ d = 𝟙 _) : IsIso c := by
  set S := SheafOfModules.{u} (unionRingSheaf f)
  set Sg := DerivedCategory.singleFunctor S 0
  let ff : Sg.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful Sg
  set i := restrictStructureSheafIso f
  set c' := i.inv ≫ c ≫ i.hom with hc'
  set d' := i.inv ≫ d ≫ i.hom with hd'
  have h' : c' ≫ d' = 𝟙 _ := by
    rw [hc', hd']
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc c d, h, Category.id_comp, Iso.inv_hom_id]
  have hpre : ff.preimage c' ≫ ff.preimage d' = 𝟙 _ :=
    ff.map_injective (by rw [Functor.map_comp, ff.map_preimage, ff.map_preimage, h', Sg.map_id])
  have : IsIso (ff.preimage c') :=
    ⟨ff.preimage d', hpre, unit_comp_eq_id_symm (mul_comm_unionRingSheaf f) _ _ hpre⟩
  have hc'iso : IsIso c' := by
    rw [← ff.map_preimage c']
    infer_instance
  have hceq : c = i.hom ≫ c' ≫ i.inv := by
    rw [hc']
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [hceq]
  infer_instance

end Restrict

end Koszul.DerivedSystem

end
