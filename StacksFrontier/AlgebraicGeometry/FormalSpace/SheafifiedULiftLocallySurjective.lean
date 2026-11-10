module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.FppfCovering
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalProperty

/-!
# Local surjectivity of the sheafified universe lift

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f : X' ⟶ X` of presheaves of
`Type u` on the big fppf site over `S` induces a morphism
`AlgebraicGeometry.Space.sheafifiedULiftMap B S hS f` of fppf sheaves of `Type (u + 1)`, the
value universe in which the formal algebraic spaces of Stacks 0AIX read their coverings. This
file proves that local surjectivity is carried along that construction, both for a single
morphism and for the morphism a family induces out of the coproduct sheaf.

## Main definitions

* `AlgebraicGeometry.Space.toSheafifiedULift` is the sheafification unit of the universe lift,
  read as a morphism into the universe lift's sheafification
  `AlgebraicGeometry.Space.sheafifiedULift`.

## Main results

* `AlgebraicGeometry.Space.isLocallySurjective_sheafifiedULiftMap`: the sheafified universe lift
  of a locally surjective morphism of presheaves of `Type u` is a locally surjective morphism of
  fppf sheaves of `Type (u + 1)`.
* `AlgebraicGeometry.Space.exists_etaleChart_isLocallySurjective_sheafifiedULiftMap`: an
  algebraic space has an étale chart by an object of the site whose sheafified universe lift is
  locally surjective.
* `AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_sheafifiedULiftMap`: the morphism a
  family induces from the coproduct of the sheafified universe lifts is locally surjective as
  soon as the morphism the family induces from the coproduct of the universe lifts, taken among
  presheaves of `Type (u + 1)`, is.

## Implementation notes

All of this rests on two facts: raising the universe of the values of a presheaf of types
preserves local surjectivity, which is
`CategoryTheory.Presheaf.isLocallySurjective_whiskerRight_typeUliftFunctor`, and the
sheafification unit is itself locally surjective and natural, so sheafification preserves local
surjectivity as well.

The unit is given a name of its own because Mathlib's sheafification unit has the sheafification
of the universe lift as its target, whereas the coproduct inclusions of the sheaves have
`AlgebraicGeometry.Space.sheafifiedULift` as their source. The two agree by definition but not at
the transparency at which composites are type-checked and instances are resolved, so composing
the one with the other needs the unit stated at the latter type.

For a family indexed by a type of `Type (u + 1)` the coproduct of the universe lifts exists among
presheaves of `Type (u + 1)` but there is no coproduct of the presheaves of `Type u` themselves,
which is why the hypothesis of
`AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_sheafifiedULiftMap` is stated after the
universe lift. No comparison between the coproduct of the sheafifications and the sheafification
of the coproduct is needed: the morphism from the presheaf coproduct into the coproduct sheaf
assembled from the units is enough, because local surjectivity of a composite descends to its
second factor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sheafification unit of the universe lift of a presheaf of `Type u`, read as a morphism
into `AlgebraicGeometry.Space.sheafifiedULift`. -/
def toSheafifiedULift (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    X ⋙ uliftFunctor.{u + 1} ⟶ (sheafifiedULift B S hS X).obj :=
  (BigFppfOver.topology B S hS).toSheafify (X ⋙ uliftFunctor.{u + 1})

/-- The sheafification unit `AlgebraicGeometry.Space.toSheafifiedULift` is locally surjective. -/
instance isLocallySurjective_toSheafifiedULift (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (toSheafifiedULift B S hS X) :=
  Presheaf.isLocallySurjective_toSheafify _ _

/-- The sheafification unit of the universe lift is natural in the presheaf. -/
theorem whiskerRight_comp_toSheafifiedULift
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X) :
    Functor.whiskerRight f uliftFunctor.{u + 1} ≫ toSheafifiedULift B S hS X =
      toSheafifiedULift B S hS X' ≫ (sheafifiedULiftMap B S hS f).hom :=
  (BigFppfOver.topology B S hS).toSheafify_naturality _

/-- A morphism of sheaves into the sheafified universe lift is locally surjective if composing a
locally surjective morphism into the universe lift with the unit factors through it. -/
private theorem isLocallySurjective_of_comp_toSheafifiedULift
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {F : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (g : P ⟶ X ⋙ uliftFunctor.{u + 1}) (h : P ⟶ F.obj) (m : F ⟶ sheafifiedULift B S hS X)
    (hg : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) g)
    (hm : g ≫ toSheafifiedULift B S hS X = h ≫ m.hom) : Sheaf.IsLocallySurjective m :=
  have := Presheaf.isLocallySurjective_comp (BigFppfOver.topology B S hS) g
    (toSheafifiedULift B S hS X)
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ hm.symm

/-- The sheafified universe lift of a locally surjective morphism of presheaves of `Type u` is a
locally surjective morphism of fppf sheaves of `Type (u + 1)`. -/
theorem isLocallySurjective_sheafifiedULiftMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f) :
    Sheaf.IsLocallySurjective (sheafifiedULiftMap B S hS f) :=
  have := hf
  isLocallySurjective_of_comp_toSheafifiedULift B S hS _ _ _ inferInstance
    (whiskerRight_comp_toSheafifiedULift B S hS f)

/-- An algebraic space over `S` has an étale chart by an object of the big fppf site whose
sheafified universe lift is locally surjective. -/
theorem exists_etaleChart_isLocallySurjective_sheafifiedULiftMap
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) :
    ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X),
      Sheaf.IsLocallySurjective (sheafifiedULiftMap B S hS f) := by
  obtain ⟨U, f, hfS, hfE⟩ := hX.exists_atlas
  exact ⟨U, f, isLocallySurjective_sheafifiedULiftMap B S hS f
    (isLocallySurjective_of_surjective_etale B S hS f hfS hfE)⟩

/-- If the morphism a family `{Xᵢ ⟶ X}` induces from the coproduct of the universe lifts of the
`Xᵢ` is locally surjective among presheaves of `Type (u + 1)`, then the morphism it induces from
the coproduct of the sheafified universe lifts is a locally surjective morphism of fppf sheaves. -/
theorem isLocallySurjective_sigmaDesc_sheafifiedULiftMap
    [HasColimitsOfSize.{u + 1, u + 1} (Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))]
    {Ix : Type (u + 1)} {Xi : Ix → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : ∀ i, Xi i ⟶ X)
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Sigma.desc fun i ↦ Functor.whiskerRight (f i) uliftFunctor.{u + 1})) :
    Sheaf.IsLocallySurjective (Sigma.desc fun i ↦ sheafifiedULiftMap B S hS (f i)) :=
  isLocallySurjective_of_comp_toSheafifiedULift B S hS _
    (Sigma.desc fun i ↦ toSheafifiedULift B S hS (Xi i) ≫
      (Sigma.ι (fun i ↦ sheafifiedULift B S hS (Xi i)) i).hom) _ hf <| by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc_assoc, Category.assoc,
      ← ObjectProperty.FullSubcategory.comp_hom, Sigma.ι_comp_desc]
    exact whiskerRight_comp_toSheafifiedULift B S hS (f i)

end AlgebraicGeometry.Space
