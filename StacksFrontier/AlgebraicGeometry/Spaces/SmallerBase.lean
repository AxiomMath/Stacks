module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Extension
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation

/-!
# Algebraic spaces over a smaller base scheme (Stacks 03I5 (2), 04SG)

Let `g : S ⟶ S'` be a morphism of a big fppf site. The lower-shriek extension
`CategoryTheory.OverShriek.relocalizePresheafFunctor g` of Stacks 03I5 part (2) carries a sheaf on
the big fppf site of `S` to a sheaf on the big fppf site of `S'`, so it needs no sheafification,
and it carries algebraic spaces to algebraic spaces. Composed with the equivalence of Stacks 00Y1
it is the forward functor of the equivalence of Stacks 04SG between algebraic spaces over `S` and
algebraic spaces over `S'` equipped with a morphism to the representable algebraic space of `S`.

## Main definitions

* `AlgebraicGeometry.relocalizeSheafFunctor`: the lower-shriek extension as a functor on sheaves,
  with `AlgebraicGeometry.relocalizeSheafAdjunction` exhibiting it as a left adjoint of restriction
  along `CategoryTheory.Over.map g`.
* `AlgebraicGeometry.smallerBasePresheafEquivalence`: presheaves on the big fppf site of `S` are
  the same thing as presheaves on the big fppf site of `S'` over the representable presheaf of
  `S ⟶ S'`; this is Stacks 00Y1 for the twice-localized site, read through the iterated-slice
  equivalence.
* `AlgebraicGeometry.spacesOverSmallerBaseFunctor`: **Stacks 04SG**, the forward functor of the
  equivalence, i.e. the lower-shriek extension read in the slice over the representable algebraic
  space of `S`.

## Main results

* `AlgebraicGeometry.isSheaf_relocalizePresheafFunctor`: the lower-shriek extension of a sheaf is
  a sheaf.
* `AlgebraicGeometry.isAlgebraicSpace_viewOver`: **Stacks 03I5 (2)**, the lower-shriek extension
  of an algebraic space over `S` is an algebraic space over `S'`.
* `AlgebraicGeometry.spacesOverSmallerBaseFunctorForgetIso`,
  `AlgebraicGeometry.spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app` and
  `AlgebraicGeometry.spacesOverSmallerBaseFunctor_hom_app_left`: the forward functor is the
  lower-shriek extension, and that identification is one of algebraic spaces *over* the
  representable algebraic space of `S`, in both directions.

## Implementation notes

That the extension of a sheaf is already a sheaf is `CategoryTheory.OverShriek.isSheaf_fiber`
applied to the coproduct presheaf of Stacks 03CD: the extension is the fibre of
`∐_{ψ : W ⟶ S} F(W →ψ S) ⟶ h_S ⟶ h_{S'}` over the tautological section, the coproduct presheaf is
a sheaf on the whole site by `CategoryTheory.OverShriek.isSheaf_presheaf` and subcanonicity
(`AlgebraicGeometry.BigFppfSite.subcanonical_topology`), and the restriction of a sheaf to a
slice is a sheaf.

Algebraicity is then Stacks 03I4 part (3) (`AlgebraicGeometry.isAlgebraicSpace_extend`), which is
stated for an *arbitrary* left adjoint of restriction; `AlgebraicGeometry.relocalizeSheafFunctor`
is such a left adjoint whose value on a sheaf is the presheaf-level extension on the nose, so no
transport along a comparison isomorphism is needed. The adjunction is the presheaf-level
adjunction `CategoryTheory.OverShriek.relocalizeAdjunction` restricted to sheaves, through
`CategoryTheory.OverShriek.relocalizeToRestricted` and
`CategoryTheory.OverShriek.relocalizeOfRestricted`.

Only the *forward* functor of the equivalence of Stacks 04SG is here. Its quasi-inverse is
restriction along `CategoryTheory.Over.map g`. That restriction does preserve algebraic spaces —
Stacks 03I5 part (1), `AlgebraicGeometry.isAlgebraicSpace_relocalizeRestrict` in
`StacksFrontier/AlgebraicGeometry/Spaces/RestrictSmallerBase.lean`, proved there directly rather
than
through Theorem 02WW, which the library does not have — but the unit and counit exhibiting the two
functors as an equivalence are still not assembled, so the equivalence itself is not yet available.
The forward functor is what every relative-property statement of Chapters 100 and 101 — Stacks
03YK and Stacks 026O among them — is written with, and it needs only part (2).

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

section Sheaves

variable (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')

/-- The lower-shriek extension of a sheaf on the big fppf site of `S` along `g : S ⟶ S'` is
already a sheaf on the big fppf site of `S'`; in particular Stacks 03I5 part (2) needs no
sheafification.

The extension is the fibre of the coproduct presheaf `∐_{ψ : W ⟶ S} F(W →ψ S)` of Stacks 03CD over
the tautological section of `h_{S'}`, the coproduct presheaf is a sheaf on the whole site because
`F` is a sheaf and `h_S` is one, and the restriction of a sheaf to a slice is a sheaf. -/
theorem isSheaf_relocalizePresheafFunctor (F : Sheaf (B.topology.over S) (Type u)) :
    Presheaf.IsSheaf (B.topology.over S')
      ((OverShriek.relocalizePresheafFunctor g).obj F.obj) := by
  have _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  have hy (X : B.Schemes) : Presieve.IsSheaf B.topology (yoneda.obj X) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have hover {P} (h : Presheaf.IsSheaf B.topology P) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (Sheaf.over (⟨P, h⟩ : Sheaf B.topology (Type u)) S').property
  rw [isSheaf_iff_isSheaf_of_type]
  refine OverShriek.isSheaf_fiber (𝟙 (yoneda.obj S'))
    (OverShriek.presheafToYoneda F.obj ≫ yoneda.map g)
    (hover ((isSheaf_iff_isSheaf_of_type _ _).2
      (OverShriek.isSheaf_presheaf B.topology F.obj (hy S)
        ((isSheaf_iff_isSheaf_of_type _ F.obj).1 F.property))))
    (hover ((isSheaf_iff_isSheaf_of_type _ _).2 (hy S'))).isSeparated

/-- The lower-shriek extension along `g : S ⟶ S'` as a functor on sheaves, by
`AlgebraicGeometry.isSheaf_relocalizePresheafFunctor`. -/
noncomputable def relocalizeSheafFunctor :
    Sheaf (B.topology.over S) (Type u) ⥤ Sheaf (B.topology.over S') (Type u) where
  obj F := ⟨(OverShriek.relocalizePresheafFunctor g).obj F.obj,
    isSheaf_relocalizePresheafFunctor B S S' g F⟩
  map f := ObjectProperty.homMk ((OverShriek.relocalizePresheafFunctor g).map f.hom)
  map_id F := by ext; rfl
  map_comp f h := by ext; rfl

/-- `AlgebraicGeometry.relocalizeSheafFunctor` is a left adjoint of restriction along
`CategoryTheory.Over.map g`: the presheaf-level adjunction
`CategoryTheory.OverShriek.relocalizeAdjunction`, restricted to sheaves. -/
noncomputable def relocalizeSheafAdjunction :
    relocalizeSheafFunctor B S S' g ⊣
      (Over.map g).sheafPushforwardContinuous (Type u)
        (B.topology.over S) (B.topology.over S') := by
  refine Adjunction.mkOfHomEquiv
    { homEquiv := fun F G =>
        { toFun := fun f => ObjectProperty.homMk (OverShriek.relocalizeToRestricted g f.hom)
          invFun := fun f => ObjectProperty.homMk (OverShriek.relocalizeOfRestricted g f.hom)
          left_inv := ?_
          right_inv := ?_ }
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  · intro f
    apply Sheaf.hom_ext
    exact OverShriek.relocalizeOfRestricted_relocalizeToRestricted g f.hom
  · intro f
    apply Sheaf.hom_ext
    exact OverShriek.relocalizeToRestricted_relocalizeOfRestricted g f.hom
  · intro F F' G f k
    rfl
  · intro F G G' f k
    rfl

end Sheaves

section Spaces

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **Stacks 03I5, part (2), algebraicity.** An algebraic space over `S`, viewed over `S'` along
the lower-shriek extension of a morphism `g : S ⟶ S'` of the site, is an algebraic space over
`S'`.

This is Stacks 03I4 part (3) (`AlgebraicGeometry.isAlgebraicSpace_extend`) for the left adjoint
`AlgebraicGeometry.relocalizeSheafFunctor`, whose value on a sheaf is the presheaf-level extension
itself. -/
@[stacks 03I5 "part (2), algebraicity"]
theorem isAlgebraicSpace_viewOver
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    IsAlgebraicSpace B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj F) :=
  isAlgebraicSpace_extend B (B.obj hS) (B.obj hS') g
    (relocalizeSheafAdjunction B (B.obj hS) (B.obj hS') g) F hF

/-- Presheaves on the big fppf site of `S` are the same thing as presheaves on the big fppf site
of `S'` sliced over the representable presheaf of `S ⟶ S'`: the iterated-slice equivalence
identifies the big fppf site of `S` with the slice of the big fppf site of `S'` over `S ⟶ S'`, and
Stacks 00Y1 identifies presheaves on that slice with presheaves over the representable presheaf. -/
@[sga "3 I 1.4.1" "special case", sga "3 IV 4.5.2" "special case"]
noncomputable def smallerBasePresheafEquivalence :
    ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ≌
      Over (yoneda.obj (Over.mk g) : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u) :=
  ((Over.iteratedSliceEquiv (Over.mk g)).op.congrLeft (E := Type u)).symm.trans
    (OverShriek.presheafEquivalence (U := Over.mk g))

/-- Forgetting the structural morphism to the representable presheaf of `S ⟶ S'` turns
`AlgebraicGeometry.smallerBasePresheafEquivalence` into the lower-shriek extension: a section of
the extension over `W` is a factorization `ψ : W ⟶ S` of the structure morphism of `W` together
with a section over `(W, ψ)`, and the structural morphism reads off `ψ`. -/
noncomputable def smallerBasePresheafForgetIso :
    (smallerBasePresheafEquivalence B S S' hS hS' g).functor ⋙
        Over.forget (yoneda.obj (Over.mk g)) ≅
      OverShriek.relocalizePresheafFunctor g :=
  NatIso.ofComponents (fun F => NatIso.ofComponents (fun W =>
    (Equiv.toIso {
      toFun := fun ⟨φ, s⟩ => ⟨⟨φ.left, s⟩, Over.w φ⟩
      invFun := fun ⟨⟨ψ, s⟩, h⟩ => ⟨Over.homMk ψ h, s⟩
      left_inv := by rintro ⟨φ, s⟩; congr 1
      right_inv := by rintro ⟨⟨ψ, s⟩, h⟩; apply Subtype.ext; rfl }))
    (by
      intro W W' f
      ext x
      rfl))
    (by
      intro F G f
      ext W x
      rfl)

/-- **Stacks 04SG, the forward functor.** An algebraic space over `S` is an algebraic space over
`S'` with a morphism to the representable algebraic space of `S`: the lower-shriek extension, read
in the slice over that representable presheaf.

The structural morphism of the image of `F` sends a section indexed by `ψ : T ⟶ S` to `ψ`; this is
the functor every relative-property statement of Chapters 100 and 101 is written with. -/
@[stacks 04SG "the forward functor of the equivalence"]
noncomputable def spacesOverSmallerBaseFunctor :
    AlgebraicSpaces B S hS ⥤ SpacesOverSmallerBase B S S' hS hS' g :=
  ObjectProperty.lift _
    (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F) ⋙
      (smallerBasePresheafEquivalence B S S' hS hS' g).functor)
    (fun F => isAlgebraicSpace_of_iso B S' hS'
      ((smallerBasePresheafForgetIso B S S' hS hS' g).app F.1)
      (isAlgebraicSpace_viewOver B S S' hS hS' g F.1 F.2))

/-- **Stacks 04SG, the forward functor is the lower-shriek extension.** Forgetting the structural
morphism to the representable algebraic space of `S` turns
`AlgebraicGeometry.spacesOverSmallerBaseFunctor` into the lower-shriek extension of Stacks 03I5
part (2). -/
@[stacks 04SG "the forward functor is the lower-shriek extension"]
noncomputable def spacesOverSmallerBaseFunctorForgetIso :
    (spacesOverSmallerBaseFunctor B S S' hS hS' g ⋙
        ObjectProperty.ι (fun X : Over (yoneda.obj (Over.mk g) :
          (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u) => IsAlgebraicSpace B S' hS' X.left) ⋙
        Over.forget (yoneda.obj (Over.mk g))) ≅
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
          IsAlgebraicSpace B S hS F) ⋙ OverShriek.relocalizePresheafFunctor g) :=
  Functor.isoWhiskerLeft
    (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
    (smallerBasePresheafForgetIso B S S' hS hS' g)

/-- The identification `AlgebraicGeometry.spacesOverSmallerBaseFunctorForgetIso` is one of
algebraic spaces *over* the representable algebraic space of `S`, not merely of presheaves: the
structural morphism of the image of `F` sends the section of the lower-shriek extension indexed by
a factorization `ψ : T ⟶ S` to `ψ`. -/
theorem spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app
    (F : AlgebraicSpaces B S hS) (W : (BigFppfOver B S' hS')ᵒᵖ)
    (s : ((OverShriek.relocalizePresheafFunctor g).obj F.1).obj W) :
    (((spacesOverSmallerBaseFunctor B S S' hS hS' g).obj F).1.hom.app W)
        (((spacesOverSmallerBaseFunctorForgetIso B S S' hS hS' g).inv.app F).app W s) =
      Over.homMk s.1.1 s.2 := by
  apply Over.OverMorphism.ext
  rfl

/-- `AlgebraicGeometry.spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app` read in the
forward direction: starting from a section `s` of the image of `F`, the structural morphism
returns exactly the factorization `ψ : T ⟶ S` that
`AlgebraicGeometry.spacesOverSmallerBaseFunctorForgetIso` reads off `s`.

This is the direction a consumer holding a section of the image needs — the other one asks for a
section of the lower-shriek extension instead, and converting between the two means cancelling
the comparison isomorphism by hand at every use. -/
theorem spacesOverSmallerBaseFunctor_hom_app_left
    (F : AlgebraicSpaces B S hS) (W : (BigFppfOver B S' hS')ᵒᵖ)
    (s : ((spacesOverSmallerBaseFunctor B S S' hS hS' g).obj F).1.left.obj W) :
    ((((spacesOverSmallerBaseFunctor B S S' hS hS' g).obj F).1.hom.app W) s).left =
      ((((spacesOverSmallerBaseFunctorForgetIso B S S' hS hS' g).hom.app F).app W) s).1.1 :=
  rfl

end Spaces

end AlgebraicGeometry

end
