module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Types.Products
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FormallySmoothOnObjects

/-!
# Testing formal smoothness on the base changes of a representable 1-morphism

A 1-morphism of categories fibred in groupoids over the big fppf category of a scheme `S` which
is representable by algebraic spaces is formally smooth on objects exactly when, for every
scheme-valued point `U` of the target, every algebraic space representing the base change has
formally smooth structural morphism *over `U`* — that is, the unique transformation from its
functor of points to the terminal presheaf on the big fppf category over `U` is formally smooth.

## Main results

* `AlgebraicGeometry.BigFppfOver.formallySmooth_relocalize_iff`: for a transformation from the
  lower-shriek extension of a presheaf on the big fppf category over `U` to the representable
  presheaf of `U` which reads off the factorization through `U`, formal smoothness is equivalent
  to formal smoothness of the transformation to the terminal presheaf upstairs.
* `AlgebraicGeometry.BigFppfOver.isRelativelyFormallySmooth_iff_formallySmooth_terminalFrom`:
  formal smoothness of a 1-morphism, in the sense of Stacks 03YK, read with the structural
  morphism of the representing space taken over `U` rather than over `S`.
* `AlgebraicGeometry.BigFppfOver.isFormallySmoothOnObjects_iff_formallySmooth_terminalFrom`:
  **Stacks 0H1K.**

## Implementation notes

The two readings of "the structural morphism of the representing space" differ by the
equivalence of Stacks 04SG. Over `S`, a presheaf `F` on the big fppf category over `U` is
presented by its lower-shriek extension
`CategoryTheory.OverShriek.relocalizePresheafFunctor` together with the transformation to the
representable presheaf of `U` reading off the factorization; that is the shape
`AlgebraicGeometry.BigFppfOver.IsRelativelyFormallySmooth` uses, through
`AlgebraicGeometry.spacesOverSmallerBaseFunctorForgetIso`. Over `U`, the structural morphism is
the unique transformation to the terminal presheaf. `formallySmooth_relocalize_iff` identifies
formal smoothness of the two, by transporting an affine square-zero square across the two
categories: downwards a square over `U` is composed with `U`, upwards the factorization of the
source of a square over `S` is read off the section it carries.

That reading-off is the only place the lower-shriek extension's restriction maps are used; it is
`CategoryTheory.OverShriek.relocalizePresheafFunctor_map_val`, which holds by definitional
unfolding, and
`CategoryTheory.OverShriek.sigmaMk_eq`, which is what identifies the pair indexed by
`i ≫ T'.hom` with the pair indexed by `T.hom`. No cast or `eqToHom` appears: the two indices are
equal only propositionally, and `sigmaMk_eq` states the resulting equality of pairs directly.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 06D3](https://stacks.math.columbia.edu/tag/06D3)
* [Stacks Project, Tag 0H1K](https://stacks.math.columbia.edu/tag/0H1K)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

universe u v w

namespace CategoryTheory

/-- The value at an object of the terminal presheaf of types is a singleton: evaluation
preserves the terminal object, and a terminal type is a singleton. -/
@[instance_reducible]
noncomputable def Limits.uniqueTerminalFunctorObj {C : Type u} [Category.{w} C] (X : C) :
    Unique ((⊤_ (C ⥤ Type v)).obj X) :=
  Limits.Types.isTerminalEquivUnique _
    (Limits.IsTerminal.isTerminalObj ((evaluation C (Type v)).obj X) _
      Limits.terminalIsTerminal)

namespace OverShriek

variable {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U)

/-- Restriction in the lower-shriek extension of `G` along `f : V ⟶ U`, read on the pair a
section is: restricting along `i : W ⟶ W'` precomposes the factorization through `V` with `i`
and restricts the section of `G` along the resulting morphism of `C/V`.

Stated on the underlying pair rather than on the section itself, so that no witness of the
factorization has to be produced on the right-hand side. -/
theorem relocalizePresheafFunctor_map_val (G : (Over V)ᵒᵖ ⥤ Type v) {W W' : Over U}
    (i : W ⟶ W') (s : ((relocalizePresheafFunctor f).obj G).obj (op W')) :
    (((relocalizePresheafFunctor f).obj G).map i.op s).1 =
      ⟨i.left ≫ s.1.1,
        G.map (Over.homMk i.left rfl : Over.mk (i.left ≫ s.1.1) ⟶ Over.mk s.1.1).op s.1.2⟩ :=
  rfl

end OverShriek

end CategoryTheory

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Formal smoothness is unchanged by precomposition with an isomorphism of the source, in the
two-sided form: if `e.hom ≫ a' = a` for an isomorphism `e` of the sources, then `a` is formally
smooth exactly when `a'` is. -/
theorem formallySmooth_iff_of_isoComp {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (e : X ≅ X')
    {a : X ⟶ Y} {a' : X' ⟶ Y} (h : e.hom ≫ a' = a) :
    Space.FormallySmooth a ↔ Space.FormallySmooth a' := by
  refine ⟨fun ha => ?_, fun ha' => h ▸ Space.FormallySmooth.isoComp e ha'⟩
  have h' : e.inv ≫ a = a' := by
    rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  exact h' ▸ Space.FormallySmooth.isoComp e.symm ha

/-- An algebraic space over `U` has formally smooth structural morphism read over `S` exactly
when it has formally smooth structural morphism read over `U`.

Over `S` the space is presented by the lower-shriek extension of its functor of points `F`,
together with a transformation `a` to the representable presheaf of `U` which reads off the
factorization through `U` carried by a section; over `U` it is presented by `F` itself, with the
unique transformation to the terminal presheaf as structural morphism.

An affine square-zero square over `U` becomes one over `S` by composing both of its objects with
`U`, and the given section determines the section of the lower-shriek extension over the smaller
one; conversely a square over `S` with a section of the lower-shriek extension over its smaller
object determines a square over `U` by reading off that section's factorization, which the
hypothesis `ha` forces to be the one named by the square's section upstairs. -/
@[sga "3 XI 1.6" "special case"]
theorem formallySmooth_relocalize_iff (U : BigFppfOver B S hS)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (a : (OverShriek.relocalizePresheafFunctor U.hom).obj F ⟶ yoneda.obj U)
    (ha : ∀ (T : BigFppfOver B S hS)
      (s : ((OverShriek.relocalizePresheafFunctor U.hom).obj F).obj (op T)),
      a.app (op T) s = Over.homMk s.1.1 s.2) :
    Space.FormallySmooth a ↔ Space.FormallySmooth (terminal.from F) := by
  constructor
  · intro hs T T' hT hT' i hi x y hxy
    have hxval : T.hom ≫ U.hom = i.left ≫ T'.hom ≫ U.hom := by
      rw [← Category.assoc, Over.w i]
    obtain ⟨zS, hzS⟩ := hs (Over.mk (i.left ≫ T'.hom ≫ U.hom)) (Over.mk (T'.hom ≫ U.hom))
      hT hT' (Over.homMk i.left rfl) hi ⟨⟨T.hom, x⟩, hxval⟩ (Over.homMk T'.hom rfl) (by
        rw [ha (Over.mk (i.left ≫ T'.hom ≫ U.hom)) ⟨⟨T.hom, x⟩, hxval⟩]
        exact Over.OverMorphism.ext (Over.w i).symm)
    obtain ⟨⟨ψ, z⟩, hψ⟩ := zS
    have hψleft : ψ = T'.hom :=
      congrArg Over.Hom.left
        ((ha (Over.mk (T'.hom ≫ U.hom)) ⟨⟨ψ, z⟩, hψ⟩).symm.trans hzS.2)
    subst hψleft
    refine ⟨z, ?_, ?_⟩
    · have hmap := (OverShriek.relocalizePresheafFunctor_map_val U.hom F
        (Over.homMk i.left rfl : Over.mk (i.left ≫ T'.hom ≫ U.hom) ⟶
          Over.mk (T'.hom ≫ U.hom)) ⟨⟨T'.hom, z⟩, hψ⟩).symm.trans (congrArg Subtype.val hzS.1)
      have hshift := OverShriek.sigmaMk_eq F z
        (Over.homMk i.left rfl : Over.mk (i.left ≫ T'.hom) ⟶ Over.mk T'.hom)
        (i : Over.mk T.hom ⟶ Over.mk T'.hom) rfl
      simpa using hshift.symm.trans hmap
    · have hu := Limits.uniqueTerminalFunctorObj
        (C := (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) (op T')
      exact (hu.uniq _).trans (hu.uniq _).symm
  · intro hs T T' hT hT' i hi x y hxy
    obtain ⟨⟨ψ, xF⟩, hψ⟩ := x
    have hfac : ψ = i.left ≫ y.left := by
      rw [ha T ⟨⟨ψ, xF⟩, hψ⟩] at hxy
      exact congrArg Over.Hom.left hxy
    subst hfac
    have hu := Limits.uniqueTerminalFunctorObj
      (C := (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) (op (Over.mk (i.left ≫ y.left)))
    obtain ⟨z, hz⟩ := hs (Over.mk (i.left ≫ y.left)) (Over.mk y.left) hT hT'
      (Over.homMk i.left rfl) hi xF
      (Limits.uniqueTerminalFunctorObj
        (C := (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) (op (Over.mk y.left))).default
      ((hu.uniq _).trans (hu.uniq _).symm)
    refine ⟨⟨⟨y.left, z⟩, Over.w y⟩, ?_, ?_⟩
    · exact Subtype.ext ((OverShriek.relocalizePresheafFunctor_map_val U.hom F i
        ⟨⟨y.left, z⟩, Over.w y⟩).trans (congrArg (Sigma.mk (i.left ≫ y.left)) hz.1))
    · rw [ha T' ⟨⟨y.left, z⟩, Over.w y⟩]
      exact Over.OverMorphism.ext rfl

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- Formal smoothness of a 1-morphism representable by algebraic spaces, in the sense of
Stacks 03YK, read with the structural morphism of the representing space taken over the
scheme-valued point `U` of the target rather than over `S`: the unique transformation from the
functor of points of the representing space to the terminal presheaf on the big fppf category
over `U` is formally smooth.

The two readings are identified by `AlgebraicGeometry.BigFppfOver.formallySmooth_relocalize_iff`,
across the comparison `AlgebraicGeometry.spacesOverSmallerBaseFunctorForgetIso` of Stacks
04SG. -/
theorem isRelativelyFormallySmooth_iff_formallySmooth_terminalFrom (p : 𝒳 ⟶ 𝒴) :
    IsRelativelyFormallySmooth B S hS p ↔
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (_hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
          Nonempty (StacksRepresentableCFG.EquivalenceOver
            (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
              (CatFiberedInGroupoids.homFunctor p))
            (presheafOfCategories (F ⋙ typeToCat)).p) →
          Space.FormallySmooth (terminal.from F) := by
  have key (U : BigFppfOver B S hS) (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F) :
      Space.FormallySmooth
          (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom ↔
        Space.FormallySmooth (terminal.from F) := by
    let e := (spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).app ⟨F, hF⟩
    let g := (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom
    refine ((formallySmooth_iff_of_isoComp B S hS e.symm
      (a := e.inv ≫ g) (a' := g) rfl).symm).trans ?_
    refine formallySmooth_relocalize_iff B S hS U F (e.inv ≫ g) (fun T s => ?_)
    exact spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app
      B U.left.1 S U.left.2 hS U.hom ⟨F, hF⟩ (op T) s
  exact forall_congr' fun U => forall_congr' fun y => forall_congr' fun _ =>
    forall_congr' fun F => forall_congr' fun hF => imp_congr_right fun _ => key U F hF

/-- **Stacks 0H1K.** A 1-morphism of categories fibred in groupoids over the big fppf category
of `S` which is representable by algebraic spaces is formally smooth on objects exactly when,
for every scheme-valued point `U` of the target, every algebraic space representing the base
change of it along that point is formally smooth over `U`.

This is Stacks 06D3,
`AlgebraicGeometry.BigFppfOver.isFormallySmoothOnObjects_iff_isRelativelyFormallySmooth`, with
the structural morphism of the representing space read over `U` rather than over `S`, which is
`AlgebraicGeometry.BigFppfOver.isRelativelyFormallySmooth_iff_formallySmooth_terminalFrom`. -/
@[stacks 0H1K]
theorem isFormallySmoothOnObjects_iff_formallySmooth_terminalFrom (p : 𝒳 ⟶ 𝒴)
    (hp : Stack.IsRepresentableByAlgebraicSpaces B S hS p.hom) :
    Stack.IsFormallySmoothOnObjects B S hS 𝒳 𝒴 p ↔
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (_hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
          Nonempty (StacksRepresentableCFG.EquivalenceOver
            (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
              (CatFiberedInGroupoids.homFunctor p))
            (presheafOfCategories (F ⋙ typeToCat)).p) →
          Space.FormallySmooth (terminal.from F) :=
  (isFormallySmoothOnObjects_iff_isRelativelyFormallySmooth B S hS p hp).trans
    (isRelativelyFormallySmooth_iff_formallySmooth_terminalFrom B S hS p)

end AlgebraicGeometry.BigFppfOver

end
