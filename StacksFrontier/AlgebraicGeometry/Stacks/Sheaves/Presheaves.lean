module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.NatIso
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory

/-!
# Two-morphisms and presheaf functors on a category fibred in groupoids

A two-morphism between categories fibred in groupoids induces canonical isomorphisms between
the associated restriction and direct-image functors on presheaves, compatibly with vertical
and horizontal composition of two-morphisms.

Every component of a two-morphism lies over an identity of the base, hence is invertible
because every morphism of a category fibred in groupoids is strongly cartesian. The resulting
natural isomorphism of underlying functors gives the restriction comparison by whiskering, and
the direct-image comparison is its mate for the two right-Kan-extension adjunctions. The two
horizontal-composition statements then come from the mate calculus: on restrictions it is
naturality of the two components, and on direct images it is `conjugateEquiv_comp` together
with the two whiskering compatibilities of the mate bijection.

## Main definitions

* `CategoryTheory.Functor.ranCompIso`: right Kan extension along a composite agrees canonically
  with iterated right Kan extension.
* `CategoryTheory.CatFiberedInGroupoids.underlyingNatIso`: the natural isomorphism of
  underlying functors defined by a two-morphism.
* `CategoryTheory.CatFiberedInGroupoids.pullbackIso`: the induced isomorphism of restriction
  functors on presheaves.
* `CategoryTheory.CatFiberedInGroupoids.pushforwardIso`: the induced isomorphism of
  direct-image functors on presheaves.

## Main results

* `CategoryTheory.CatFiberedInGroupoids.isIso_underlyingNatTrans_app`: a two-morphism is
  invertible componentwise.
* `CategoryTheory.CatFiberedInGroupoids.pullbackIso_hom_app`: the restriction comparison acts
  pointwise by the component of the two-morphism.
* `CategoryTheory.CatFiberedInGroupoids.pushforwardIso_hom`: the direct-image comparison is the
  mate of the restriction comparison.
* `CategoryTheory.CatFiberedInGroupoids.pullbackIso_trans`,
  `CategoryTheory.CatFiberedInGroupoids.pushforwardIso_trans`: compatibility with vertical
  composition.
* `CategoryTheory.CatFiberedInGroupoids.pullbackIso_hcomp`,
  `CategoryTheory.CatFiberedInGroupoids.pushforwardIso_hcomp`: compatibility with horizontal
  composition.

## Implementation notes

The results are stated for presheaves valued in any category with the required right Kan
extensions and over any base category; the source's big fppf site is a special case.
Restriction is precomposition with the opposite functor, and direct image is right Kan
extension along it.

The underlying category of a category fibred in groupoids is written
`CategoryTheory.CatFiberedInGroupoids.based` rather than the raw subtype projection `.val`.
The two are definitionally equal, but `based` is `@[reducible]` while `CatFiberedInGroupoids`
is an `abbrev` for an `InducedBicategory`, which is a semireducible `def`; a goal mentioning
the raw projection is therefore not type-correct at `implicit` transparency, and `rw` and
`simp only` both decline to rewrite in it. Spelling the statements with `based` is what makes
the mate-calculus rewrites in `pushforwardIso_hcomp` go through. For the same reason the four
opposite functors are given explicit type ascriptions at the start of that proof, so that the
adjunctions built from them record the `based` spelling of their source and target.

## References

* [Stacks Project, Tag 06TM](https://stacks.math.columbia.edu/tag/06TM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

universe v₀ v₁ v₂ v₃ v₄ u₀ u₁ u₂ u₃ u₄

namespace CategoryTheory.Functor

/-- Right Kan extension along a composite agrees canonically with iterated right Kan
extension. -/
noncomputable def ranCompIso {C : Type u₀} [Category.{v₀} C]
    {D : Type u₁} [Category.{v₁} D] {E : Type u₃} [Category.{v₃} E]
    (F : C ⥤ D) (G : D ⥤ E) (A : Type u₂) [Category.{v₂} A]
    [∀ P : C ⥤ A, F.HasRightKanExtension P]
    [∀ P : D ⥤ A, G.HasRightKanExtension P]
    [∀ P : C ⥤ A, (F ⋙ G).HasRightKanExtension P] :
    (F ⋙ G).ran (H := A) ≅ F.ran (H := A) ⋙ G.ran (H := A) :=
  ((F ⋙ G).ranAdjunction A).rightAdjointUniq
    (((G.ranAdjunction A).comp (F.ranAdjunction A)).ofNatIsoLeft
      (eqToIso
        (rfl :
          (Functor.whiskeringLeft D E A).obj G ⋙ (Functor.whiskeringLeft C D A).obj F =
            (Functor.whiskeringLeft C E A).obj (F ⋙ G))))

end CategoryTheory.Functor

namespace CategoryTheory.CatFiberedInGroupoids

variable {B : Type u₀} [Category.{v₀} B]
variable {𝒳 𝒴 : CatFiberedInGroupoids.{v₀, v₁, u₀, u₁} B}

/-- **Stacks 06TM.** Every component of a two-morphism of categories fibred in groupoids lies
over an identity, hence is invertible. -/
@[stacks 06TM "invertibility of the two-morphism"]
theorem isIso_underlyingNatTrans_app {f g : 𝒳 ⟶ 𝒴} (t : f ⟶ g) (x : 𝒳.based.obj) :
    IsIso (t.hom.toNatTrans.app x) := by
  have := CatFiberedInGroupoids.isHomLift_app t x
  have hsc : 𝒴.based.p.IsStronglyCartesian (𝟙 (𝒳.based.p.obj x)) (t.hom.toNatTrans.app x) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift 𝒴.2 _ _
  exact IsStronglyCartesian.isIso_of_base_isIso (p := 𝒴.based.p)
    (f := 𝟙 (𝒳.based.p.obj x)) (t.hom.toNatTrans.app x)

/-- The natural isomorphism of underlying functors defined by a two-morphism. -/
noncomputable def underlyingNatIso {f g : 𝒳 ⟶ 𝒴} (t : f ⟶ g) :
    CatFiberedInGroupoids.homFunctor f ≅ CatFiberedInGroupoids.homFunctor g := by
  have : ∀ x : 𝒳.based.obj, IsIso (t.hom.toNatTrans.app x) := isIso_underlyingNatTrans_app t
  have := NatIso.isIso_of_isIso_app t.hom.toNatTrans
  exact asIso (t.hom.toNatTrans : CatFiberedInGroupoids.homFunctor f ⟶
    CatFiberedInGroupoids.homFunctor g)

/-- The opposite of the functor underlying a one-morphism of categories fibred in groupoids,
with its source and target spelled through `CatFiberedInGroupoids.based`.

This is `(CatFiberedInGroupoids.homFunctor G).op` and is `@[reducible]`, so the two are
interchangeable. It exists because `homFunctor` is declared with the raw subtype projection in
its result type, so `(homFunctor G).op` carries `(𝒳.val).obj` as an implicit argument of
`Functor.op`; that argument is not type-correct at `implicit` transparency and therefore blocks
`rw` and `simp only` in any goal containing it. Writing `homFunctorOp G` keeps the same term up
to reducible unfolding while recording the `based` spelling instead. -/
@[reducible]
def homFunctorOp {𝒳 𝒴 : CatFiberedInGroupoids.{v₀, v₁, u₀, u₁} B} (G : 𝒳 ⟶ 𝒴) :
    𝒳.based.objᵒᵖ ⥤ 𝒴.based.objᵒᵖ :=
  (CatFiberedInGroupoids.homFunctor G).op

variable (A : Type u₂) [Category.{v₂} A]
variable {f g : 𝒳 ⟶ 𝒴} (t : f ⟶ g)

/-- **Stacks 06TM.** Pullback of presheaves along the isomorphism of functors underlying a
two-morphism, contravariant in the two-morphism. -/
@[stacks 06TM "canonical isomorphism on restriction functors"]
noncomputable def pullbackIso :
    (whiskeringLeft 𝒳.based.objᵒᵖ 𝒴.based.objᵒᵖ A).obj
        (homFunctorOp g) ≅
      (whiskeringLeft 𝒳.based.objᵒᵖ 𝒴.based.objᵒᵖ A).obj
        (homFunctorOp f) :=
  (whiskeringLeft 𝒳.based.objᵒᵖ 𝒴.based.objᵒᵖ A).mapIso (NatIso.op (underlyingNatIso t))

/-- **Stacks 06TM.** On a presheaf and an object, the restriction comparison is evaluation on
the component of the given two-morphism. -/
@[stacks 06TM "pointwise description of restriction"]
theorem pullbackIso_hom_app (P : 𝒴.based.objᵒᵖ ⥤ A) (x : 𝒳.based.obj) :
    ((pullbackIso A t).hom.app P).app (Opposite.op x) =
      P.map (t.hom.toNatTrans.app x).op := by
  simp [pullbackIso, underlyingNatIso]

/-- **Stacks 06TM.** Vertical composition of two-morphisms becomes composition of the induced
restriction isomorphisms, in reverse order. -/
@[stacks 06TM "vertical composition on restriction"]
theorem pullbackIso_trans {h : 𝒳 ⟶ 𝒴} (s : g ⟶ h) :
    pullbackIso A (t ≫ s) = pullbackIso A s ≪≫ pullbackIso A t := by
  ext P x
  simp only [whiskeringLeft_obj_obj, comp_obj, op_obj,
    Bicategory.InducedBicategory.bicategory_Hom, Iso.trans_hom, NatTrans.comp_app]
  change P.map
      (t.hom.toNatTrans.app (Opposite.unop x) ≫
        s.hom.toNatTrans.app (Opposite.unop x)).op = _
  simp [pullbackIso, underlyingNatIso]

/-- **Stacks 06TM.** The restriction comparison for a horizontal composite acts pointwise by
the two component maps, in the contravariant order. -/
@[stacks 06TM "horizontal composition on restriction"]
theorem pullbackIso_hcomp {𝒵 : CatFiberedInGroupoids.{v₀, v₁, u₀, u₁} B}
    {h k : 𝒴 ⟶ 𝒵} (s : h ⟶ k) (P : 𝒵.based.objᵒᵖ ⥤ A) (x : 𝒳.based.obj) :
    ((pullbackIso (f := f ≫ h) (g := g ≫ k) A
      (Bicategory.whiskerRight t h ≫ Bicategory.whiskerLeft g s)).hom.app P).app
        (Opposite.op x) =
      P.map (s.hom.toNatTrans.app ((CatFiberedInGroupoids.homFunctor g).obj x)).op ≫
        P.map ((CatFiberedInGroupoids.homFunctor h).map (t.hom.toNatTrans.app x)).op := by
  simp only [whiskeringLeft_obj_obj, comp_obj, op_obj,
    Bicategory.InducedBicategory.bicategory_Hom]
  change P.map
    (((CatFiberedInGroupoids.homFunctor h).map (t.hom.toNatTrans.app x) ≫
      s.hom.toNatTrans.app ((CatFiberedInGroupoids.homFunctor g).obj x)).op) = _
  simp only [CategoryTheory.op_comp, Functor.map_comp]

/-- The restriction comparison for a horizontal composite is the horizontal composite of the
two restriction comparisons. -/
private theorem pullbackIso_hcomp_hom {𝒵 : CatFiberedInGroupoids.{v₀, v₁, u₀, u₁} B}
    {h k : 𝒴 ⟶ 𝒵} (s : h ⟶ k) :
    (pullbackIso (f := f ≫ h) (g := g ≫ k) A
        (Bicategory.whiskerRight t h ≫ Bicategory.whiskerLeft g s)).hom =
      whiskerRight (pullbackIso A s).hom
          ((whiskeringLeft 𝒳.based.objᵒᵖ 𝒴.based.objᵒᵖ A).obj (homFunctorOp g)) ≫
        whiskerLeft ((whiskeringLeft 𝒴.based.objᵒᵖ 𝒵.based.objᵒᵖ A).obj (homFunctorOp h))
          (pullbackIso A t).hom := by
  ext P x
  rw [pullbackIso_hcomp]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.whiskeringLeft_obj_map, Functor.whiskeringLeft_obj_obj]
  have hs : ((pullbackIso A s).hom.app P).app ((homFunctorOp g).obj x) =
      P.map (s.hom.toNatTrans.app
        ((CatFiberedInGroupoids.homFunctor g).obj (Opposite.unop x))).op := by
    simpa using pullbackIso_hom_app (A := A) (t := s) P
      ((CatFiberedInGroupoids.homFunctor g).obj (Opposite.unop x))
  have ht : ((pullbackIso A t).hom.app (homFunctorOp h ⋙ P)).app x =
      P.map ((CatFiberedInGroupoids.homFunctor h).map
        (t.hom.toNatTrans.app (Opposite.unop x))).op := by
    simpa using pullbackIso_hom_app (A := A) (t := t) (homFunctorOp h ⋙ P) (Opposite.unop x)
  rw [hs, ht]

section RightKanExtension

variable [∀ (F : 𝒳.based.objᵒᵖ ⥤ A),
  (homFunctorOp f).HasRightKanExtension F]
variable [∀ (F : 𝒳.based.objᵒᵖ ⥤ A),
  (homFunctorOp g).HasRightKanExtension F]

/-- **Stacks 06TM.** Direct image of presheaves along the isomorphism of functors underlying a
two-morphism, obtained as the adjoint mate of the pullback isomorphism. -/
@[stacks 06TM "canonical isomorphism on right adjoints"]
noncomputable def pushforwardIso :
    (homFunctorOp f).ran (H := A) ≅
      (homFunctorOp g).ran (H := A) :=
  conjugateIsoEquiv ((homFunctorOp f).ranAdjunction A)
    ((homFunctorOp g).ranAdjunction A) (pullbackIso A t)

/-- **Stacks 06TM.** The direct-image comparison is the mate of the restriction comparison,
expressing compatibility with both adjunctions. -/
@[stacks 06TM "compatibility with adjunction"]
theorem pushforwardIso_hom :
    (pushforwardIso A t).hom =
      conjugateEquiv ((homFunctorOp f).ranAdjunction A)
        ((homFunctorOp g).ranAdjunction A)
        (pullbackIso A t).hom := rfl

/-- **Stacks 06TM.** Vertical composition of two-morphisms becomes composition of the
corresponding direct-image isomorphisms. -/
@[stacks 06TM "vertical composition on right adjoints"]
theorem pushforwardIso_trans {h : 𝒳 ⟶ 𝒴} (s : g ⟶ h)
    [∀ (F : 𝒳.based.objᵒᵖ ⥤ A),
      (homFunctorOp h).HasRightKanExtension F] :
    pushforwardIso A (t ≫ s) = pushforwardIso A t ≪≫ pushforwardIso A s := by
  apply Iso.ext
  rw [Iso.trans_hom, pushforwardIso_hom, pushforwardIso_hom, pushforwardIso_hom,
    pullbackIso_trans, Iso.trans_hom]
  exact (conjugateEquiv_comp _ _ _ _ _).symm

/-- **Stacks 06TM.** The direct-image comparison for a horizontal composite, after identifying
direct images of composites with successive direct images, is the horizontal composite of the
two direct-image comparisons. -/
@[stacks 06TM "horizontal composition on right adjoints"]
theorem pushforwardIso_hcomp {𝒵 : CatFiberedInGroupoids.{v₀, v₁, u₀, u₁} B}
    {h k : 𝒴 ⟶ 𝒵} (s : h ⟶ k)
    [∀ (P : 𝒴.based.objᵒᵖ ⥤ A),
      (homFunctorOp h).HasRightKanExtension P]
    [∀ (P : 𝒴.based.objᵒᵖ ⥤ A),
      (homFunctorOp k).HasRightKanExtension P]
    [∀ (F : 𝒳.based.objᵒᵖ ⥤ A),
      (homFunctorOp (f ≫ h)).HasRightKanExtension F]
    [∀ (F : 𝒳.based.objᵒᵖ ⥤ A),
      (homFunctorOp (g ≫ k)).HasRightKanExtension F]
    [∀ (F : 𝒳.based.objᵒᵖ ⥤ A),
      ((homFunctorOp f) ⋙
        (homFunctorOp h)).HasRightKanExtension F]
    [∀ (F : 𝒳.based.objᵒᵖ ⥤ A),
      ((homFunctorOp g) ⋙
        (homFunctorOp k)).HasRightKanExtension F] :
    pushforwardIso A (Bicategory.whiskerRight t h ≫ Bicategory.whiskerLeft g s) ≪≫
        ranCompIso (homFunctorOp g)
          (homFunctorOp k) A =
      ranCompIso (homFunctorOp f)
          (homFunctorOp h) A ≪≫
        Functor.isoWhiskerRight (pushforwardIso A t)
          ((homFunctorOp h).ran (H := A)) ≪≫
        Functor.isoWhiskerLeft ((homFunctorOp g).ran (H := A))
        (pushforwardIso A s) := by
  let F := homFunctorOp f
  let G := homFunctorOp g
  let H := homFunctorOp h
  let K := homFunctorOp k
  let adjF := F.ranAdjunction A
  let adjG := G.ranAdjunction A
  let adjH := H.ranAdjunction A
  let adjK := K.ranAdjunction A
  let adjFH := (homFunctorOp (f ≫ h)).ranAdjunction A
  let adjGK := (homFunctorOp (g ≫ k)).ranAdjunction A
  let adjCompFH := (adjH.comp adjF).ofNatIsoLeft
    (eqToIso (rfl :
      (whiskeringLeft 𝒴.based.objᵒᵖ 𝒵.based.objᵒᵖ A).obj H ⋙
        (whiskeringLeft 𝒳.based.objᵒᵖ 𝒴.based.objᵒᵖ A).obj F =
      (whiskeringLeft 𝒳.based.objᵒᵖ 𝒵.based.objᵒᵖ A).obj (F ⋙ H)))
  let adjCompGK := (adjK.comp adjG).ofNatIsoLeft
    (eqToIso (rfl :
      (whiskeringLeft 𝒴.based.objᵒᵖ 𝒵.based.objᵒᵖ A).obj K ⋙
        (whiskeringLeft 𝒳.based.objᵒᵖ 𝒴.based.objᵒᵖ A).obj G =
      (whiskeringLeft 𝒳.based.objᵒᵖ 𝒵.based.objᵒᵖ A).obj (G ⋙ K)))
  have hcompFH : adjCompFH = adjH.comp adjF := by simp [adjCompFH, Adjunction.ofNatIsoLeft]
  have hcompGK : adjCompGK = adjK.comp adjG := by simp [adjCompGK, Adjunction.ofNatIsoLeft]
  -- The comparison on left adjoints is an equality of functors, not merely an isomorphism, so
  -- it is `eqToHom` of a named equation rather than `Iso.refl`. Spelling it as `Iso.refl`
  -- leaves the goal ill-typed at `implicit` transparency -- the two endpoints are
  -- definitionally but not syntactically equal -- which again stops `rw`.
  have hFHeq :
      (whiskeringLeft 𝒴.based.objᵒᵖ 𝒵.based.objᵒᵖ A).obj H ⋙
          (whiskeringLeft 𝒳.based.objᵒᵖ 𝒴.based.objᵒᵖ A).obj F =
        (whiskeringLeft 𝒳.based.objᵒᵖ 𝒵.based.objᵒᵖ A).obj (homFunctorOp (f ≫ h)) := rfl
  have hGKeq :
      (whiskeringLeft 𝒴.based.objᵒᵖ 𝒵.based.objᵒᵖ A).obj K ⋙
          (whiskeringLeft 𝒳.based.objᵒᵖ 𝒴.based.objᵒᵖ A).obj G =
        (whiskeringLeft 𝒳.based.objᵒᵖ 𝒵.based.objᵒᵖ A).obj (homFunctorOp (g ≫ k)) := rfl
  apply Iso.ext
  change
    (conjugateEquiv adjFH adjGK
        (pullbackIso A (Bicategory.whiskerRight t h ≫ Bicategory.whiskerLeft g s)).hom ≫
      conjugateEquiv adjGK adjCompGK (eqToHom hGKeq.symm)) =
    (conjugateEquiv adjFH adjCompFH (eqToHom hFHeq.symm) ≫
      whiskerRight (conjugateEquiv adjF adjG (pullbackIso A t).hom)
        ((homFunctorOp h).ran (H := A)) ≫
      whiskerLeft ((homFunctorOp g).ran (H := A))
        (conjugateEquiv adjH adjK (pullbackIso A s).hom))
  rw [hcompFH, hcompGK, conjugateEquiv_comp,
    ← conjugateEquiv_whiskerLeft adjF adjG adjH (pullbackIso A t).hom,
    ← conjugateEquiv_whiskerRight adjH adjK adjG (pullbackIso A s).hom,
    conjugateEquiv_comp, conjugateEquiv_comp, pullbackIso_hcomp_hom]
  apply congrArg (conjugateEquiv adjFH (adjK.comp adjG))
  change (𝟙 _ ≫ _) = _ ≫ 𝟙 _
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end RightKanExtension

end CategoryTheory.CatFiberedInGroupoids

end
