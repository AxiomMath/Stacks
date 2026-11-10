module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueingSubterminal

/-!
# Fullness of the glueing functor over a subterminal base

`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueingSubterminal` proves the
faithfulness half of Stacks 0E8Z over a base `Z` which is only *subterminal* in the big fppf
site, rather than terminal. This file does the same for fullness.

The argument of
`AlgebraicGeometry.FinitePresentationSpacesOver.full_glueingFunctor` glues a pair of
base-changed morphisms by the sheaf condition at the Mayer--Vietoris square of each object `T`
of the site. Over a terminal base that square exists at every `T`; over a subterminal base it
exists at every `T` *equipped with a morphism to `Z`*, by
`AlgebraicGeometry.FinitePresentationSpacesOver.mayerVietorisSquareOfHom`. That is enough,
because the morphism is only ever needed at an object carrying a section of the source `X`, and
such a section maps to a morphism `T ⟶ Z` under the structure morphism of `X`. So the glued
morphism is defined section by section, each section supplying the morphism to `Z` that its own
glueing needs.

Nothing here assumes that every object of the site admits a morphism to `Z`: such an assumption
would make a subterminal `Z` terminal, and the generalisation would be empty.

## Main results

* `CategoryTheory.IsSubterminal.yonedaObj`: the representable presheaf of a subterminal object
  is subterminal. This is what replaces the terminality of `yoneda.obj Z` used to see that a
  morphism of presheaves over `Z` commutes with the structure morphisms.
* `CategoryTheory.Over.pullbackSectionsEquivOfIsSubterminal` and its companions: the sections
  over an object lying over a subterminal `U` of a base change along `yoneda.map (j : U ⟶ Z)`,
  for `Z` subterminal rather than terminal.
* `AlgebraicGeometry.FinitePresentationSpacesOver.isPullback_sections_prodSquare`: the sheaf
  condition at the square `V ⨯ T, U ⨯ T, W ⨯ T, T`, in a form independent of the choice of a
  morphism `T ⟶ Z`, with `glueProdOfHom` and `sheafSection_ext_prod_of_hom` reading off the
  glueing and the uniqueness.
* `AlgebraicGeometry.FinitePresentationSpacesOver.glueingFullOverHomOfIsSubterminal`: the
  morphism glued from a compatible pair of base-changed morphisms, and
  `pullback_map_glueingFullOverHomOfIsSubterminal_left` and `..._right`, which identify its two
  base changes with the given pair.
* `AlgebraicGeometry.FinitePresentationSpacesOver.full_glueingFunctor_of_isSubterminal`: the
  glueing functor is full over a subterminal base.

## References

* [Stacks Project, Tag 0E8Z](https://stacks.math.columbia.edu/tag/0E8Z)
* [Stacks Project, Tag 0E91](https://stacks.math.columbia.edu/tag/0E91)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- **The representable presheaf of a subterminal object is subterminal**: two morphisms into
it out of a presheaf `F` take a section of `F` to two morphisms into the object, which agree. -/
theorem IsSubterminal.yonedaObj {Z : C} (hZ : IsSubterminal Z) :
    IsSubterminal (yoneda.obj Z : Cᵒᵖ ⥤ Type v) := fun _ _ _ =>
  NatTrans.ext (funext fun _ => ConcreteCategory.hom_ext _ _ fun _ => hZ _ _)

/-! ### Sections of a base change over a subterminal base -/

section PullbackSections

variable {Z U : C} (hZ : IsSubterminal Z) (j : U ⟶ Z) (hU : IsSubterminal U)

/-- **Over an object lying over a subterminal `U`, the base change along the Yoneda image of
`j : U ⟶ Z` has the same sections as the presheaf itself**, the bijection being the first
projection. This is `CategoryTheory.Over.pullbackSectionsEquiv` with terminality of `Z`
weakened to subterminality, which is all that its proof uses. -/
noncomputable def Over.pullbackSectionsEquivOfIsSubterminal
    (X : Over (yoneda.obj Z : Cᵒᵖ ⥤ Type v)) {T : C} (hT : Nonempty (T ⟶ U)) :
    ((Over.pullback (yoneda.map j)).obj X).left.obj (op T) ≃ X.left.obj (op T) :=
  Equiv.ofBijective _ (hT.elim fun p => bijective_pullback_fst_app j hZ hU X p)

/-- `CategoryTheory.Over.pullbackSectionsEquivOfIsSubterminal` sends a section of the base
change to its image under the first projection. -/
@[simp]
theorem Over.pullbackSectionsEquivOfIsSubterminal_apply
    (X : Over (yoneda.obj Z : Cᵒᵖ ⥤ Type v)) {T : C} (hT : Nonempty (T ⟶ U))
    (z : ((Over.pullback (yoneda.map j)).obj X).left.obj (op T)) :
    Over.pullbackSectionsEquivOfIsSubterminal hZ j hU X hT z =
      (pullback.fst X.hom (yoneda.map j)).app (op T) z :=
  rfl

/-- The map on sections over an object lying over a subterminal `U` induced by a morphism of the
base changes along the Yoneda image of `j : U ⟶ Z`, for `Z` subterminal. This is
`CategoryTheory.Over.pullbackSectionsMap` over a subterminal base. -/
noncomputable def Over.pullbackSectionsMapOfIsSubterminal
    {X Y : Over (yoneda.obj Z : Cᵒᵖ ⥤ Type v)}
    (m : (Over.pullback (yoneda.map j)).obj X ⟶ (Over.pullback (yoneda.map j)).obj Y) {T : C}
    (hT : Nonempty (T ⟶ U)) : X.left.obj (op T) → Y.left.obj (op T) :=
  fun x => Over.pullbackSectionsEquivOfIsSubterminal hZ j hU Y hT
    (m.left.app (op T) ((Over.pullbackSectionsEquivOfIsSubterminal hZ j hU X hT).symm x))

/-- `CategoryTheory.Over.pullbackSectionsMapOfIsSubterminal` is characterised by its
compatibility with the first projections from the two base changes. -/
theorem Over.pullbackSectionsMapOfIsSubterminal_fst {X Y : Over (yoneda.obj Z : Cᵒᵖ ⥤ Type v)}
    (m : (Over.pullback (yoneda.map j)).obj X ⟶ (Over.pullback (yoneda.map j)).obj Y) {T : C}
    (hT : Nonempty (T ⟶ U)) (z : ((Over.pullback (yoneda.map j)).obj X).left.obj (op T)) :
    Over.pullbackSectionsMapOfIsSubterminal hZ j hU m hT
        ((pullback.fst X.hom (yoneda.map j)).app (op T) z) =
      (pullback.fst Y.hom (yoneda.map j)).app (op T) (m.left.app (op T) z) :=
  congrArg (fun w => Over.pullbackSectionsEquivOfIsSubterminal hZ j hU Y hT
      (m.left.app (op T) w))
    ((Over.pullbackSectionsEquivOfIsSubterminal hZ j hU X hT).symm_apply_apply z)

/-- A morphism of the slice whose components agree with a given map of base changes over every
object lying over `U` has that map as its base change. -/
private theorem pullback_map_eq_of_forall_app_eq {X Y : Over (yoneda.obj Z : Cᵒᵖ ⥤ Type v)}
    (m : (Over.pullback (yoneda.map j)).obj X ⟶ (Over.pullback (yoneda.map j)).obj Y)
    (f : X ⟶ Y) (h : ∀ (T : Cᵒᵖ) (hT : Nonempty (T.unop ⟶ U)) (x : X.left.obj T),
      f.left.app T x = Over.pullbackSectionsMapOfIsSubterminal hZ j hU m hT x) :
    (Over.pullback (yoneda.map j)).map f = m := by
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w m).symm))
  refine (Over.pullback_map_left_comp_fst (yoneda.map j) _).trans ?_
  refine NatTrans.ext (funext fun T => ConcreteCategory.hom_ext _ _ fun z => ?_)
  simp only [NatTrans.comp_app, types_comp_apply]
  rw [h T ⟨(pullback.snd X.hom (yoneda.map j)).app T z⟩,
    Over.pullbackSectionsMapOfIsSubterminal_fst]

/-- `CategoryTheory.Over.pullbackSectionsMapOfIsSubterminal` is natural in the object lying over
`U`. -/
theorem Over.pullbackSectionsMapOfIsSubterminal_naturality
    {X Y : Over (yoneda.obj Z : Cᵒᵖ ⥤ Type v)}
    (m : (Over.pullback (yoneda.map j)).obj X ⟶ (Over.pullback (yoneda.map j)).obj Y) {T T' : C}
    (g : T' ⟶ T) (hT : Nonempty (T ⟶ U)) (hT' : Nonempty (T' ⟶ U)) (x : X.left.obj (op T)) :
    Y.left.map g.op (Over.pullbackSectionsMapOfIsSubterminal hZ j hU m hT x) =
      Over.pullbackSectionsMapOfIsSubterminal hZ j hU m hT' (X.left.map g.op x) := by
  obtain ⟨z, hz⟩ := (Over.pullbackSectionsEquivOfIsSubterminal hZ j hU X hT).surjective x
  rw [Over.pullbackSectionsEquivOfIsSubterminal_apply] at hz
  subst hz
  rw [Over.pullbackSectionsMapOfIsSubterminal_fst,
    ← NatTrans.naturality_apply (pullback.fst X.hom (yoneda.map j)) g.op,
    Over.pullbackSectionsMapOfIsSubterminal_fst]
  exact (NatTrans.naturality_apply (pullback.fst Y.hom (yoneda.map j)) g.op _).symm.trans
    (congrArg (fun w => (pullback.fst Y.hom (yoneda.map j)).app (op T') w)
      (NatTrans.naturality_apply m.left g.op z).symm)

/-- **A pair of base-changed morphisms commuting with the comparison isomorphism of a square
induces the same map on sections over an object lying over `V`.** This is
`CategoryTheory.Over.pullbackSectionsMap_eq_of_comm` over a subterminal base. -/
theorem Over.pullbackSectionsMapOfIsSubterminal_eq_of_comm {W V : C} {jU : U ⟶ Z} {jW : W ⟶ Z}
    {iU : V ⟶ U} {iW : V ⟶ W} (hW : IsSubterminal W) (hVs : IsSubterminal V)
    (w : yoneda.map iU ≫ yoneda.map jU = yoneda.map iW ≫ yoneda.map jW)
    {X Y : Over (yoneda.obj Z : Cᵒᵖ ⥤ Type v)}
    {mU : (Over.pullback (yoneda.map jU)).obj X ⟶ (Over.pullback (yoneda.map jU)).obj Y}
    {mW : (Over.pullback (yoneda.map jW)).obj X ⟶ (Over.pullback (yoneda.map jW)).obj Y}
    (hcomm : (Over.pullback (yoneda.map iU)).map mU ≫ (Over.pullbackSquareObjIso w Y).hom =
      (Over.pullbackSquareObjIso w X).hom ≫ (Over.pullback (yoneda.map iW)).map mW)
    {T : C} (p : T ⟶ V) (x : X.left.obj (op T)) :
    Over.pullbackSectionsMapOfIsSubterminal hZ jU hU mU ⟨p ≫ iU⟩ x =
      Over.pullbackSectionsMapOfIsSubterminal hZ jW hW mW ⟨p ≫ iW⟩ x := by
  obtain ⟨z, hz⟩ := (bijective_pullback_fst_app jU hZ hU X (p ≫ iU)).surjective x
  have hb : Function.Bijective
      ((pullback.fst (pullback.snd X.hom (yoneda.map jU)) (yoneda.map iU)).app (op T)) :=
    bijective_pullback_fst_app iU hU hVs ((Over.pullback (yoneda.map jU)).obj X) p
  obtain ⟨r, hr⟩ := hb.surjective z
  have hsq := ConcreteCategory.congr_hom (NatTrans.congr_app
    (Over.pullbackSquareObjIso_hom_left_fst w X) (op T)) r
  have hmU := ConcreteCategory.congr_hom (NatTrans.congr_app
    (Over.pullback_map_left_comp_fst (yoneda.map iU) mU) (op T)) r
  have hmW := ConcreteCategory.congr_hom (NatTrans.congr_app
    (Over.pullback_map_left_comp_fst (yoneda.map iW) mW) (op T))
    ((Over.pullbackSquareObjIso w X).hom.left.app (op T) r)
  have hkey := ConcreteCategory.congr_hom (NatTrans.congr_app
    (Over.pullbackSquare_map_left_fst w hcomm) (op T)) r
  simp only [NatTrans.comp_app, types_comp_apply, Over.pullback_obj_hom] at hsq hmU hmW hkey
  rw [← hz, ← hr, Over.pullbackSectionsMapOfIsSubterminal_fst, ← hsq,
    Over.pullbackSectionsMapOfIsSubterminal_fst, ← hmU, ← hmW]
  exact hkey

end PullbackSections

end CategoryTheory

namespace AlgebraicGeometry.FinitePresentationSpacesOver

attribute [local instance] BigFppfOver.hasSheafify_type

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z U W V : BigFppfOver B S hS} (hZ : IsSubterminal Z) (hU : IsSubterminal U)
  (hW : IsSubterminal W) {jU : U ⟶ Z} {jW : W ⟶ Z} {iU : V ⟶ U} {iW : V ⟶ W}
  (hV : IsPullback iU iW jU jW)
  (hcov : Sieve.ofTwoArrows jU jW ∈ BigFppfOver.topology B S hS Z)

/-! ### Glueing sections over an object lying over a subterminal base -/

section Glue

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) {T : BigFppfOver B S hS}
  (hT : Nonempty (T ⟶ Z))

include hZ hU hW hV hcov hF hT in
/-- **The sheaf condition at the square `V ⨯ T, U ⨯ T, W ⨯ T, T` for an object `T` admitting a
morphism to a subterminal base.** This is the sheaf condition of
`AlgebraicGeometry.FinitePresentationSpacesOver.mayerVietorisSquareOfHom`, stated so that the
chosen morphism `T ⟶ Z` does not appear: only its existence matters, and over a terminal base
it is automatic. -/
theorem isPullback_sections_prodSquare :
    IsPullback (F.map (prod.snd : U ⨯ T ⟶ T).op) (F.map (prod.snd : W ⨯ T ⟶ T).op)
      (F.map (prod.map iU (𝟙 T)).op) (F.map (prod.map iW (𝟙 T)).op) :=
  hT.elim fun p => sheafCondition_mayerVietorisSquareOfHom B S hS hZ hU hW hV hcov p hF

include hZ hU hW hV hcov hF hT in
/-- **A section of an fppf sheaf over an object `T` lying over the subterminal base is
determined by its restrictions to `U ⨯ T` and to `W ⨯ T`.** This is
`AlgebraicGeometry.FinitePresentationSpacesOver.sheafSection_ext_prod` over a subterminal
base. -/
theorem sheafSection_ext_prod_of_hom {x y : F.obj (op T)}
    (hxyU : F.map (prod.snd : U ⨯ T ⟶ T).op x = F.map (prod.snd : U ⨯ T ⟶ T).op y)
    (hxyW : F.map (prod.snd : W ⨯ T ⟶ T).op x = F.map (prod.snd : W ⨯ T ⟶ T).op y) : x = y :=
  Types.ext_of_isPullback
    (isPullback_sections_prodSquare B S hS hZ hU hW hV hcov hF hT) hxyU hxyW

include hZ hU hW hV hcov hF hT in
/-- **Two sections of an fppf sheaf over `U ⨯ T` and over `W ⨯ T` which agree over `V ⨯ T` glue
to a section over `T`**, for `T` lying over the subterminal base. This is
`AlgebraicGeometry.FinitePresentationSpacesOver.glueProd` over a subterminal base. -/
noncomputable def glueProdOfHom (a : F.obj (op (U ⨯ T))) (b : F.obj (op (W ⨯ T)))
    (hab : F.map (prod.map iU (𝟙 T)).op a = F.map (prod.map iW (𝟙 T)).op b) : F.obj (op T) :=
  (PullbackCone.IsLimit.equivPullbackObj
    (isPullback_sections_prodSquare B S hS hZ hU hW hV hcov hF hT).isLimit).symm ⟨⟨a, b⟩, hab⟩

include hZ hU hW hV hcov hF hT in
/-- The restriction to `U ⨯ T` of a glued section is the first of the two sections glued. -/
@[simp]
theorem map_prod_snd_op_glueProdOfHom_left (a : F.obj (op (U ⨯ T))) (b : F.obj (op (W ⨯ T)))
    (hab : F.map (prod.map iU (𝟙 T)).op a = F.map (prod.map iW (𝟙 T)).op b) :
    F.map (prod.snd : U ⨯ T ⟶ T).op
        (glueProdOfHom B S hS hZ hU hW hV hcov hF hT a b hab) = a :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst
    (isPullback_sections_prodSquare B S hS hZ hU hW hV hcov hF hT).isLimit _

include hZ hU hW hV hcov hF hT in
/-- The restriction to `W ⨯ T` of a glued section is the second of the two sections glued. -/
@[simp]
theorem map_prod_snd_op_glueProdOfHom_right (a : F.obj (op (U ⨯ T))) (b : F.obj (op (W ⨯ T)))
    (hab : F.map (prod.map iU (𝟙 T)).op a = F.map (prod.map iW (𝟙 T)).op b) :
    F.map (prod.snd : W ⨯ T ⟶ T).op
        (glueProdOfHom B S hS hZ hU hW hV hcov hF hT a b hab) = b :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd
    (isPullback_sections_prodSquare B S hS hZ hU hW hV hcov hF hT).isLimit _

end Glue

/-! ### Fullness of the comparison functor over a subterminal base -/

section Full

variable {X Y : Over (yoneda.obj Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
  (mU : (Over.pullback (yoneda.map jU)).obj X ⟶ (Over.pullback (yoneda.map jU)).obj Y)
  (mW : (Over.pullback (yoneda.map jW)).obj X ⟶ (Over.pullback (yoneda.map jW)).obj Y)

/-- The section of `Y` over `U' ⨯ T` attached to a section of `X` over `T` by a base change to
a subterminal `U'` is natural in `T`. This is
`AlgebraicGeometry.FinitePresentationSpacesOver.pullbackSectionsMap_prod_naturality` over a
subterminal base. -/
theorem pullbackSectionsMapOfIsSubterminal_prod_naturality {U' : BigFppfOver B S hS}
    (jU' : U' ⟶ Z) (hU' : IsSubterminal U')
    (m : (Over.pullback (yoneda.map jU')).obj X ⟶ (Over.pullback (yoneda.map jU')).obj Y)
    {T T' : (BigFppfOver B S hS)ᵒᵖ} (g : T ⟶ T') (x : X.left.obj T) :
    Y.left.map (prod.map (𝟙 U') g.unop).op
        (Over.pullbackSectionsMapOfIsSubterminal hZ jU' hU' m ⟨prod.fst⟩
          (X.left.map (prod.snd : U' ⨯ T.unop ⟶ T.unop).op x)) =
      Over.pullbackSectionsMapOfIsSubterminal hZ jU' hU' m ⟨prod.fst⟩
        (X.left.map (prod.snd : U' ⨯ T'.unop ⟶ T'.unop).op (X.left.map g x)) := by
  rw [Over.pullbackSectionsMapOfIsSubterminal_naturality hZ jU' hU' m
      (prod.map (𝟙 U') g.unop) ⟨prod.fst⟩ ⟨prod.fst⟩,
    map_prod_snd_op_comp B S hS X.left g x]

include hZ hU hW hV in
/-- **Two compatible base changes of a morphism of presheaves over a subterminal base agree
over `V ⨯ T`.** This is
`AlgebraicGeometry.FinitePresentationSpacesOver.pullbackSectionsMap_restrict_eq` over a
subterminal base. -/
theorem pullbackSectionsMapOfIsSubterminal_restrict_eq
    (hcomm : (Over.pullback (yoneda.map iU)).map mU ≫
        (Over.pullbackSquareObjIso (yoneda_map_comm hV.w) Y).hom =
      (Over.pullbackSquareObjIso (yoneda_map_comm hV.w) X).hom ≫
        (Over.pullback (yoneda.map iW)).map mW)
    (T : BigFppfOver B S hS) (x : X.left.obj (op T)) :
    Y.left.map (prod.map iU (𝟙 T)).op
        (Over.pullbackSectionsMapOfIsSubterminal hZ jU hU mU ⟨prod.fst⟩
          (X.left.map (prod.snd : U ⨯ T ⟶ T).op x)) =
      Y.left.map (prod.map iW (𝟙 T)).op
        (Over.pullbackSectionsMapOfIsSubterminal hZ jW hW mW ⟨prod.fst⟩
          (X.left.map (prod.snd : W ⨯ T ⟶ T).op x)) := by
  have hres : ∀ {U' : BigFppfOver B S hS} (f : V ⟶ U'),
      X.left.map (prod.map f (𝟙 T)).op (X.left.map (prod.snd : U' ⨯ T ⟶ T).op x) =
        X.left.map (prod.snd : V ⨯ T ⟶ T).op x := by
    intro U' f
    have h : prod.map f (𝟙 T) ≫ (prod.snd : U' ⨯ T ⟶ T) = (prod.snd : V ⨯ T ⟶ T) := by simp
    simp only [← Functor.map_comp_apply, ← op_comp, h]
  rw [Over.pullbackSectionsMapOfIsSubterminal_naturality hZ jU hU mU
      (prod.map iU (𝟙 T)) ⟨prod.fst⟩ ⟨(prod.fst : V ⨯ T ⟶ V) ≫ iU⟩,
    Over.pullbackSectionsMapOfIsSubterminal_naturality hZ jW hW mW
      (prod.map iW (𝟙 T)) ⟨prod.fst⟩ ⟨(prod.fst : V ⨯ T ⟶ V) ≫ iW⟩,
    hres iU, hres iW]
  exact Over.pullbackSectionsMapOfIsSubterminal_eq_of_comm hZ hU hW (hV.isSubterminal hU hW)
    (yoneda_map_comm hV.w) hcomm prod.fst _

variable (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y.left)
  (hcomm : (Over.pullback (yoneda.map iU)).map mU ≫
      (Over.pullbackSquareObjIso (yoneda_map_comm hV.w) Y).hom =
    (Over.pullbackSquareObjIso (yoneda_map_comm hV.w) X).hom ≫
      (Over.pullback (yoneda.map iW)).map mW)

include hZ hU hW hV hcov hY hcomm in
/-- **The morphism of presheaves over a subterminal base glued from two compatible base-changed
morphisms.** Over `U ⨯ T` it is the first datum and over `W ⨯ T` the second; they agree over
`V ⨯ T`, so the sheaf condition at the Mayer--Vietoris square of `T` glues them.

The Mayer--Vietoris square of `T` exists because the section being glued supplies, through the
structure morphism of `X`, a morphism `T ⟶ Z`. This is
`AlgebraicGeometry.FinitePresentationSpacesOver.glueingFullHom` over a subterminal base. -/
noncomputable def glueingFullHomOfIsSubterminal : X.left ⟶ Y.left where
  app T := ↾fun x =>
    glueProdOfHom B S hS hZ hU hW hV hcov hY ⟨(X.hom.app T x : T.unop ⟶ Z)⟩
      (Over.pullbackSectionsMapOfIsSubterminal hZ jU hU mU ⟨prod.fst⟩
        (X.left.map (prod.snd : U ⨯ T.unop ⟶ T.unop).op x))
      (Over.pullbackSectionsMapOfIsSubterminal hZ jW hW mW ⟨prod.fst⟩
        (X.left.map (prod.snd : W ⨯ T.unop ⟶ T.unop).op x))
      (pullbackSectionsMapOfIsSubterminal_restrict_eq B S hS hZ hU hW hV mU mW hcomm T.unop x)
  naturality T T' g := ConcreteCategory.hom_ext _ _ fun x => by
    simp only [types_comp_apply, TypeCat.ofHom_apply]
    refine sheafSection_ext_prod_of_hom B S hS hZ hU hW hV hcov hY
      ⟨(X.hom.app T' (X.left.map g x) : T'.unop ⟶ Z)⟩ ?_ ?_
    · rw [map_prod_snd_op_glueProdOfHom_left, map_prod_snd_op_comp B S hS Y.left g,
        map_prod_snd_op_glueProdOfHom_left,
        pullbackSectionsMapOfIsSubterminal_prod_naturality B S hS hZ jU hU mU g x]
    · rw [map_prod_snd_op_glueProdOfHom_right, map_prod_snd_op_comp B S hS Y.left g,
        map_prod_snd_op_glueProdOfHom_right,
        pullbackSectionsMapOfIsSubterminal_prod_naturality B S hS hZ jW hW mW g x]

include hZ hU hW hV hcov hY hcomm in
/-- The glued morphism is, on sections, the glueing of the two base-changed data. -/
theorem glueingFullHomOfIsSubterminal_app_apply (T : (BigFppfOver B S hS)ᵒᵖ)
    (x : X.left.obj T) :
    (glueingFullHomOfIsSubterminal B S hS hZ hU hW hV hcov mU mW hY hcomm).app T x =
      glueProdOfHom B S hS hZ hU hW hV hcov hY ⟨(X.hom.app T x : T.unop ⟶ Z)⟩
        (Over.pullbackSectionsMapOfIsSubterminal hZ jU hU mU ⟨prod.fst⟩
          (X.left.map (prod.snd : U ⨯ T.unop ⟶ T.unop).op x))
        (Over.pullbackSectionsMapOfIsSubterminal hZ jW hW mW ⟨prod.fst⟩
          (X.left.map (prod.snd : W ⨯ T.unop ⟶ T.unop).op x))
        (pullbackSectionsMapOfIsSubterminal_restrict_eq B S hS hZ hU hW hV mU mW hcomm T.unop
          x) :=
  rfl

include hZ hU hW hV hcov hY hcomm in
/-- **Over an object lying over `U` the glued morphism is the first datum.** -/
theorem glueingFullHomOfIsSubterminal_app_eq_left (T : (BigFppfOver B S hS)ᵒᵖ)
    (hT : Nonempty (T.unop ⟶ U)) (x : X.left.obj T) :
    (glueingFullHomOfIsSubterminal B S hS hZ hU hW hV hcov mU mW hY hcomm).app T x =
      Over.pullbackSectionsMapOfIsSubterminal hZ jU hU mU hT x := by
  obtain ⟨q⟩ := hT
  refine sheafSection_ext_prod_of_hom B S hS hZ hU hW hV hcov hY ⟨q ≫ jU⟩ ?_ ?_
  · rw [glueingFullHomOfIsSubterminal_app_apply, map_prod_snd_op_glueProdOfHom_left,
      Over.pullbackSectionsMapOfIsSubterminal_naturality hZ jU hU mU
        (prod.snd : U ⨯ T.unop ⟶ T.unop) ⟨q⟩ ⟨prod.fst⟩]
  · rw [glueingFullHomOfIsSubterminal_app_apply, map_prod_snd_op_glueProdOfHom_right,
      Over.pullbackSectionsMapOfIsSubterminal_naturality hZ jU hU mU
        (prod.snd : W ⨯ T.unop ⟶ T.unop) ⟨q⟩ ⟨(prod.snd : W ⨯ T.unop ⟶ T.unop) ≫ q⟩]
    exact (Over.pullbackSectionsMapOfIsSubterminal_eq_of_comm hZ hU hW
      (hV.isSubterminal hU hW) (yoneda_map_comm hV.w) hcomm
      (hV.lift ((prod.snd : W ⨯ T.unop ⟶ T.unop) ≫ q) prod.fst (hZ _ _)) _).symm

include hZ hU hW hV hcov hY hcomm in
/-- **Over an object lying over `W` the glued morphism is the second datum.** -/
theorem glueingFullHomOfIsSubterminal_app_eq_right (T : (BigFppfOver B S hS)ᵒᵖ)
    (hT : Nonempty (T.unop ⟶ W)) (x : X.left.obj T) :
    (glueingFullHomOfIsSubterminal B S hS hZ hU hW hV hcov mU mW hY hcomm).app T x =
      Over.pullbackSectionsMapOfIsSubterminal hZ jW hW mW hT x := by
  obtain ⟨q⟩ := hT
  refine sheafSection_ext_prod_of_hom B S hS hZ hU hW hV hcov hY ⟨q ≫ jW⟩ ?_ ?_
  · rw [glueingFullHomOfIsSubterminal_app_apply, map_prod_snd_op_glueProdOfHom_left,
      Over.pullbackSectionsMapOfIsSubterminal_naturality hZ jW hW mW
        (prod.snd : U ⨯ T.unop ⟶ T.unop) ⟨q⟩ ⟨(prod.snd : U ⨯ T.unop ⟶ T.unop) ≫ q⟩]
    exact Over.pullbackSectionsMapOfIsSubterminal_eq_of_comm hZ hU hW
      (hV.isSubterminal hU hW) (yoneda_map_comm hV.w) hcomm
      (hV.lift prod.fst ((prod.snd : U ⨯ T.unop ⟶ T.unop) ≫ q) (hZ _ _)) _
  · rw [glueingFullHomOfIsSubterminal_app_apply, map_prod_snd_op_glueProdOfHom_right,
      Over.pullbackSectionsMapOfIsSubterminal_naturality hZ jW hW mW
        (prod.snd : W ⨯ T.unop ⟶ T.unop) ⟨q⟩ ⟨prod.fst⟩]

include hZ hU hW hV hcov hY hcomm in
/-- The glued morphism, as a morphism of the slice over the representable presheaf of a
subterminal base: the compatibility is automatic, that presheaf being subterminal by
`CategoryTheory.IsSubterminal.yonedaObj`. -/
noncomputable def glueingFullOverHomOfIsSubterminal : X ⟶ Y :=
  Over.homMk (glueingFullHomOfIsSubterminal B S hS hZ hU hW hV hcov mU mW hY hcomm)
    (hZ.yonedaObj _ _)

include hZ hU hW hV hcov hY hcomm in
/-- **The base change to `U` of the glued morphism is the first datum.** -/
theorem pullback_map_glueingFullOverHomOfIsSubterminal_left :
    (Over.pullback (yoneda.map jU)).map
        (glueingFullOverHomOfIsSubterminal B S hS hZ hU hW hV hcov mU mW hY hcomm) = mU :=
  pullback_map_eq_of_forall_app_eq hZ jU hU _ _ fun T hT x =>
    glueingFullHomOfIsSubterminal_app_eq_left B S hS hZ hU hW hV hcov mU mW hY hcomm T hT x

include hZ hU hW hV hcov hY hcomm in
/-- **The base change to `W` of the glued morphism is the second datum.** -/
theorem pullback_map_glueingFullOverHomOfIsSubterminal_right :
    (Over.pullback (yoneda.map jW)).map
        (glueingFullOverHomOfIsSubterminal B S hS hZ hU hW hV hcov mU mW hY hcomm) = mW :=
  pullback_map_eq_of_forall_app_eq hZ jW hW _ _ fun T hT x =>
    glueingFullHomOfIsSubterminal_app_eq_right B S hS hZ hU hW hV hcov mU mW hY hcomm T hT x

end Full

include hZ hU hW hV hcov in
/-- **The comparison functor into the `2`-fibre product is full over a subterminal base.** A
morphism of the `2`-fibre product is a pair of morphisms of the base changes to `U` and to `W`
agreeing over `V`; the sheaf condition at the Mayer--Vietoris squares of the objects lying over
the base glues them to a morphism over the base, whose two base changes are the given pair.

This is `AlgebraicGeometry.FinitePresentationSpacesOver.full_glueingFunctor` with terminality of
the base weakened to subterminality, which is what Stacks 0E91 needs at a stage `Z i = U ∪ W i`.
-/
theorem full_glueingFunctor_of_isSubterminal : (glueingFunctor B S hS hV.w).Full where
  map_surjective {F G} m := by
    have hw : (Over.pullback (yoneda.map iU)).map
          ((ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS U)).map m.hom.left) ≫
          (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS V)).map
            ((baseChangeSquareIso B S hS hV.w).hom.app G) =
        (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS V)).map
            ((baseChangeSquareIso B S hS hV.w).hom.app F) ≫
          (Over.pullback (yoneda.map iW)).map
            ((ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS W)).map m.hom.right) :=
      (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS V)).congr_map m.hom.w
    rw [baseChangeSquareIso_hom_app_left, baseChangeSquareIso_hom_app_left,
      Over.pullbackSquareIso_hom_app, Over.pullbackSquareIso_hom_app] at hw
    refine ⟨ObjectProperty.homMk (glueingFullOverHomOfIsSubterminal B S hS hZ hU hW hV hcov
      ((ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS U)).map m.hom.left)
      ((ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS W)).map m.hom.right)
      G.property.1.isSheaf hw), ?_⟩
    refine ObjectProperty.hom_ext _ (Comma.hom_ext _ _ ?_ ?_)
    · rw [glueingFunctor_map_hom_left]
      refine (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS U)).map_injective ?_
      rw [ι_map_baseChange_map]
      exact pullback_map_glueingFullOverHomOfIsSubterminal_left B S hS hZ hU hW hV hcov _ _
        G.property.1.isSheaf hw
    · rw [glueingFunctor_map_hom_right]
      refine (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS W)).map_injective ?_
      rw [ι_map_baseChange_map]
      exact pullback_map_glueingFullOverHomOfIsSubterminal_right B S hS hZ hU hW hV hcov _ _
        G.property.1.isSheaf hw

end AlgebraicGeometry.FinitePresentationSpacesOver

end
