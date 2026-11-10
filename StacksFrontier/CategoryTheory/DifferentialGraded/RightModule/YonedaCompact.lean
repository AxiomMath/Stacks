module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.YonedaSum

/-!
# The representable right differential graded modules are compact

Let `C` be a differential graded category over a commutative ring `R` and let `B` be an object
of `C`. The functor corepresented by the representable module `h_B = C(-, B)` on the homotopy
category `K(Mod^dg(C))` preserves coproducts indexed by the universe of the morphism modules
of `C`:

`PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op h_B))`.

This is the hypothesis under which
`CategoryTheory.ObjectProperty.exists_isTriangulated_reflector_localizingClosure` produces the
exact reflector of step 1 of [Stacks, Tag 09LK], and it is supplied here verbatim for the
family of representables.

The content is `DGCategory.RightModule.bijective_cofanMap_coprodCofan`: the canonical map from
the direct sum of the morphism groups to the morphism group of the direct sum is bijective.
Given that, the degreewise direct sum — which is a coproduct in `K(Mod^dg(C)) by
`DGCategory.RightModule.isColimitCoprodCofan` — is carried to a coproduct of abelian groups,
and preservation of one colimit cocone of a diagram is preservation of them all.

## Main results

* `DGCategory.RightModule.preservesColimitsOfShape_discrete_coyoneda_yonedaObjK`: the
  corepresented functor preserves coproducts.
* `DGCategory.RightModule.isCompactObject_yonedaObjK`: `h_B` is a compact object of
  `K(Mod^dg(C))`.

## Universes

Everything here is indexed by one universe `v`, the universe of the morphism modules of `C`.
The morphism groups of `K(Mod^dg(C))` live in `max u v`, where `Type u` is the type of objects
of `C`, because a homogeneous morphism of modules is a family indexed by the objects of `C`.
So the coproducts preserved here, indexed by `Type v`, are exactly the ones the reflector
bridge asks for precisely when `max u v = v`, that is when `C` has no more objects than its
morphism modules have elements — for instance when `C` has one object, the case of a
differential graded algebra. For a `C` with more objects than that, the representables of this
file are compact for `Type v`-indexed coproducts and the bridge needs `Type (max u v)`-indexed
ones; the missing step is a universe lift of `h_B` into `RightModule.{max u v} C`, which is
not built here.

## Implementation notes

The colimit in `AddCommGrpCat` is exhibited directly with `Limits.Cofan.IsColimit.mk` rather
than through `Limits.sigmaComparison`, so that no coproduct of abelian groups has to be named:
the descent map is the inverse of the bijection of
`DGCategory.RightModule.bijective_cofanMap_coprodCofan` followed by the universal map out of a
direct sum.
-/

@[expose] public section

namespace DGCategory

universe v u r

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite DirectSum

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

namespace RightModule

attribute [local implicit_reducible] DGCategory.K

variable (B : C.Obj) {α : Type v} (M : α → (rightModuleCategory.{v} C).K) [DecidableEq α]

/-- The bijection of `DGCategory.RightModule.bijective_cofanMap_coprodCofan`, as an isomorphism
of additive groups. -/
noncomputable def coprodCofanAddEquiv :
    (⨁ a, (yonedaObjK B ⟶ M a)) ≃+ (yonedaObjK B ⟶ (coprodCofan M).pt) :=
  AddEquiv.ofBijective (cofanMap (yonedaObjK B) (coprodCofan M).inj)
    (bijective_cofanMap_coprodCofan B M)

/-- `DGCategory.RightModule.coprodCofanAddEquiv` sends the summand `g` at `a` to the composite
of `g` with the inclusion of the `a`-th summand. -/
@[simp] theorem coprodCofanAddEquiv_of (a : α) (g : yonedaObjK B ⟶ M a) :
    coprodCofanAddEquiv B M (DirectSum.of _ a g) = g ≫ (coprodCofan M).inj a :=
  cofanMap_of _ _ a g

/-- The value of the corepresented functor on the inclusion of a summand is composition with
that inclusion. -/
theorem coyoneda_map_coprodCofan_inj (a : α) (g : yonedaObjK B ⟶ M a) :
    (preadditiveCoyoneda.obj (op (yonedaObjK B))).map ((coprodCofan M).inj a) g =
      g ≫ (coprodCofan M).inj a :=
  rfl

variable (t : Cofan fun a => (preadditiveCoyoneda.obj (op (yonedaObjK B))).obj (M a))

/-- A component of a cofan of abelian groups under the corepresented functor, as an additive
map out of a morphism group. -/
noncomputable def coyonedaCofanInj (a : α) : (yonedaObjK B ⟶ M a) →+ t.pt :=
  ConcreteCategory.hom (C := AddCommGrpCat) (t.inj a)

omit [DecidableEq α] in
/-- `DGCategory.RightModule.coyonedaCofanInj` evaluates as the `a`-th inclusion of the cofan. -/
@[simp] theorem coyonedaCofanInj_apply (a : α) (g : yonedaObjK B ⟶ M a) :
    coyonedaCofanInj B M t a g = t.inj a g :=
  rfl

/-- The descent of a cofan of abelian groups through the direct-sum bijection: the inverse of
`DGCategory.RightModule.coprodCofanAddEquiv` followed by the universal map out of a direct
sum. -/
noncomputable def coyonedaCoprodDescHom :
    (yonedaObjK B ⟶ (coprodCofan M).pt) →+ t.pt :=
  (DirectSum.toAddMonoid (coyonedaCofanInj B M t)).comp
    (coprodCofanAddEquiv B M).symm.toAddMonoidHom

/-- `DGCategory.RightModule.coyonedaCoprodDescHom` sends `g` composed with the inclusion of the
`a`-th summand to the image of `g` under the `a`-th inclusion of the cofan. -/
theorem coyonedaCoprodDescHom_apply (a : α) (g : yonedaObjK B ⟶ M a) :
    coyonedaCoprodDescHom B M t (g ≫ (coprodCofan M).inj a) = t.inj a g :=
  (congrArg (DirectSum.toAddMonoid (coyonedaCofanInj B M t))
      ((coprodCofanAddEquiv B M).symm_apply_eq.2
        (coprodCofanAddEquiv_of B M a g).symm)).trans
    (DirectSum.toAddMonoid_of (coyonedaCofanInj B M t) a g)

/-- The descent of a cofan of abelian groups, as a morphism of `AddCommGrpCat`. -/
noncomputable def coyonedaCoprodDesc :
    (preadditiveCoyoneda.obj (op (yonedaObjK B))).obj (coprodCofan M).pt ⟶ t.pt :=
  ConcreteCategory.ofHom (C := AddCommGrpCat) (coyonedaCoprodDescHom B M t)

/-- `DGCategory.RightModule.coyonedaCoprodDesc` sends `g` composed with the inclusion of the
`a`-th summand to the image of `g` under the `a`-th inclusion of the cofan. -/
theorem coyonedaCoprodDesc_apply (a : α) (g : yonedaObjK B ⟶ M a) :
    coyonedaCoprodDesc B M t (g ≫ (coprodCofan M).inj a) = t.inj a g :=
  coyonedaCoprodDescHom_apply B M t a g

variable {t}

/-- The corepresented functor carries the direct-sum cofan to a colimit cofan of abelian
groups. -/
noncomputable def isColimitCoyonedaCoprodCofan :
    IsColimit (Cofan.mk ((preadditiveCoyoneda.obj (op (yonedaObjK B))).obj (coprodCofan M).pt)
        (fun a => (preadditiveCoyoneda.obj (op (yonedaObjK B))).map ((coprodCofan M).inj a)) :
      Cofan fun a => (preadditiveCoyoneda.obj (op (yonedaObjK B))).obj (M a)) := by
  refine Cofan.IsColimit.mk _ (coyonedaCoprodDesc B M) (fun t a => ?_) (fun t m hm => ?_)
  · exact ConcreteCategory.hom_ext (C := AddCommGrpCat) _ _ (coyonedaCoprodDesc_apply B M t a)
  · refine ConcreteCategory.hom_ext (C := AddCommGrpCat) _ _ fun y => ?_
    obtain ⟨x, rfl⟩ := (coprodCofanAddEquiv B M).surjective y
    have key : (ConcreteCategory.hom (C := AddCommGrpCat) m).comp
          (coprodCofanAddEquiv B M).toAddMonoidHom =
        (coyonedaCoprodDescHom B M t).comp (coprodCofanAddEquiv B M).toAddMonoidHom := by
      refine DirectSum.addHom_ext fun a g => ?_
      have he : (coprodCofanAddEquiv B M).toAddMonoidHom (DirectSum.of _ a g) =
          g ≫ (coprodCofan M).inj a := coprodCofanAddEquiv_of B M a g
      calc ((ConcreteCategory.hom (C := AddCommGrpCat) m).comp
              (coprodCofanAddEquiv B M).toAddMonoidHom) (DirectSum.of _ a g)
          = ConcreteCategory.hom (C := AddCommGrpCat) m (g ≫ (coprodCofan M).inj a) :=
            congrArg (ConcreteCategory.hom (C := AddCommGrpCat) m) he
        _ = t.inj a g := congrArg (fun φ => ConcreteCategory.hom (C := AddCommGrpCat) φ g) (hm a)
        _ = coyonedaCoprodDescHom B M t (g ≫ (coprodCofan M).inj a) :=
            (coyonedaCoprodDescHom_apply B M t a g).symm
        _ = ((coyonedaCoprodDescHom B M t).comp
              (coprodCofanAddEquiv B M).toAddMonoidHom) (DirectSum.of _ a g) :=
            congrArg (coyonedaCoprodDescHom B M t) he.symm
    exact DFunLike.congr_fun key x

omit [DecidableEq α] in
/-- The corepresented functor of a representable module preserves the coproduct of a family of
right differential graded modules. -/
theorem preservesColimit_discreteFunctor_coyoneda :
    PreservesColimit (Discrete.functor M) (preadditiveCoyoneda.obj (op (yonedaObjK B))) := by
  classical
  exact preservesColimit_of_preserves_colimit_cocone (isColimitCoprodCofan M)
    ((isColimitMapCoconeCofanMkEquiv (preadditiveCoyoneda.obj (op (yonedaObjK B))) M
      (coprodCofan M).inj).symm (isColimitCoyonedaCoprodCofan B M))

omit [DecidableEq α] in
/-- **The representable right differential graded module `h_B` is compact.** The functor it
corepresents on the homotopy category preserves coproducts indexed by the universe of the
morphism modules of `C`. This is the hypothesis of
`CategoryTheory.ObjectProperty.exists_isTriangulated_reflector_localizingClosure`. -/
theorem preservesColimitsOfShape_discrete_coyoneda_yonedaObjK :
    PreservesColimitsOfShape (Discrete α)
      (preadditiveCoyoneda.obj (op (yonedaObjK B))) := by
  classical
  constructor
  intro G
  have := preservesColimit_discreteFunctor_coyoneda B (G.obj ∘ Discrete.mk)
  exact preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

omit [DecidableEq α] in
/-- `h_B` is a compact object of the homotopy category of right differential graded
`C`-modules, in the sense of [Stacks, Tag 07LS]. -/
theorem isCompactObject_yonedaObjK :
    IsCompactObject.{v} (yonedaObjK B : (rightModuleCategory.{v} C).K) :=
  isCompactObject_of_preservesColimitsOfShape_preadditiveCoyoneda _
    fun I => preservesColimitsOfShape_discrete_coyoneda_yonedaObjK (α := I) B

end RightModule

end DGCategory

end
