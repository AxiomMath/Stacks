module

public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsAlongAFunctor

/-!
# Sections of the direct image along a cocontinuous functor, and its derived functor

Let `w : C ⥤ D` be a cocontinuous functor of sites. The direct image `w_s` of abelian sheaves
along `w` is right Kan extension along `w.op`, and its sections over an object `V` of `D` are
corepresented by the free abelian sheaf `ℤ[w^p h_V]^#` on the restriction along `w` of the
representable presheaf of `V`: this is the composite of the free-abelian-sheaf adjunction, of the
adjunction between restriction along `w.op` and right Kan extension along it, and of the Yoneda
lemma. Here this is done at independent universes for the two sites, the coefficients being in a
universe containing all four, which is the generality the sites of algebraic stacks need: there
the objects live in `Type (u + 1)`, the morphisms in `Type u` and the coefficients in
`AddCommGrpCat.{u + 1}`.

Consequently the unit of a right derived functor of `w_s` is invertible at a complex `Z` of
abelian sheaves on `C` as soon as the localization map on homotopy classes of morphisms out of
each `ℤ[w^p h_V]^#`, placed in degree `0`, into each shift of `Z` is bijective: `Z` then computes
`R w_s`, whether or not it is K-injective.

## Main definitions

* `Stacks.Cohomology.CocontinuousPushforwardCorep.pushforwardCorep`: the sheaf
  `ℤ[w^p h_V]^#`.
* `Stacks.Cohomology.CocontinuousPushforwardCorep.pushforwardCorepRepresentation`: sections over
  `V` of `w_s` are corepresented by it.

## Main results

* `Stacks.Cohomology.CocontinuousPushforwardCorep.quasiIso_of_quasiIso_sheafToPresheaf`: a
  morphism of complexes of abelian sheaves is a quasi-isomorphism when its underlying morphism of
  complexes of presheaves is.
* `Stacks.Cohomology.CocontinuousPushforwardCorep.isIso_rightDerivedUnit_of_qh_bijective`: the
  criterion above for the unit of a right derived functor of `w_s`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ u₁ v₂ u₂ v₃ u₃ t₁ t₂

namespace Stacks.Cohomology.CocontinuousPushforwardCorep

section QuasiIso

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]

/-- **Quasi-isomorphy of a morphism of complexes of abelian sheaves can be checked on the
underlying complexes of presheaves**: sheafification is exact and its composite with the
inclusion of sheaves is the identity. -/
lemma quasiIso_of_quasiIso_sheafToPresheaf
    {K L : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ} (f : K ⟶ L)
    (hf : QuasiIso (((sheafToPresheaf J AddCommGrpCat.{w}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f)) : QuasiIso f := by
  let F := sheafToPresheaf J AddCommGrpCat.{w}
  let G := presheafToSheaf J AddCommGrpCat.{w}
  let c := ComplexShape.up ℤ
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  let e : F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c ≅
      𝟭 (CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) :=
    Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c ≪≫
      NatIso.mapHomologicalComplex (sheafificationNatIso J AddCommGrpCat.{w}).symm c ≪≫
      Functor.mapHomologicalComplexIdIso _ c
  let sf := (G.mapHomologicalComplex c).map ((F.mapHomologicalComplex c).map f)
  have hsf : QuasiIso sf :=
    HomologicalComplex.quasiIso_map_of_preservesHomology
      ((F.mapHomologicalComplex c).map f) G
  exact quasiIso_of_arrow_mk_iso sf f
    (Arrow.isoMk (e.app K) (e.app L) (by simpa [sf] using (e.hom.naturality f).symm))

end QuasiIso

section Yoneda

variable {D : Type u₂} [Category.{v₂} D]

set_option linter.checkUnivs false in
/-- Morphisms from the free abelian presheaf on a representable presheaf are sections, at
independent universes. -/
def freeUliftYonedaHomAddEquiv (V : D) (F : Dᵒᵖ ⥤ AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}) :
    ((uliftYoneda.{max u₁ u₂ v₁ w}.obj V ⋙ AddCommGrpCat.free) ⟶ F) ≃+ F.obj (op V) :=
  let e := ((AddCommGrpCat.adj.whiskerRight Dᵒᵖ).homEquiv
      (uliftYoneda.{max u₁ u₂ v₁ w}.obj V) F).trans
    (uliftYonedaEquiv.{max u₁ u₂ v₁ w} (F := F ⋙ forget AddCommGrpCat))
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := fun _ _ => rfl }

end Yoneda

section Corepresentation

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (w : C ⥤ D)
  [w.IsCocontinuous J K]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ u₂ v₁ v₂ w},
    w.op.HasPointwiseRightKanExtension G]
  [HasSheafify J AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}]

/-- **The sheaf corepresenting sections over `V` of the direct image along a cocontinuous
functor**: the free abelian sheaf on the restriction along `w` of the representable presheaf of
`V`, whose sections over `W` are, before sheafification, the free abelian group on
`w(W) ⟶ V`. -/
abbrev pushforwardCorep (V : D) : Sheaf J AddCommGrpCat.{max u₁ u₂ v₁ v₂ w} :=
  (Presheaf.freeAbelianSheaf.{max u₁ u₂ v₁ v₂ w} J).obj
    (w.op ⋙ uliftYoneda.{max u₁ u₂ v₁ w}.obj V)

/-- Morphisms out of `pushforwardCorep` are the sections over `V` of the direct image along a
cocontinuous functor: the composite of the sheafification adjunction, of the adjunction between
restriction along `w.op` and right Kan extension along it, and of
`freeUliftYonedaHomAddEquiv`. -/
def pushforwardCorepHomAddEquiv (V : D) (F : Sheaf J AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}) :
    (pushforwardCorep J w V ⟶ F) ≃+
      ((w.sheafPushforwardCocontinuous AddCommGrpCat.{max u₁ u₂ v₁ v₂ w} J K).obj F).obj.obj
        (op V) :=
  ((sheafificationAdjunction J AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}).homAddEquiv
      (w.op ⋙ uliftYoneda.{max u₁ u₂ v₁ w}.obj V ⋙ AddCommGrpCat.free) F).trans
    (((w.op.ranAdjunction AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}).homAddEquiv
        (uliftYoneda.{max u₁ u₂ v₁ w}.obj V ⋙ AddCommGrpCat.free) F.obj).trans
      (freeUliftYonedaHomAddEquiv.{w, v₁, u₁, v₂, u₂} V (w.op.ran.obj F.obj)))

/-- The bijection `pushforwardCorepHomAddEquiv` is natural in the sheaf. -/
lemma pushforwardCorepHomAddEquiv_naturality (V : D)
    {F G : Sheaf J AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}} (β : F ⟶ G)
    (x : (preadditiveCoyoneda.obj (op (pushforwardCorep J w V))).obj F) :
    pushforwardCorepHomAddEquiv J K w V G
        ((preadditiveCoyoneda.obj (op (pushforwardCorep J w V))).map β x) =
      (((w.sheafPushforwardCocontinuous AddCommGrpCat.{max u₁ u₂ v₁ v₂ w} J K).map β).hom.app
        (op V)) (pushforwardCorepHomAddEquiv J K w V F x) := by
  have h1 :=
    (sheafificationAdjunction J AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}).homEquiv_naturality_right
    (X := w.op ⋙ uliftYoneda.{max u₁ u₂ v₁ w}.obj V ⋙ AddCommGrpCat.free) x β
  have h2 := (w.op.ranAdjunction AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}).homEquiv_naturality_right
    (X := uliftYoneda.{max u₁ u₂ v₁ w}.obj V ⋙ AddCommGrpCat.free)
    ((sheafificationAdjunction J AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}).homEquiv
      (w.op ⋙ uliftYoneda.{max u₁ u₂ v₁ w}.obj V ⋙ AddCommGrpCat.free) F x)
    ((sheafToPresheaf J AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}).map β)
  refine (congrArg (fun t => freeUliftYonedaHomAddEquiv.{w, v₁, u₁, v₂, u₂} V (w.op.ran.obj G.obj)
    ((w.op.ranAdjunction AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}).homEquiv
      (uliftYoneda.{max u₁ u₂ v₁ w}.obj V ⋙ AddCommGrpCat.free) G.obj t)) h1).trans ?_
  refine (congrArg (fun t => freeUliftYonedaHomAddEquiv.{w, v₁, u₁, v₂, u₂} V
    (w.op.ran.obj G.obj) t) h2).trans ?_
  rfl

/-- **Sections over `V` of the direct image along a cocontinuous functor are corepresented by
`pushforwardCorep`**, naturally in the sheaf. -/
def pushforwardCorepRepresentation (V : D) :
    w.sheafPushforwardCocontinuous AddCommGrpCat.{max u₁ u₂ v₁ v₂ w} J K ⋙
        (sheafSections K AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}).obj (op V) ≅
      preadditiveCoyoneda.obj (op (pushforwardCorep J w V)) := by
  refine (NatIso.ofComponents
    (fun F => (pushforwardCorepHomAddEquiv J K w V F).toAddCommGrpIso) fun β => ?_).symm
  ext x
  exact pushforwardCorepHomAddEquiv_naturality J K w V β x

end Corepresentation

section Derived

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (w : C ⥤ D)
  [w.IsCocontinuous J K]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ u₂ v₁ v₂ w},
    w.op.HasPointwiseRightKanExtension G]
  [HasSheafify J AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}]
  [HasSheafify K AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}]
  [IsGrothendieckAbelian.{max u₁ u₂ v₁ v₂ w} (Sheaf J AddCommGrpCat.{max u₁ u₂ v₁ v₂ w})]
  [(w.sheafPushforwardCocontinuous AddCommGrpCat.{max u₁ u₂ v₁ v₂ w} J K).Additive]
  [HasDerivedCategory.{t₁} (Sheaf J AddCommGrpCat.{max u₁ u₂ v₁ v₂ w})]
  [HasDerivedCategory.{t₂} (Sheaf K AddCommGrpCat.{max u₁ u₂ v₁ v₂ w})]
  {H : Type u₃} [Category.{v₃} H]

/-- **The unit of a right derived functor of the direct image along a cocontinuous functor is
invertible at a complex `Z` as soon as the localization map on homotopy classes out of each
corepresenting sheaf `ℤ[w^p h_V]^#`, placed in degree `0`, into each shift of `Z` is bijective.**

Let `Z ⟶ I` be a K-injective resolution. Quasi-isomorphy of `w_s(Z) ⟶ w_s(I)` is checked on the
underlying complexes of presheaves, hence object by object of `D`; sections over `V` of `w_s` are
corepresented by `ℤ[w^p h_V]^#`, so the corepresentable criterion
`Stacks.Cohomology.DerivedLowerShriek.quasiIso_mapHomologicalComplex_of_corepresentable` applies,
its input being the bijectivity of the localization maps into the shifts of `Z` and of `I`.

The two derived categories carry arbitrary `HasDerivedCategory` instances. -/
theorem isIso_rightDerivedUnit_of_qh_bijective
    (RF : DerivedCategory (Sheaf J AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}) ⥤
      DerivedCategory (Sheaf K AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}))
    (αF : (w.sheafPushforwardCocontinuous AddCommGrpCat.{max u₁ u₂ v₁ v₂ w} J K).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (Z : CochainComplex (Sheaf J AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}) ℤ)
    (hZ : ∀ (V : D) (n : ℤ), Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor _ 0).obj (pushforwardCorep J w V)) ⟶
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (Z⟦n⟧)) → _)) :
    IsIso (αF.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Z)) := by
  set A := Sheaf J AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}
  set Fs := w.sheafPushforwardCocontinuous AddCommGrpCat.{max u₁ u₂ v₁ v₂ w} J K
  let q := (Stacks.Injectives.kInjectiveResolutionInclusion A).app Z
  refine DerivedLowerShriek.rightDerivedUnit_isIso_of_quasiIso_resolution _ RF αF q ?_
  have hqi : QuasiIso ((Fs.mapHomologicalComplex (ComplexShape.up ℤ)).map q) := by
    apply quasiIso_of_quasiIso_sheafToPresheaf K
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro t
    have : ((sheafSections K AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}).obj t).Additive :=
      ⟨fun {_ _ _ _} => rfl⟩
    change QuasiIso (((Fs ⋙ (sheafSections K AddCommGrpCat.{max u₁ u₂ v₁ v₂ w}).obj t
      ).mapHomologicalComplex (ComplexShape.up ℤ)).map q)
    refine DerivedLowerShriek.quasiIso_mapHomologicalComplex_of_corepresentable
      _ _ (pushforwardCorepRepresentation J K w t.unop).symm q (fun n => ?_)
    have : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (q⟦n⟧'))) := by
      apply Localization.inverts DerivedCategory.Qh
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
      change QuasiIso ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) n).map q)
      infer_instance
    exact DerivedLowerShriek.bijective_postcomp_of_qh_bijective _ (hZ t.unop n)
      (CochainComplex.IsKInjective.Qh_map_bijective _
        (((Stacks.Injectives.kInjectiveResolutionFunctor A).obj Z)⟦n⟧))
  change IsIso (DerivedCategory.Qh.map ((Fs.mapHomotopyCategory (ComplexShape.up ℤ)).map
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q)))
  rw [Functor.mapHomotopyCategory_map]
  exact _root_.isIso_Qh_map_quotient_map_of_quasiIso _

end Derived

end Stacks.Cohomology.CocontinuousPushforwardCorep
