module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundaryInertiaInvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalk
public import StacksFrontier.AlgebraicGeometry.ProEtale.BigSmall.AbelianSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundaryStalkFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparisonNaturality
public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The specialization map of `j_* F` at a boundary point

Let `j : U ⟶ S` be quasi-compact and quasi-separated, `s` a geometric point of `S` such that
`U ×_S Spec 𝒪^{sh}_{S,s}` is the spectrum of a field `K` (for a boundary point of a regular
curve, `K = K^{sh}`), `g : Spec K ⟶ U` the projection and `t̄` a geometric point of `Spec K`.
This file constructs the **specialization map**
```
(j_* F)_s ⟶ F_{g(t̄)}
```
as a natural transformation of functors of sheaves of sets on `U`: Stacks 03Q9 in degree zero
(the stalk of `j_* F` at `s` is the set of sections over `U ×_S Spec 𝒪^{sh}`), then sections over
`Spec K`, their germ at `t̄` (Stacks 04JM) and the stalk of an inverse image (Stacks 03Q1). It is
injective, and its image is the set of elements fixed by the maps of Tag 04FN along the images
in `U` of the automorphisms of `t̄` over `K`, i.e. the invariants of the image of inertia: this is
`H⁰_loc` of Weil II 1.8 as a subset of the stalk at a geometric generic point.

Because the map is natural, it is additive on sheaves of modules
(`AlgebraicGeometry.ProEtale.natural_map_add`): for a sheaf of `R`-modules `M` on `U` it is an
injective morphism of abelian groups `(j_* M)_s ⟶ M_{g(t̄)}`.

## Main definitions

* `Stacks.EtaleCohomology.directImageStalkIsoBaseChangeSections` — Stacks 03Q9 in degree zero
  as a natural isomorphism.
* `Stacks.EtaleCohomology.sheafΓGerm` — the germ of a global section over `Spec K`, natural.
* `Stacks.EtaleCohomology.directImageStalkToStalk` — the specialization map on sheaves of sets.
* `Stacks.EtaleCohomology.directImageStalkToStalkHom` — the specialization map on sheaves of
  modules, additive.
* `Stacks.EtaleCohomology.natTransAddHom` — a natural map of underlying sets between additive
  functors to abelian groups, as morphisms of abelian groups.

## Main results

* `Stacks.EtaleCohomology.directImageStalkToStalk_injective`,
  `Stacks.EtaleCohomology.mem_range_directImageStalkToStalk_iff` — injectivity and the image.
* `Stacks.EtaleCohomology.directImageStalkToStalkHom_injective` — injectivity for modules.

## Implementation notes

The kernel cannot check an `IsIso` instance of a library lemma against a component of a
whiskered composite built here (it unfolds the sheaf functors before `Functor.comp`); building
the composite as a natural isomorphism, with `asIso` of `NatIso.isIso_of_isIso_app` fed a
restated standalone lemma, avoids this.

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 04JM](https://stacks.math.columbia.edu/tag/04JM)
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (Weil II 1.8, `H⁰_loc`)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
  Stacks.ConstantSheaf

universe u v

namespace AlgebraicGeometry

open Opposite

section GlobalGerm

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The canonical point of `Spec Ω ⟶ Z` on the final étale object `Z` over `Z`. -/
def pointSmallEtaleIdElementOf {Z : Scheme.{u}} (s : Spec (.of Ω) ⟶ Z) :
    (pointSmallEtale s).fiber.obj (Scheme.Etale.mk (𝟙 Z)) :=
  CategoryTheory.Over.homMk s (Category.comp_id s)

/-- The lift of `s` to the final étale object is unique. -/
theorem eq_pointSmallEtaleIdElementOf {Z : Scheme.{u}} (s : Spec (.of Ω) ⟶ Z)
    (x : (pointSmallEtale s).fiber.obj (Scheme.Etale.mk (𝟙 Z))) :
    x = pointSmallEtaleIdElementOf s :=
  CategoryTheory.Over.OverMorphism.ext
    ((Category.comp_id x.left).symm.trans (CategoryTheory.Over.w x))

/-- The germ at `s` of a global section of a sheaf of sets on Mathlib's small étale site of `Z`,
natural in the sheaf. -/
def smallEtaleGlobalGerm {Z : Scheme.{u}} (s : Spec (.of Ω) ⟶ Z) :
    Sheaf.Γ (smallEtaleTopology Z) (Type (u + 1)) ⟶
      (pointSmallEtale s).sheafFiber (A := Type (u + 1)) where
  app G := (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) (Type (u + 1))
      (Stacks.EtaleCohomology.isTerminalEtaleMkId Z)).hom.app G ≫
    (pointSmallEtale s).toPresheafFiber (Scheme.Etale.mk (𝟙 Z)) (pointSmallEtaleIdElementOf s) G.obj
  naturality G G' f := by
    have h1 := (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) (Type (u + 1))
      (Stacks.EtaleCohomology.isTerminalEtaleMkId Z)).hom.naturality f
    have h2 := (pointSmallEtale s).toPresheafFiber_naturality f.hom (Scheme.Etale.mk (𝟙 Z))
      (pointSmallEtaleIdElementOf s)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h2.symm)))

/-- A morphism of geometric points fixes the germ of a global section. -/
theorem smallEtaleGlobalGerm_app_pointSmallEtaleHom {Z : Scheme.{u}} (s : Spec (.of Ω) ⟶ Z)
    (a : Spec (.of Ω) ⟶ Spec (.of Ω)) (ha : a ≫ s = s)
    (G : Sheaf (smallEtaleTopology Z) (Type (u + 1))) :
    (smallEtaleGlobalGerm s).app G ≫ (pointSmallEtaleHom s s a ha).sheafFiber.app G =
      (smallEtaleGlobalGerm s).app G := by
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  refine (toPresheafFiber_pointSmallEtaleHom s s a ha G.obj _ _).trans ?_
  rw [eq_pointSmallEtaleIdElementOf s ((Over.homMk a ha : Over.mk s ⟶ Over.mk s) ≫
    pointSmallEtaleIdElementOf s)]

end GlobalGerm

section StalkComparison

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- The stalk comparison of the two small étale sites for sheaves of sets: the stalk at `x` of
a sheaf on the bounded site, read on Mathlib's site, is its stalk at `x`. -/
def sheafEquivFunctorSheafFiberIso (x : GeometricPoint X) :
    (SmallEtale.sheafEquiv B X hX (Type (u + 1))).functor ⋙
        (pointSmallEtale x.hom).sheafFiber (A := Type (u + 1)) ≅
      (geometricPointSitePoint B X hX x).sheafFiber :=
  sheafFiberIsoOfAdjOfFiberIso (geometricPointSitePoint B X hX x) (pointSmallEtale x.hom)
    (SmallEtale.toEtaleSite B X hX) (toEtaleSiteFiberIso B X hX x)
    (SmallEtale.sheafEquiv B X hX (Type (u + 1))).toAdjunction

/-- **The stalk comparison of the two small étale sites, for sheaves of sets on Mathlib's
site**: the stalk at `x` of a sheaf on Mathlib's small étale site is the stalk at `x` of its
restriction to the bounded site. -/
def pointSmallEtaleSheafFiberIso (x : GeometricPoint X) :
    (pointSmallEtale x.hom).sheafFiber (A := Type (u + 1)) ≅
      (SmallEtale.sheafEquiv B X hX (Type (u + 1))).inverse ⋙
        (geometricPointSitePoint B X hX x).sheafFiber :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (SmallEtale.sheafEquiv B X hX (Type (u + 1))).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sheafEquivFunctorSheafFiberIso B X hX x)

private theorem isoChain_bridge_hom_app {𝒜 ℬ 𝒟 : Type*} [Category* 𝒜] [Category* ℬ]
    [Category* 𝒟] (Fib : 𝒜 ⥤ 𝒟) (I : 𝒜 ⥤ ℬ) (Fu : ℬ ⥤ 𝒜) (c : I ⋙ Fu ≅ 𝟭 𝒜)
    (Fib' : ℬ ⥤ 𝒟) (β : Fu ⋙ Fib ≅ Fib') (F : 𝒜) :
    ((Functor.leftUnitor Fib).symm ≪≫ Functor.isoWhiskerRight c.symm Fib ≪≫
        Functor.associator I Fu Fib ≪≫ Functor.isoWhiskerLeft I β).hom.app F =
      Fib.map (c.inv.app F) ≫ β.hom.app (I.obj F) := by
  simp

/-- The component of `pointSmallEtaleSheafFiberIso` at a sheaf `F` is the fiber of the inverse
counit at `F` followed by the component of `sheafEquivFunctorSheafFiberIso`. -/
theorem pointSmallEtaleSheafFiberIso_hom_app (x : GeometricPoint X)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (pointSmallEtaleSheafFiberIso B X hX x).hom.app F =
      (pointSmallEtale x.hom).sheafFiber.map
          ((SmallEtale.sheafEquiv B X hX (Type (u + 1))).counitIso.inv.app F) ≫
        (sheafEquivFunctorSheafFiberIso B X hX x).hom.app
          ((SmallEtale.sheafEquiv B X hX (Type (u + 1))).inverse.obj F) :=
  isoChain_bridge_hom_app _ _ _ _ _ _ F

/-- The germ formula for the stalk comparison: a germ on the bounded site goes to the germ, at
the same lift, of the corresponding section on Mathlib's site. -/
theorem toPresheafFiber_sheafEquivFunctorSheafFiberIso_inv (x : GeometricPoint X)
    (F : Sheaf (SmallEtale.topology B X hX) (Type (u + 1)))
    (U : SmallEtale B X hX) (y : (geometricPointFiber B X hX x).obj U) :
    (geometricPointSitePoint B X hX x).toPresheafFiber U y F.obj ≫
        (sheafEquivFunctorSheafFiberIso B X hX x).inv.app F =
      ((SmallEtale.sheafEquiv B X hX (Type (u + 1))).unit.app F).hom.app (op U) ≫
        (pointSmallEtale x.hom).toPresheafFiber ((SmallEtale.toEtaleSite B X hX).obj U)
          ((toEtaleSiteFiberIso B X hX x).inv.app U y)
          ((SmallEtale.sheafEquiv B X hX (Type (u + 1))).functor.obj F).obj :=
  (congrArg ((geometricPointSitePoint B X hX x).toPresheafFiber U y F.obj ≫ ·)
      (Category.id_comp _)).symm.trans
    (toPresheafFiber_sheafFiberIsoOfAdjOfFiberIso_inv (geometricPointSitePoint B X hX x)
      (pointSmallEtale x.hom) (SmallEtale.toEtaleSite B X hX)
      (SmallEtale.sheafEquiv B X hX (Type (u + 1))).toAdjunction
      (toEtaleSiteFiberIso B X hX x) F U y)

/-- **Naturality of the stalk comparison in the geometric point**, for sheaves of sets: the map
of Mathlib's stalks induced by a morphism of geometric points corresponds to the map of
Tag 04FN on the bounded site. -/
theorem sheafEquivFunctorSheafFiberIso_inv_naturality {x y : GeometricPoint X}
    (a : GeometricPoint.Hom x y) (F : Sheaf (SmallEtale.topology B X hX) (Type (u + 1))) :
    (sheafEquivFunctorSheafFiberIso B X hX y).inv.app F ≫
        (smallEtalePointHom X a).sheafFiber.app
          ((SmallEtale.sheafEquiv B X hX (Type (u + 1))).functor.obj F) =
      (geometricPointStalkMap B X hX a (Type (u + 1))).app F.obj ≫
        (sheafEquivFunctorSheafFiberIso B X hX x).inv.app F := by
  refine (geometricPointSitePoint B X hX y).presheafFiber_hom_ext (fun U z => ?_)
  let L := (SmallEtale.sheafEquiv B X hX (Type (u + 1))).functor
  let GU := (SmallEtale.toEtaleSite B X hX).obj U
  have h2 := (pointSmallEtale y.hom).toPresheafFiber_presheafFiberDesc
    (A := Type (u + 1)) (P := (L.obj F).obj)
    (fun V v => (pointSmallEtale x.hom).toPresheafFiber V
      ((smallEtalePointHom X a).hom.app V v) (L.obj F).obj) (by
        intro V W g v
        exact ((pointSmallEtale x.hom).toPresheafFiber_w g _ _).trans (by
          congr 1))
    GU ((toEtaleSiteFiberIso B X hX y).inv.app U z)
  have hl := (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (smallEtalePointHom X a).sheafFiber.app (L.obj F))
      (toPresheafFiber_sheafEquivFunctorSheafFiberIso_inv B X hX y F U z)).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h2)))
  have hr := (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (sheafEquivFunctorSheafFiberIso B X hX x).inv.app F)
      (colimit.ι_pre ((CategoryOfElements.π (geometricPointFiber B X hX x)).op ⋙
        F.obj) (neighborhoodFunctor B X hX a).op (op ⟨U, z⟩))).trans
    (toPresheafFiber_sheafEquivFunctorSheafFiberIso_inv B X hX x F U _))
  refine hl.trans (Eq.trans ?_ hr.symm)
  congr 2

/-- **Naturality of the stalk comparison in the geometric point**, for sheaves of sets on
Mathlib's site. -/
theorem pointSmallEtaleSheafFiberIso_hom_naturality {x y : GeometricPoint X}
    (a : GeometricPoint.Hom x y) (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (pointSmallEtaleSheafFiberIso B X hX y).hom.app F ≫
        (geometricPointStalkMap B X hX a (Type (u + 1))).app
          ((SmallEtale.sheafEquiv B X hX (Type (u + 1))).inverse.obj F).obj =
      (smallEtalePointHom X a).sheafFiber.app F ≫
        (pointSmallEtaleSheafFiberIso B X hX x).hom.app F := by
  let E := SmallEtale.sheafEquiv B X hX (Type (u + 1))
  have h1 := sheafEquivFunctorSheafFiberIso_inv_naturality B X hX a (E.inverse.obj F)
  have e1 := (Iso.inv_comp_eq ((sheafEquivFunctorSheafFiberIso B X hX y).app
    (E.inverse.obj F))).1 h1
  have h1' := ((Iso.eq_comp_inv ((sheafEquivFunctorSheafFiberIso B X hX x).app
    (E.inverse.obj F))).1 (e1.trans (Category.assoc _ _ _).symm)).symm
  have h2 := ((smallEtalePointHom X a).sheafFiber (A := Type (u + 1))).naturality
    (E.counitIso.inv.app F)
  rw [pointSmallEtaleSheafFiberIso_hom_app, pointSmallEtaleSheafFiberIso_hom_app]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h1').trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h2).trans (Category.assoc _ _ _))))

end StalkComparison

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] GeometricPoint.residueFieldAlgebra

section Generic

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

/-- A component of a whiskered natural transformation is invertible as soon as the image of the
component is, stated so that the hypothesis matches `H.map (α.app X)` syntactically. -/
theorem isIso_whiskerRight_app_of_isIso_map {F G : C ⥤ D} (α : F ⟶ G) (H : D ⥤ E) (X : C)
    (h : IsIso (H.map (α.app X))) : IsIso ((Functor.whiskerRight α H).app X) := h

/-- A component of a composite of five natural transformations is invertible as soon as the
five components are. -/
theorem isIso_comp_app_of_isIso₅ {F₀ F₁ F₂ F₃ F₄ F₅ : C ⥤ D} (a : F₀ ⟶ F₁) (b : F₁ ⟶ F₂)
    (c : F₂ ⟶ F₃) (d : F₃ ⟶ F₄) (e : F₄ ⟶ F₅) (X : C) (ha : IsIso (a.app X))
    (hb : IsIso (b.app X)) (hc : IsIso (c.app X)) (hd : IsIso (d.app X))
    (he : IsIso (e.app X)) : IsIso ((a ≫ b ≫ c ≫ d ≫ e).app X) := by
  simp only [NatTrans.comp_app]
  infer_instance

/-- A component of a natural isomorphism whiskered on the left is invertible. -/
theorem isIso_whiskerLeft_hom_app {G H : D ⥤ E} (F : C ⥤ D) (e : G ≅ H) (X : C) :
    IsIso ((Functor.whiskerLeft F e.hom).app X) := by
  rw [Functor.whiskerLeft_app]
  infer_instance

/-- A natural family of maps of underlying sets between additive functors to abelian groups,
as a family of morphisms of abelian groups (it is additive by
`AlgebraicGeometry.ProEtale.natural_map_add`). -/
def natTransAddHom {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
    (F G : C ⥤ AddCommGrpCat.{v}) [F.Additive] [G.Additive]
    (a : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) (X : C) : F.obj X ⟶ G.obj X :=
  AddCommGrpCat.ofHom
    { toFun := ConcreteCategory.hom (a.app X)
      map_zero' := by
        have he := AlgebraicGeometry.ProEtale.natural_map_add F G a X 0 0
        rw [add_zero] at he
        exact left_eq_add.1 he
      map_add' := AlgebraicGeometry.ProEtale.natural_map_add F G a X }

/-- The image of `natTransAddHom` of a natural map factored through natural isomorphisms of the
underlying-set functors is read off the middle factor. -/
theorem mem_range_natTransAddHom_iff {C : Type*} [Category* C] [Preadditive C]
    [HasBinaryBiproducts C] (F G : C ⥤ AddCommGrpCat.{v}) [F.Additive] [G.Additive]
    (a : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat)
    {P Q : C ⥤ Type v} (α : F ⋙ forget AddCommGrpCat ≅ P) (β : G ⋙ forget AddCommGrpCat ≅ Q)
    (ψ : P ⟶ Q) (ha : a = α.hom ≫ ψ ≫ β.inv) (X : C) (z : G.obj X) :
    z ∈ Set.range (ConcreteCategory.hom (natTransAddHom F G a X)) ↔
      ConcreteCategory.hom (β.hom.app X) z ∈ Set.range (ConcreteCategory.hom (ψ.app X)) := by
  subst ha
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨ConcreteCategory.hom (α.hom.app X) x, ?_⟩
    change _ = ConcreteCategory.hom (β.hom.app X)
      (ConcreteCategory.hom ((α.hom ≫ ψ ≫ β.inv).app X) x)
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
    rw [← ConcreteCategory.comp_apply (β.inv.app X), Iso.inv_hom_id_app]
    rfl
  · rintro ⟨y, hy⟩
    refine ⟨ConcreteCategory.hom (α.inv.app X) y, ?_⟩
    change ConcreteCategory.hom ((α.hom ≫ ψ ≫ β.inv).app X)
      (ConcreteCategory.hom (α.inv.app X) y) = z
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
    rw [← ConcreteCategory.comp_apply (α.inv.app X), Iso.inv_hom_id_app]
    change ConcreteCategory.hom (β.inv.app X) (ConcreteCategory.hom (ψ.app X) y) = z
    rw [hy, ← ConcreteCategory.comp_apply, Iso.hom_inv_id_app]
    rfl

/-- The image of a whiskered component is the image of the component. -/
theorem mem_range_whiskerLeft_app_iff {C D : Type*} [Category* C] [Category* D] (E : C ⥤ D)
    {P Q : D ⥤ Type v} (ψ : P ⟶ Q) (X : C) (y : (E ⋙ Q).obj X) :
    y ∈ Set.range (ConcreteCategory.hom ((Functor.whiskerLeft E ψ).app X)) ↔
      y ∈ Set.range (ConcreteCategory.hom (ψ.app (E.obj X))) :=
  Iff.rfl

end Generic

section Sets

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  {A : Scheme.{u}} (φ : A ⟶ S)

/-- For `φ : A ⟶ S` quasi-compact and quasi-separated, taking global sections over the strict
henselization of `S` at `s` turns the base change map for `φ` at a sheaf of sets `F` into an
isomorphism. -/
theorem isIso_whiskerRight_smallEtaleSetBaseChange_app [QuasiCompact φ] [QuasiSeparated φ]
    (F : Sheaf A.smallEtaleTopology (Type (u + 1))) :
    IsIso ((Functor.whiskerRight
      (smallEtaleSetBaseChange.{u, 0} (pullback.fst φ (strictHenselizationToBase B S hS s))
        (pullback.snd φ (strictHenselizationToBase B S hS s)) φ
        (strictHenselizationToBase B S hS s) pullback.condition)
      (Sheaf.Γ (strictHenselization B S hS s).smallEtaleTopology (Type (u + 1)))).app F) :=
  isIso_whiskerRight_app_of_isIso_map
    (smallEtaleSetBaseChange.{u, 0} (pullback.fst φ (strictHenselizationToBase B S hS s))
      (pullback.snd φ (strictHenselizationToBase B S hS s)) φ
      (strictHenselizationToBase B S hS s) pullback.condition)
    (Sheaf.Γ (strictHenselization B S hS s).smallEtaleTopology (Type (u + 1))) F
    (isIso_Γ_map_smallEtaleSetBaseChange_strictHenselization B S hS s φ F)

/-- **Stacks 03Q9 in degree zero, as a natural isomorphism.** For `φ` quasi-compact and
quasi-separated, the stalk at `s` of `φ_* F` is the set of sections of the pullback of `F` to
`A ×_S Spec 𝒪^{sh}_{S,s}`, naturally in the sheaf of sets `F`. -/
def directImageStalkIsoBaseChangeSections [QuasiCompact φ] [QuasiSeparated φ] :
    (smallEtaleBaseChange φ).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology S) (smallEtaleTopology A) ⋙
      (pointSmallEtale s.hom).sheafFiber (A := Type (u + 1)) ≅
    smallEtaleInverseImage.{u, 0} (pullback.fst φ (strictHenselizationToBase B S hS s)) ⋙
      Sheaf.Γ (pullback φ (strictHenselizationToBase B S hS s)).smallEtaleTopology
        (Type (u + 1)) :=
  Functor.isoWhiskerLeft _ (stalkIsoStrictHenselizationGamma B S hS s) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    @asIso _ _ _ _ (Functor.whiskerRight
      (smallEtaleSetBaseChange.{u, 0} (pullback.fst φ (strictHenselizationToBase B S hS s))
        (pullback.snd φ (strictHenselizationToBase B S hS s)) φ
        (strictHenselizationToBase B S hS s) pullback.condition)
      (Sheaf.Γ (strictHenselization B S hS s).smallEtaleTopology (Type (u + 1))))
      (@NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
        (fun F => isIso_whiskerRight_smallEtaleSetBaseChange_app B S hS s φ F)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, 0}
        (pullback.fst φ (strictHenselizationToBase B S hS s)))
      (smallEtalePushforwardGammaIso.{u, 0}
        (pullback.snd φ (strictHenselizationToBase B S hS s)))

end Sets

section Germ

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (t : GeometricPoint (Spec (.of K)))

/-- The germ at a geometric point `t̄` of a global section of a sheaf of sets on Mathlib's small
étale site of `Spec K`, as a natural transformation (Stacks 04JM: its image is the set of
Galois-fixed elements). -/
def sheafΓGerm :
    Sheaf.Γ (Spec (.of K)).smallEtaleTopology (Type (u + 1)) ⟶
      (SmallEtale.sheafEquiv B (Spec (.of K)) hK (Type (u + 1))).inverse ⋙
        etaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK t where
  app G := ((Sheaf.ΓNatIsoSheafSections _ _
      (isTerminalToEtaleSiteFinal B (Spec (.of K)) hK)).app G).hom ≫
    TypeCat.ofHom (fun x => etaleGlobalSectionGerm.{u, u + 1} B K hK t
      ((SmallEtale.sheafEquiv B (Spec (.of K)) hK (Type (u + 1))).inverse.obj G) x)
  naturality G G' f := by
    ext x
    have h1 := ConcreteCategory.congr_hom ((Sheaf.ΓNatIsoSheafSections _ _
      (isTerminalToEtaleSiteFinal B (Spec (.of K)) hK)).hom.naturality f) x
    exact (congrArg (etaleGlobalSectionGerm.{u, u + 1} B K hK t _) h1).trans
      (etaleGlobalSectionGerm_map.{u, u + 1} B K hK t
        ((SmallEtale.sheafEquiv B (Spec (.of K)) hK (Type (u + 1))).inverse.map f) _)

/-- The germ of a global section `x` of `G` is the underlying element of the Galois-fixed point
that `sheafΓEquivGaloisFixedPoints` assigns to `x`. -/
theorem sheafΓGerm_app_apply (G : Sheaf (Spec (.of K)).smallEtaleTopology (Type (u + 1)))
    (x : (Sheaf.Γ (Spec (.of K)).smallEtaleTopology (Type (u + 1))).obj G) :
    (sheafΓGerm B K hK t).app G x =
      (sheafΓEquivGaloisFixedPoints B K hK t G x).1 :=
  rfl

private theorem chain_globalGerm {𝒞 : Type*} [Category* 𝒞] {a b c d e f g : 𝒞}
    (Γm : a ⟶ b) (germ : b ⟶ c) (fm : c ⟶ d) (ih : d ⟶ e) (Gt : b ⟶ f) (germ0 : f ⟶ c)
    (ΓT : a ⟶ f) (ca : f ⟶ g) (germ' : g ⟶ d) (gB : f ⟶ e)
    (ha : Gt ≫ germ0 = germ) (hb : Γm ≫ Gt = ΓT) (hc : germ0 ≫ fm = ca ≫ germ')
    (he : ca ≫ germ' ≫ ih = gB) :
    Γm ≫ germ ≫ fm ≫ ih = ΓT ≫ gB := by
  subst ha hb he
  simp only [Category.assoc]
  rw [reassoc_of% hc]

/-- **The germ of a global section on Mathlib's site is the germ on the bounded site**: through
the stalk comparison of the two small étale sites of `Spec K`, the germ at `t̄` of a global section
on Mathlib's site is its germ on the bounded site. -/
theorem smallEtaleGlobalGerm_app_comp_pointSmallEtaleSheafFiberIso_hom_app
    (G : Sheaf (Spec (.of K)).smallEtaleTopology (Type (u + 1))) :
    (smallEtaleGlobalGerm t.hom).app G ≫
        (pointSmallEtaleSheafFiberIso B (Spec (.of K)) hK t).hom.app G =
      (sheafΓGerm B K hK t).app G := by
  let E := SmallEtale.sheafEquiv B (Spec (.of K)) hK (Type (u + 1))
  let U0 := SmallEtale.final B (Spec (.of K)) hK
  let x0 := finalGeometricPointLift B K hK t
  let x0' := (toEtaleSiteFiberIso B (Spec (.of K)) hK t).inv.app U0 x0
  let hT0 := isTerminalToEtaleSiteFinal B (Spec (.of K)) hK
  let term : (SmallEtale.toEtaleSite B (Spec (.of K)) hK).obj U0 ⟶
      Scheme.Etale.mk (𝟙 (Spec (.of K))) := (isTerminalEtaleMkId _).from _
  have ha : G.obj.map term.op ≫ (pointSmallEtale t.hom).toPresheafFiber _ x0' G.obj =
      (pointSmallEtale t.hom).toPresheafFiber (Scheme.Etale.mk (𝟙 (Spec (.of K))))
        (pointSmallEtaleIdElementOf t.hom) G.obj := by
    refine ((pointSmallEtale t.hom).toPresheafFiber_w term x0' G.obj).trans ?_
    rw [eq_pointSmallEtaleIdElementOf t.hom ((pointSmallEtale t.hom).fiber.map term x0')]
  have hb :=
    Sheaf.ΓNatIsoSheafSections_hom_app_map _ (isTerminalEtaleMkId (Spec (.of K))) hT0 term G
  have hc := (pointSmallEtale t.hom).toPresheafFiber_naturality (E.counitIso.inv.app G).hom
    ((SmallEtale.toEtaleSite B (Spec (.of K)) hK).obj U0) x0'
  have hd :
      (E.counitIso.inv.app G).hom.app (op ((SmallEtale.toEtaleSite B (Spec (.of K)) hK).obj U0)) =
      (E.unit.app (E.inverse.obj G)).hom.app (op U0) :=
    (congrArg (fun φ => φ.hom.app (op U0)) (E.unit_app_inverse G)).symm
  have hgerm := toPresheafFiber_sheafEquivFunctorSheafFiberIso_inv B (Spec (.of K)) hK t
    (E.inverse.obj G) U0 x0
  have he :
      (E.counitIso.inv.app G).hom.app (op ((SmallEtale.toEtaleSite B (Spec (.of K)) hK).obj U0)) ≫
      (pointSmallEtale t.hom).toPresheafFiber _ x0' (E.functor.obj (E.inverse.obj G)).obj ≫
      (sheafEquivFunctorSheafFiberIso B (Spec (.of K)) hK t).hom.app (E.inverse.obj G) =
      (geometricPointSitePoint B (Spec (.of K)) hK t).toPresheafFiber U0 x0
        (E.inverse.obj G).obj := by
    rw [hd]
    exact (((Iso.comp_inv_eq ((sheafEquivFunctorSheafFiberIso B (Spec (.of K)) hK t).app
      (E.inverse.obj G))).1 hgerm).trans (Category.assoc _ _ _)).symm
  have key := chain_globalGerm _ _ _ _ _ _ _ _ _ _ ha hb hc he
  rw [pointSmallEtaleSheafFiberIso_hom_app]
  exact key

include B hK in
/-- The germ at `t̄` of global sections on Mathlib's small étale site of `Spec K` is injective
(Stacks 04JM). -/
theorem smallEtaleGlobalGerm_app_injective
    (G : Sheaf (Spec (.of K)).smallEtaleTopology (Type (u + 1))) :
    Function.Injective (ConcreteCategory.hom ((smallEtaleGlobalGerm t.hom).app G)) := by
  intro c c' h
  have hc := ConcreteCategory.congr_hom
    (smallEtaleGlobalGerm_app_comp_pointSmallEtaleSheafFiberIso_hom_app B K hK t G) c
  have hc' := ConcreteCategory.congr_hom
    (smallEtaleGlobalGerm_app_comp_pointSmallEtaleSheafFiberIso_hom_app B K hK t G) c'
  rw [ConcreteCategory.comp_apply, h, ← ConcreteCategory.comp_apply, hc'] at hc
  refine (sheafΓEquivGaloisFixedPoints B K hK t G).injective (Subtype.ext ?_)
  rw [← sheafΓGerm_app_apply, ← sheafΓGerm_app_apply]
  exact hc.symm

include B hK in
/-- **The image of the germ of global sections is the set of Galois-fixed elements** (Stacks 04JM
on Mathlib's site): for an algebraic geometric point `t̄` of `Spec K`, an element of the stalk at
`t̄` is the germ of a global section exactly when every automorphism of `t̄` over `K` fixes it. -/
theorem mem_range_smallEtaleGlobalGerm_app_iff (ht : t.IsAlgebraic)
    (G : Sheaf (Spec (.of K)).smallEtaleTopology (Type (u + 1)))
    (y : (pointSmallEtale t.hom).sheafFiber.obj G) :
    y ∈ Set.range (ConcreteCategory.hom ((smallEtaleGlobalGerm t.hom).app G)) ↔
      ∀ (σ : GeometricPoint.absoluteGaloisGroup t)
        (τ : Gal(t.residueField / (Spec (.of K)).residueField (t.hom default)))
        (_ : ∀ a : GeometricPoint.separableClosure t,
          (σ a : t.residueField) = τ (a : t.residueField))
        (α : t.source ≅ t.source) (_ : α.hom = Spec.map (CommRingCat.ofHom τ.toRingHom))
        (hαt : α.hom ≫ t.hom = t.hom),
        ConcreteCategory.hom
          ((pointSmallEtaleHom t.hom t.hom α.hom hαt).sheafFiber.app G) y = y := by
  constructor
  · rintro ⟨c, rfl⟩ σ τ hτ α hα hαt
    simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom
      (smallEtaleGlobalGerm_app_pointSmallEtaleHom t.hom α.hom hαt G) c
  · intro hy
    let P := (pointSmallEtaleSheafFiberIso B (Spec (.of K)) hK t).hom.app G
    have hfix : ∀ σ : GeometricPoint.absoluteGaloisGroup t,
        ConcreteCategory.hom (etaleStalkSmul.{u, u + 1} B K hK t
          ((SmallEtale.sheafEquiv B (Spec (.of K)) hK (Type (u + 1))).inverse.obj G) σ)
          (ConcreteCategory.hom P y) = ConcreteCategory.hom P y := by
      intro σ
      obtain ⟨τ, hτ, α, hα, hαt⟩ := t.exists_lift_of_isAlgebraic ht σ
      rw [etaleStalkSmul_eq_geometricPointStalkMap.{u, u + 1} B K hK t _ σ τ hτ ⟨α.hom, hαt⟩ hα]
      have h2 := ConcreteCategory.congr_hom
        (pointSmallEtaleSheafFiberIso_hom_naturality B (Spec (.of K)) hK ⟨α.hom, hαt⟩ G) y
      exact h2.trans (congrArg (ConcreteCategory.hom P) (hy σ τ hτ α hα hαt))
    let c := (sheafΓEquivGaloisFixedPoints B K hK t G).symm ⟨_, hfix⟩
    refine ⟨c, (mono_iff_injective _).1 (inferInstance : Mono P) ?_⟩
    have hc := ConcreteCategory.congr_hom
      (smallEtaleGlobalGerm_app_comp_pointSmallEtaleSheafFiberIso_hom_app B K hK t G) c
    exact (hc.trans (sheafΓGerm_app_apply B K hK t G c)).trans
      (congrArg Subtype.val ((sheafΓEquivGaloisFixedPoints B K hK t G).apply_symm_apply ⟨_, hfix⟩))

end Germ


section Boundary

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (B' : BigEtaleSite.{u}) (U : B'.Scheme) (j : U.1 ⟶ S)
  (K : Type u) [Field K] (e : pullback j (strictHenselizationToBase B S hS s) ≅ Spec (.of K))
  (hK : B'.Contains (Spec (.of K))) (g : B'.obj (Spec (.of K)) hK ⟶ U)
  (hg : B'.inclusion.map g = e.inv ≫ pullback.fst j (strictHenselizationToBase B S hS s))
  (t : GeometricPoint (Spec (.of K)))

/-- Inverse image to `U ×_S Spec 𝒪^{sh} ≅ Spec K` followed by direct image along the
identification is inverse image along `g : Spec K ⟶ U`. -/
def baseChangeFieldInverseImageIso :
    smallEtaleInverseImage.{u, 0} (pullback.fst j (strictHenselizationToBase B S hS s)) ⋙
        (smallEtaleBaseChange e.hom).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology (Spec (.of K)))
          (smallEtaleTopology (pullback j (strictHenselizationToBase B S hS s))) ≅
      smallEtaleInverseImage.{u, 0} (B'.inclusion.map g) :=
  Functor.isoWhiskerLeft _ (smallEtalePushforwardIsoInverseImageOfIso.{u, 0} e) ≪≫
    smallEtaleInverseImageComp.{u, 0} e.inv
      (pullback.fst j (strictHenselizationToBase B S hS s)) ≪≫
    eqToIso (congrArg (fun k => smallEtaleInverseImage.{u, 0} k) hg.symm)

/-- Inverse image along `g` on Mathlib's small étale site, read on the bounded sites, is the
bounded inverse image, naturally in the sheaf. -/
def sheafEquivInverseInverseImageNatIso :
    smallEtaleInverseImage.{u, 0} (B'.inclusion.map g) ⋙
        (SmallEtale.sheafEquiv B' (Spec (.of K)) hK (Type (u + 1))).inverse ≅
      (SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).inverse ⋙
        (AlgebraicGeometry.smallEtaleBaseChange B' g).sheafPullback (Type (u + 1))
          (SmallEtale.topology B' U.1 U.2) (SmallEtale.topology B' (Spec (.of K)) hK) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (SmallEtale.sheafEquivPullbackBaseChangeIso B' g (Type (u + 1))
        (smallEtaleInverseImageAdjunction.{u, 0} (B'.inclusion.map g))
        ((AlgebraicGeometry.smallEtaleBaseChange B' g).sheafAdjunctionContinuous (Type (u + 1))
          (SmallEtale.topology B' U.1 U.2) (SmallEtale.topology B' (Spec (.of K)) hK))) _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (SmallEtale.sheafEquiv B' (Spec (.of K)) hK (Type (u + 1))).unitIso.symm) ≪≫
    Functor.isoWhiskerLeft _ (Functor.rightUnitor _)

/-- The stalk at `s` of `j_* F` as a set of sections over `Spec K`, naturally in `F`. -/
def directImageStalkIsoFieldSections [QuasiCompact j] [QuasiSeparated j] :
    (smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology S) (smallEtaleTopology U.1) ⋙
      (pointSmallEtale s.hom).sheafFiber (A := Type (u + 1)) ≅
    smallEtaleInverseImage.{u, 0} (B'.inclusion.map g) ⋙
      Sheaf.Γ (Spec (.of K)).smallEtaleTopology (Type (u + 1)) :=
  directImageStalkIsoBaseChangeSections B S hS s j ≪≫
    Functor.isoWhiskerLeft _ (smallEtalePushforwardGammaIso.{u, 0} e.hom).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (baseChangeFieldInverseImageIso B S hS s B' U j K e hK g hg) _

/-- **The specialization map of `j_* F` at a boundary point.** The stalk at `s` of `j_* F`
maps, naturally in the sheaf of sets `F` on `U`, to the stalk of `F` at the geometric point
`g(t̄)` of `U`: take sections over `Spec K`, then their germ at `t̄`, the stalk of an inverse image
(Stacks 03Q1) and the comparison of the stalks of Mathlib's and the bounded small étale sites. -/
def directImageStalkToStalk [QuasiCompact j] [QuasiSeparated j] :
    (smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology S) (smallEtaleTopology U.1) ⋙
      (pointSmallEtale s.hom).sheafFiber (A := Type (u + 1)) ⟶
    (SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).inverse ⋙
      (geometricPointSitePoint B' U.1 U.2 (t.map (B'.inclusion.map g))).sheafFiber :=
  (directImageStalkIsoFieldSections B S hS s B' U j K e hK g hg).hom ≫
    Functor.whiskerLeft _ (smallEtaleGlobalGerm t.hom) ≫
    (smallEtaleInverseImageStalkIso.{0, u} (B'.inclusion.map g) t.hom).hom ≫
    (pointSmallEtaleSheafFiberIso B' U.1 U.2 (t.map (B'.inclusion.map g))).hom

variable {B S hS s B' U j K e hK g hg t} in
/-- `directImageStalkToStalk` unfolded: sections over `Spec K`, their germ at `t̄`, the stalk of
the inverse image along `g`, and the comparison of the two sites. -/
theorem directImageStalkToStalk_app_apply [QuasiCompact j] [QuasiSeparated j]
    (F : Sheaf U.1.smallEtaleTopology (Type (u + 1)))
    (x : (pointSmallEtale s.hom).sheafFiber.obj
      (((smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology S) (smallEtaleTopology U.1)).obj F)) :
    ConcreteCategory.hom ((directImageStalkToStalk B S hS s B' U j K e hK g hg t).app F) x =
      ConcreteCategory.hom
          ((pointSmallEtaleSheafFiberIso B' U.1 U.2 (t.map (B'.inclusion.map g))).hom.app F)
        (ConcreteCategory.hom
          ((smallEtaleInverseImageStalkIso.{0, u} (B'.inclusion.map g) t.hom).hom.app F)
          (ConcreteCategory.hom ((smallEtaleGlobalGerm t.hom).app
              ((smallEtaleInverseImage.{u, 0} (B'.inclusion.map g)).obj F))
            (ConcreteCategory.hom
              ((directImageStalkIsoFieldSections B S hS s B' U j K e hK g hg).hom.app F) x))) :=
  rfl

variable {B' U K hK g t} in
/-- The Galois action on the stalk at `t̄` of the inverse image along `g` is, through the stalk of
an inverse image, the map of Tag 04FN along the image in `U` of the automorphism of `t̄`. -/
theorem geometricPointStalkMap_pullbackSheafFiber (F : Sheaf U.1.smallEtaleTopology (Type (u + 1)))
    (σ : GeometricPoint.absoluteGaloisGroup t)
    (τ : Gal(t.residueField/(Spec (.of K)).residueField (t.hom default)))
    (hτ : ∀ a : GeometricPoint.separableClosure t,
      (σ a : t.residueField) = τ (a : t.residueField))
    (α : t.source ≅ t.source) (hα : α.hom = Spec.map (CommRingCat.ofHom τ.toRingHom))
    (hαt : α.hom ≫ t.hom = t.hom)
    (y : (etaleStalkFunctor.{u, u + 1} B' (Spec (.of K)) hK t).obj
      ((SmallEtale.sheafEquiv B' (Spec (.of K)) hK (Type (u + 1))).inverse.obj
        ((smallEtaleInverseImage.{u, 0} (B'.inclusion.map g)).obj F))) :
    ConcreteCategory.hom ((geometricPointStalkMap B' U.1 U.2
        ((⟨α.hom, hαt⟩ : GeometricPoint.Hom t t).mapHom (B'.inclusion.map g)) (Type (u + 1))).app
        ((SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).inverse.obj F).obj)
      (ConcreteCategory.hom ((smallEtalePullbackSheafFiberIso B' g t (Type (u + 1))).hom.app
          ((SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).inverse.obj F))
        (ConcreteCategory.hom ((etaleStalkFunctor.{u, u + 1} B' (Spec (.of K)) hK t).map
            ((sheafEquivInverseInverseImageNatIso B' U K hK g).hom.app F)) y)) =
    ConcreteCategory.hom ((smallEtalePullbackSheafFiberIso B' g t (Type (u + 1))).hom.app
        ((SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).inverse.obj F))
      (ConcreteCategory.hom ((etaleStalkFunctor.{u, u + 1} B' (Spec (.of K)) hK t).map
          ((sheafEquivInverseInverseImageNatIso B' U K hK g).hom.app F))
        (ConcreteCategory.hom (etaleStalkSmul.{u, u + 1} B' K hK t _ σ) y)) := by
  let a : GeometricPoint.Hom t t := ⟨α.hom, hαt⟩
  have h0 := ConcreteCategory.congr_hom (etaleStalkSmul_naturality.{u, u + 1} B' K hK t
    ((sheafEquivInverseInverseImageNatIso B' U K hK g).hom.app F) σ) y
  have h1 := etaleStalkSmul_eq_geometricPointStalkMap.{u, u + 1} B' K hK t
    (((SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).inverse ⋙
      (AlgebraicGeometry.smallEtaleBaseChange B' g).sheafPullback (Type (u + 1))
      (SmallEtale.topology B' U.1 U.2) (SmallEtale.topology B' (Spec (.of K)) hK)).obj F)
      σ τ hτ a hα
  have h2 := ConcreteCategory.congr_hom
    (geometricPointStalkMap_comp_etaleStalkSmallEtalePullObjIso_hom B' g t (Type (u + 1)) a
      ((SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).inverse.obj F))
    (ConcreteCategory.hom ((etaleStalkFunctor.{u, u + 1} B' (Spec (.of K)) hK t).map
      ((sheafEquivInverseInverseImageNatIso B' U K hK g).hom.app F)) y)
  simp only [ConcreteCategory.comp_apply] at h0 h2
  rw [h0, h1]
  exact h2.symm

/-- The germ map of `sheafΓGerm` is injective (Stacks 04JM). -/
theorem sheafΓGerm_app_injective' (G : Sheaf (Spec (.of K)).smallEtaleTopology (Type (u + 1))) :
    Function.Injective (ConcreteCategory.hom ((sheafΓGerm B' K hK t).app G)) :=
  fun _ _ h => (sheafΓEquivGaloisFixedPoints B' K hK t G).injective (Subtype.ext h)

/-- **The specialization map of `j_* F` at a boundary point is injective.** -/
theorem directImageStalkToStalk_injective [QuasiCompact j] [QuasiSeparated j]
    (F : Sheaf U.1.smallEtaleTopology (Type (u + 1))) :
    Function.Injective
      (ConcreteCategory.hom ((directImageStalkToStalk B S hS s B' U j K e hK g hg t).app F)) := by
  intro x x' h
  rw [directImageStalkToStalk_app_apply, directImageStalkToStalk_app_apply] at h
  have h1 := (ConcreteCategory.bijective_of_isIso
    ((pointSmallEtaleSheafFiberIso B' U.1 U.2 (t.map (B'.inclusion.map g))).hom.app F)).1 h
  have h2 := (ConcreteCategory.bijective_of_isIso
    ((smallEtaleInverseImageStalkIso.{0, u} (B'.inclusion.map g) t.hom).hom.app F)).1 h1
  exact (ConcreteCategory.bijective_of_isIso
    ((directImageStalkIsoFieldSections B S hS s B' U j K e hK g hg).hom.app F)).1
    (smallEtaleGlobalGerm_app_injective B' K hK t _ h2)

/-- Tag 03Q1 and the comparison of the two sites intertwine the maps induced by an automorphism
`α` of `t̄` over `K` with the map of Tag 04FN along its image in `U`. -/
theorem smallEtaleInverseImageStalkIso_comp_pointSmallEtaleSheafFiberIso_geometricPointStalkMap
    (F : Sheaf U.1.smallEtaleTopology (Type (u + 1))) (α : t.source ≅ t.source)
    (hαt : α.hom ≫ t.hom = t.hom) :
    (smallEtaleInverseImageStalkIso.{0, u} (B'.inclusion.map g) t.hom).hom.app F ≫
        (pointSmallEtaleSheafFiberIso B' U.1 U.2 (t.map (B'.inclusion.map g))).hom.app F ≫
        (geometricPointStalkMap B' U.1 U.2
          ((⟨α.hom, hαt⟩ : GeometricPoint.Hom t t).mapHom (B'.inclusion.map g))
            (Type (u + 1))).app
          ((SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).inverse.obj F).obj =
      (pointSmallEtaleHom t.hom t.hom α.hom hαt).sheafFiber.app
          ((smallEtaleInverseImage.{u, 0} (B'.inclusion.map g)).obj F) ≫
        (smallEtaleInverseImageStalkIso.{0, u} (B'.inclusion.map g) t.hom).hom.app F ≫
        (pointSmallEtaleSheafFiberIso B' U.1 U.2 (t.map (B'.inclusion.map g))).hom.app F := by
  have hN := pointSmallEtaleSheafFiberIso_hom_naturality B' U.1 U.2
    ((⟨α.hom, hαt⟩ : GeometricPoint.Hom t t).mapHom (B'.inclusion.map g)) F
  have hF := smallEtaleInverseImageStalkIso_hom_naturality.{u, 0} (B'.inclusion.map g) t.hom t.hom
    α.hom hαt F
  exact (congrArg (_ ≫ ·) hN).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hF.symm).trans (Category.assoc _ _ _)))

/-- **The image of the specialization map of `j_* F` at a boundary point is the set of
inertia invariants.** For an algebraic geometric point `t̄` of `Spec K`, an element of the stalk
of `F` at `g(t̄)` comes from the stalk of `j_* F` at `s` exactly when it is fixed by the map of
Tag 04FN along the image in `U` of every automorphism of `t̄` over `K`. -/
@[sga "7 XIII 1.2.2" "(B), partial"]
theorem mem_range_directImageStalkToStalk_iff [QuasiCompact j] [QuasiSeparated j]
    (ht : t.IsAlgebraic) (F : Sheaf U.1.smallEtaleTopology (Type (u + 1)))
    (z : ((geometricPointSitePoint B' U.1 U.2 (t.map (B'.inclusion.map g))).sheafFiber).obj
      ((SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).inverse.obj F)) :
    z ∈ Set.range
        (ConcreteCategory.hom ((directImageStalkToStalk B S hS s B' U j K e hK g hg t).app F)) ↔
      ∀ (σ : GeometricPoint.absoluteGaloisGroup t)
        (τ : Gal(t.residueField / (Spec (.of K)).residueField (t.hom default)))
        (_ : ∀ a : GeometricPoint.separableClosure t,
          (σ a : t.residueField) = τ (a : t.residueField))
        (α : t.source ≅ t.source) (_ : α.hom = Spec.map (CommRingCat.ofHom τ.toRingHom))
        (hαt : α.hom ≫ t.hom = t.hom),
        ConcreteCategory.hom ((geometricPointStalkMap B' U.1 U.2
          ((⟨α.hom, hαt⟩ : GeometricPoint.Hom t t).mapHom (B'.inclusion.map g))
            (Type (u + 1))).app
          ((SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).inverse.obj F).obj) z = z := by
  let P := (pointSmallEtaleSheafFiberIso B' U.1 U.2 (t.map (B'.inclusion.map g))).hom.app F
  let Q := (smallEtaleInverseImageStalkIso.{0, u} (B'.inclusion.map g) t.hom).hom.app F
  let Gm := (smallEtaleGlobalGerm t.hom).app
    ((smallEtaleInverseImage.{u, 0} (B'.inclusion.map g)).obj F)
  let D := (directImageStalkIsoFieldSections B S hS s B' U j K e hK g hg).hom.app F
  have hP := ConcreteCategory.bijective_of_isIso P
  have hQ := ConcreteCategory.bijective_of_isIso Q
  have hD := ConcreteCategory.bijective_of_isIso D
  have hk := fun α hαt w => ConcreteCategory.congr_hom
    (smallEtaleInverseImageStalkIso_comp_pointSmallEtaleSheafFiberIso_geometricPointStalkMap
      B' U K hK g t F α hαt) w
  constructor
  · rintro ⟨x, rfl⟩ σ τ hτ α hα hαt
    rw [directImageStalkToStalk_app_apply]
    have hfix := ((mem_range_smallEtaleGlobalGerm_app_iff B' K hK t ht _
      (ConcreteCategory.hom Gm (ConcreteCategory.hom D x))).1 ⟨_, rfl⟩) σ τ hτ α hα hαt
    exact (hk α hαt _).trans
      (congrArg (fun w => ConcreteCategory.hom P (ConcreteCategory.hom Q w)) hfix)
  · intro hz
    obtain ⟨w₁, rfl⟩ := hP.2 z
    obtain ⟨w, rfl⟩ := hQ.2 w₁
    have hw : w ∈ Set.range (ConcreteCategory.hom Gm) := by
      refine (mem_range_smallEtaleGlobalGerm_app_iff B' K hK t ht _ w).2 ?_
      intro σ τ hτ α hα hαt
      exact hQ.1 (hP.1 ((hk α hαt w).symm.trans (hz σ τ hτ α hα hαt)))
    obtain ⟨c, rfl⟩ := hw
    obtain ⟨x, rfl⟩ := hD.2 c
    exact ⟨x, directImageStalkToStalk_app_apply F x⟩

end Boundary





section Modules

/-- Limits of the size of the small étale site in `ModuleCat.{u + 1} R` for a ring `R` of the
lowest universe, with the universes pinned for instance search. -/
instance hasLimitsOfSize_moduleCat_type (R : Type) [Ring R] :
    HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1}

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (B' : BigEtaleSite.{u}) (U : B'.Scheme) (j : U.1 ⟶ S)
  (K : Type u) [Field K] (e : pullback j (strictHenselizationToBase B S hS s) ≅ Spec (.of K))
  (hK : B'.Contains (Spec (.of K))) (g : B'.obj (Spec (.of K)) hK ⟶ U)
  (hg : B'.inclusion.map g = e.inv ≫ pullback.fst j (strictHenselizationToBase B S hS s))
  (t : GeometricPoint (Spec (.of K))) (R : Type) [Ring R]

/-- The forgetful functor from `R`-modules in universe `u + 1` to types preserves filtered colimits
indexed by categories in universe `u`. -/
instance forget_moduleCat_preservesFilteredColimitsOfSize :
    PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} R)) := by
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1} ⋙ forget AddCommGrpCat.{u + 1}) :=
    inferInstance
  exact preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1} ⋙ forget AddCommGrpCat.{u + 1})

/-- The forgetful functor from modules preserves the filtered colimits over the pointed étale
neighbourhoods of a geometric point that compute stalks on the bounded site. -/
instance forget_moduleCat_preservesFiberColimits (B : BigEtaleSite.{u}) (X : Scheme.{u})
    (hX : B.Contains X) (x : GeometricPoint X) :
    PreservesColimitsOfShape (geometricPointFiber B X hX x).Elementsᵒᵖ
      (forget (ModuleCat.{u + 1} R)) :=
  Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{u} (geometricPointFiber B X hX x).Elementsᵒᵖ) _

/-- Mathlib's stalk functor at a geometric point is additive on sheaves of modules: it is a left
adjoint, so it preserves binary biproducts. -/
instance pointSmallEtale_sheafFiber_moduleCat_additive {X : Scheme.{u}} (x : GeometricPoint X) :
    ((pointSmallEtale x.hom).sheafFiber (A := ModuleCat.{u + 1} R)).Additive := by
  have : ((pointSmallEtale x.hom).sheafFiber (A := ModuleCat.{u + 1} R)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    ((pointSmallEtale x.hom).sheafFiber (A := ModuleCat.{u + 1} R))
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The stalk functor of the bounded small étale site at a geometric point is additive on
sheaves of modules. -/
instance geometricPointSitePoint_sheafFiber_moduleCat_additive (B : BigEtaleSite.{u})
    (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X) :
    ((geometricPointSitePoint B X hX x).sheafFiber (A := ModuleCat.{u + 1} R)).Additive := by
  have : ((geometricPointSitePoint B X hX x).sheafFiber
      (A := ModuleCat.{u + 1} R)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    ((geometricPointSitePoint B X hX x).sheafFiber (A := ModuleCat.{u + 1} R))
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Restriction of sheaves of modules from Mathlib's small étale site to the bounded one is
additive: it is an equivalence. -/
instance sheafEquiv_inverse_moduleCat_additive (B : BigEtaleSite.{u}) (X : Scheme.{u})
    (hX : B.Contains X) :
    (SmallEtale.sheafEquiv B X hX (ModuleCat.{u + 1} R)).inverse.Additive := by
  have : (SmallEtale.sheafEquiv B X hX (ModuleCat.{u + 1} R)).inverse.IsLeftAdjoint :=
    (SmallEtale.sheafEquiv B X hX (ModuleCat.{u + 1} R)).symm.toAdjunction.isLeftAdjoint
  have : (SmallEtale.sheafEquiv B X hX (ModuleCat.{u + 1} R)).inverse.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (SmallEtale.sheafEquiv B X hX (ModuleCat.{u + 1} R)).inverse
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The stalk at `s` of the direct image of a sheaf of `R`-modules, as an abelian group. -/
def directImageStalkAb :
    Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤ AddCommGrpCat.{u + 1} :=
  (smallEtaleBaseChange j).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
      (smallEtaleTopology S) (smallEtaleTopology U.1) ⋙
    (pointSmallEtale s.hom).sheafFiber ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}

/-- The stalk at `g(t̄)` of a sheaf of `R`-modules, read on the bounded site, as an abelian
group. -/
def pointStalkAb :
    Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤ AddCommGrpCat.{u + 1} :=
  (SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} R)).inverse ⋙
    (geometricPointSitePoint B' U.1 U.2 (t.map (B'.inclusion.map g))).sheafFiber ⋙
      forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}

/-- The stalk of the direct image, `directImageStalkAb`, is an additive functor. -/
instance directImageStalkAb_additive : (directImageStalkAb S s B' U j R).Additive := by
  unfold directImageStalkAb
  infer_instance

/-- The stalk at `g(t̄)`, `pointStalkAb`, is an additive functor. -/
instance pointStalkAb_additive : (pointStalkAb B' U K hK g t R).Additive := by
  unfold pointStalkAb
  infer_instance

/-- The underlying set of the stalk of `j_* M` is the stalk of `j_*` of the underlying sheaf of
sets of `M`. -/
def directImageStalkAbForgetIso :
    directImageStalkAb S s B' U j R ⋙ forget AddCommGrpCat.{u + 1} ≅
      sheafCompose U.1.smallEtaleTopology (forget (ModuleCat.{u + 1} R)) ⋙
        ((smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
            (smallEtaleTopology S) (smallEtaleTopology U.1) ⋙
          (pointSmallEtale s.hom).sheafFiber (A := Type (u + 1))) :=
  Functor.isoWhiskerLeft ((smallEtaleBaseChange j).sheafPushforwardContinuous
      (ModuleCat.{u + 1} R) (smallEtaleTopology S) (smallEtaleTopology U.1))
    ((pointSmallEtale s.hom).sheafFiberCompIso (forget (ModuleCat.{u + 1} R))).symm

/-- The underlying set of the stalk of `M` at `g(t̄)` is the stalk of the underlying sheaf of sets
of `M`. -/
def pointStalkAbForgetIso :
    pointStalkAb B' U K hK g t R ⋙ forget AddCommGrpCat.{u + 1} ≅
      sheafCompose U.1.smallEtaleTopology (forget (ModuleCat.{u + 1} R)) ⋙
        ((SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).inverse ⋙
          (geometricPointSitePoint B' U.1 U.2 (t.map (B'.inclusion.map g))).sheafFiber) :=
  Functor.isoWhiskerLeft (SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} R)).inverse
    ((geometricPointSitePoint B' U.1 U.2 (t.map (B'.inclusion.map g))).sheafFiberCompIso
      (forget (ModuleCat.{u + 1} R))).symm

variable [QuasiCompact j] [QuasiSeparated j]

/-- The specialization map of `j_* M` at a boundary point on underlying sets, natural in the
sheaf of modules `M`. -/
def directImageStalkToStalkAb :
    directImageStalkAb S s B' U j R ⋙ forget AddCommGrpCat.{u + 1} ⟶
      pointStalkAb B' U K hK g t R ⋙ forget AddCommGrpCat.{u + 1} :=
  (directImageStalkAbForgetIso S s B' U j R).hom ≫
    Functor.whiskerLeft (sheafCompose U.1.smallEtaleTopology (forget (ModuleCat.{u + 1} R)))
      (directImageStalkToStalk B S hS s B' U j K e hK g hg t) ≫
    (pointStalkAbForgetIso B' U K hK g t R).inv

/-- The specialization map of `j_* M` is additive, by naturality (the two stalk functors are
additive and it is natural in `M`). -/
theorem directImageStalkToStalkAb_app_add (M : Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} R))
    (x y : (directImageStalkAb S s B' U j R).obj M) :
    ConcreteCategory.hom ((directImageStalkToStalkAb B S hS s B' U j K e hK g hg t R).app M)
        (x + y) =
      ConcreteCategory.hom ((directImageStalkToStalkAb B S hS s B' U j K e hK g hg t R).app M) x +
        ConcreteCategory.hom
          ((directImageStalkToStalkAb B S hS s B' U j K e hK g hg t R).app M) y := by
  have hP : (directImageStalkAb S s B' U j R).Additive := inferInstance
  have hQ : (pointStalkAb B' U K hK g t R).Additive := inferInstance
  exact @AlgebraicGeometry.ProEtale.natural_map_add _ _ _ _ _ _ hP hQ _ M x y

/-- **The specialization map of `j_* M` at a boundary point**, an additive map
`(j_* M)_s → M_{g(t̄)}` for a sheaf of `R`-modules `M` on `U`. -/
def directImageStalkToStalkHom (M : Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (directImageStalkAb S s B' U j R).obj M ⟶ (pointStalkAb B' U K hK g t R).obj M :=
  natTransAddHom _ _ (directImageStalkToStalkAb B S hS s B' U j K e hK g hg t R) M

/-- `directImageStalkToStalkHom` acts on elements as the component of
`directImageStalkToStalkAb`. -/
theorem directImageStalkToStalkHom_apply
    (M : Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} R))
    (x : (directImageStalkAb S s B' U j R).obj M) :
    directImageStalkToStalkHom B S hS s B' U j K e hK g hg t R M x =
      ConcreteCategory.hom ((directImageStalkToStalkAb B S hS s B' U j K e hK g hg t R).app M) x :=
  rfl

/-- The specialization map `(j_* M)_s → M_{g(t̄)}` is injective. -/
theorem directImageStalkToStalkHom_injective
    (M : Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    Function.Injective
      (ConcreteCategory.hom (directImageStalkToStalkHom B S hS s B' U j K e hK g hg t R M)) := by
  intro x x' h
  have h1 := (mono_iff_injective _).1 (inferInstance : Mono
    ((pointStalkAbForgetIso B' U K hK g t R).inv.app M)) h
  have h2 := directImageStalkToStalk_injective B S hS s B' U j K e hK g hg t _ h1
  exact (mono_iff_injective _).1 (inferInstance : Mono
    ((directImageStalkAbForgetIso S s B' U j R).hom.app M)) h2

omit [QuasiCompact j] [QuasiSeparated j] in
/-- The identification of the underlying set of the stalk of `M` with the stalk of its
underlying sheaf of sets intertwines the maps of Tag 04FN. -/
theorem pointStalkAbForgetIso_hom_app_geometricPointStalkMap
    (M : Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} R))
    (a : GeometricPoint.Hom (t.map (B'.inclusion.map g)) (t.map (B'.inclusion.map g)))
    (z : (pointStalkAb B' U K hK g t R).obj M) :
    ConcreteCategory.hom ((pointStalkAbForgetIso B' U K hK g t R).hom.app M)
        (ConcreteCategory.hom ((geometricPointStalkMap B' U.1 U.2 a (ModuleCat.{u + 1} R)).app
          ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} R)).inverse.obj M).obj) z) =
      ConcreteCategory.hom ((geometricPointStalkMap B' U.1 U.2 a (Type (u + 1))).app
          ((SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).inverse.obj
            ((sheafCompose U.1.smallEtaleTopology (forget (ModuleCat.{u + 1} R))).obj M)).obj)
        (ConcreteCategory.hom ((pointStalkAbForgetIso B' U K hK g t R).hom.app M) z) := by
  have hb : (pointStalkAbForgetIso B' U K hK g t R).hom.app M =
      (preservesColimitIso (forget (ModuleCat.{u + 1} R))
        ((CategoryOfElements.π (geometricPointFiber B' U.1 U.2
          (t.map (B'.inclusion.map g)))).op ⋙
          ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} R)).inverse.obj M).obj)).hom := by
    simp [pointStalkAbForgetIso, GrothendieckTopology.Point.sheafFiberCompIso,
      GrothendieckTopology.Point.presheafFiberCompIso, preservesColimitNatIso]
    rfl
  have h := ConcreteCategory.congr_hom (geometricPointStalkMap_preservesColimitIso B' U.1 U.2
    (forget (ModuleCat.{u + 1} R)) a
    ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} R)).inverse.obj M).obj) z
  simp only at h
  rw [hb]
  exact h

/-- **The image of the specialization map of `j_* M` at a boundary point is the module of
inertia invariants.** For an algebraic geometric point `t̄` of `Spec K`, an element of the stalk
of the sheaf of modules `M` at `g(t̄)` comes from `(j_* M)_s` exactly when it is fixed by the
map of Tag 04FN along the image in `U` of every automorphism of `t̄` over `K`. -/
@[sga "7 XIII 1.2.2" "(B), partial", sga "7 XXI 5.6.2" "partial"]
theorem mem_range_directImageStalkToStalkHom_iff (ht : t.IsAlgebraic)
    (M : Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} R))
    (z : (pointStalkAb B' U K hK g t R).obj M) :
    z ∈ Set.range
        (ConcreteCategory.hom (directImageStalkToStalkHom B S hS s B' U j K e hK g hg t R M)) ↔
      ∀ (σ : GeometricPoint.absoluteGaloisGroup t)
        (τ : Gal(t.residueField / (Spec (.of K)).residueField (t.hom default)))
        (_ : ∀ a : GeometricPoint.separableClosure t,
          (σ a : t.residueField) = τ (a : t.residueField))
        (α : t.source ≅ t.source) (_ : α.hom = Spec.map (CommRingCat.ofHom τ.toRingHom))
        (hαt : α.hom ≫ t.hom = t.hom),
        ConcreteCategory.hom ((geometricPointStalkMap B' U.1 U.2
          ((⟨α.hom, hαt⟩ : GeometricPoint.Hom t t).mapHom (B'.inclusion.map g))
            (ModuleCat.{u + 1} R)).app
          ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} R)).inverse.obj M).obj) z = z := by
  have h1 := mem_range_natTransAddHom_iff (directImageStalkAb S s B' U j R)
    (pointStalkAb B' U K hK g t R) (directImageStalkToStalkAb B S hS s B' U j K e hK g hg t R)
    (directImageStalkAbForgetIso S s B' U j R) (pointStalkAbForgetIso B' U K hK g t R)
    (Functor.whiskerLeft (sheafCompose U.1.smallEtaleTopology (forget (ModuleCat.{u + 1} R)))
      (directImageStalkToStalk B S hS s B' U j K e hK g hg t)) rfl M z
  refine h1.trans ?_
  rw [mem_range_whiskerLeft_app_iff, mem_range_directImageStalkToStalk_iff B S hS s B' U j K e
    hK g hg t ht]
  refine forall_congr' fun σ => forall_congr' fun τ => forall_congr' fun hτ =>
    forall_congr' fun α => forall_congr' fun hα => forall_congr' fun hαt => ?_
  rw [← pointStalkAbForgetIso_hom_app_geometricPointStalkMap]
  exact ⟨fun h => (ConcreteCategory.bijective_of_isIso
      ((pointStalkAbForgetIso B' U K hK g t R).hom.app M)).1 h, fun h => by rw [h]⟩

end Modules




end Stacks.EtaleCohomology

end
