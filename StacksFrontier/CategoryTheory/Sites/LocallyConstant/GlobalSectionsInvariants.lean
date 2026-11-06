module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DegreeZero.GaloisInvariants
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianFiniteGModules
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteModuleSheafScalarAction

/-!
# Global sections of a finite locally constant sheaf are the invariants of its `G`-module

Let `(C, J)` be a site with a terminal object `T`, let `G` be a topological group and let `e`
be an equivalence between the finite locally constant sheaves of sets on `C` and the finite
continuous `G`-sets. Through the transport of commutative group objects
`Stacks.ConstantSheaf.finiteLocallyConstantAbelianEquivalenceOfSetEquivalence`, `e` attaches a
finite discrete `G`-module to every finite locally constant abelian sheaf `ℱ`. This file proves
that the global sections `ℱ(T)` are the `G`-invariants of that module, naturally in `ℱ`.

## Main definitions

* `Stacks.ConstantSheaf.sheafSectionsEquivHomTerminal` — a section over a terminal object of a
  sheaf of sets is a morphism from the terminal sheaf.
* `AlgebraicGeometry.ContinuousGSet.finitePoint` — the one-point finite continuous `G`-set,
  a terminal object of the finite continuous `G`-sets.
* `CategoryTheory.ContinuousGAddCommGrp.finiteInvariants` — the invariants of a finite discrete
  `G`-module, as a functor to abelian groups.
* `Stacks.ConstantSheaf.finiteLocallyConstantAbelianSectionsIsoInvariants` — the natural
  isomorphism `ℱ(T) ≅ (E ℱ)^G` of abelian-group-valued functors.

## Implementation notes

The argument is Yoneda's at the terminal object, carried out on the underlying sets, which is
where the equivalence `e` acts. A section over `T` is a morphism from the terminal sheaf; the
terminal sheaf is finite locally constant, being a finite limit of such (Tag 093U (1)), so `e`
moves that morphism to one out of `e(⋆)`, which is terminal because `e` is an equivalence, hence
isomorphic to the one-point `G`-set; and a morphism out of the one-point `G`-set is a fixed
point. The finite `G`-set underlying the discrete `G`-module attached to `ℱ` is `e` of the sheaf
of sets underlying `ℱ` on the nose
(`Stacks.ConstantSheaf.finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_forgetAction`), so
this is a natural bijection between the underlying sets of two abelian-group-valued functors.
Such a bijection is additive, by `CategoryTheory.natIsoOfForgetAddCommGrpCat`, since the finite
locally constant abelian sheaves have binary biproducts.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u v u'

namespace Stacks.ConstantSheaf

section Terminal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {T : C}

/-- The sheaf of sets with one-point values. -/
def pointSheaf : Sheaf J (Type w) where
  obj :=
    { obj := fun _ ↦ PUnit.{w + 1}
      map := fun _ ↦ 𝟙 _ }
  property := (isSheaf_iff_isSheaf_of_type J _).2 fun _ _ _ _ _ ↦
    ⟨PUnit.unit, fun _ _ _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- The point of a value of the sheaf with one-point values. -/
def pointSheafPt (U : Cᵒᵖ) : (pointSheaf.{w} J).obj.obj U := PUnit.unit

/-- Every element of a value of the sheaf with one-point values is its point. -/
theorem eq_pointSheafPt {U : Cᵒᵖ} (x : (pointSheaf.{w} J).obj.obj U) : x = pointSheafPt J U :=
  rfl

/-- The sheaf with one-point values is terminal. -/
def isTerminalPointSheaf : IsTerminal (pointSheaf.{w} J) :=
  IsTerminal.ofUniqueHom (fun _ ↦ ⟨{ app := fun _ ↦ TypeCat.ofHom fun _ ↦ PUnit.unit }⟩)
    (fun _ _ ↦ by ext; rfl)

/-- The morphism from the terminal sheaf attached to a section over a terminal object: it
restricts the section to every object. -/
def homTerminalOfSection (hT : IsTerminal T) (H : Sheaf J (Type w)) (s : H.obj.obj (op T)) :
    pointSheaf.{w} J ⟶ H :=
  ⟨{ app := fun U ↦ TypeCat.ofHom fun _ ↦ H.obj.map (hT.from U.unop).op s
     naturality := fun U V f ↦ by
       ext x
       change H.obj.map (hT.from V.unop).op s = H.obj.map f (H.obj.map (hT.from U.unop).op s)
       rw [← Functor.map_comp_apply,
         show (hT.from U.unop).op ≫ f = (hT.from V.unop).op from
           Quiver.Hom.unop_inj (hT.hom_ext _ _)] }⟩

/-- The component of `homTerminalOfSection` at `U` sends the point to the restriction of the
section to `U`. -/
theorem homTerminalOfSection_app (hT : IsTerminal T) (H : Sheaf J (Type w))
    (s : H.obj.obj (op T)) (U : Cᵒᵖ) (x : (pointSheaf.{w} J).obj.obj U) :
    (homTerminalOfSection J hT H s).hom.app U x = H.obj.map (hT.from U.unop).op s :=
  rfl

/-- **A section over a terminal object of a sheaf of sets is a morphism from the terminal
sheaf.** -/
def sheafSectionsEquivHomTerminal (hT : IsTerminal T) (H : Sheaf J (Type w)) :
    H.obj.obj (op T) ≃ (pointSheaf.{w} J ⟶ H) where
  toFun := homTerminalOfSection J hT H
  invFun φ := φ.hom.app (op T) (pointSheafPt J (op T))
  left_inv s := by
    change (homTerminalOfSection J hT H s).hom.app (op T) (pointSheafPt J (op T)) = s
    rw [homTerminalOfSection_app, hT.hom_ext (hT.from T) (𝟙 T), op_id,
      Functor.map_id_apply]
  right_inv φ := by
    ext U x
    change (homTerminalOfSection J hT H (φ.hom.app (op T) (pointSheafPt J (op T)))).hom.app U x =
      φ.hom.app U x
    rw [homTerminalOfSection_app, eq_pointSheafPt J x]
    exact (NatTrans.naturality_apply φ.hom (hT.from U.unop).op (pointSheafPt J (op T))).symm

/-- The bijection `sheafSectionsEquivHomTerminal` is natural in the sheaf. -/
theorem sheafSectionsEquivHomTerminal_naturality (hT : IsTerminal T) {H H' : Sheaf J (Type w)}
    (f : H ⟶ H') (s : H.obj.obj (op T)) :
    sheafSectionsEquivHomTerminal J hT H' (f.hom.app (op T) s) =
      sheafSectionsEquivHomTerminal J hT H s ≫ f := by
  ext U x
  show (homTerminalOfSection J hT H' (f.hom.app (op T) s)).hom.app U x =
    f.hom.app U ((homTerminalOfSection J hT H s).hom.app U x)
  rw [homTerminalOfSection_app, homTerminalOfSection_app]
  exact (NatTrans.naturality_apply f.hom (hT.from U.unop).op s).symm

end Terminal

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

section PointGSet

variable (G : Type u') [Group G] [TopologicalSpace G]

attribute [local instance] discreteForget₂Type

/-- The one-point continuous `G`-set. -/
def ContinuousGSet.point : ContinuousGSet.{u', w} G := by
  let A : Action (Type w) G :=
    { V := PUnit.{w + 1}
      ρ := 1 }
  refine ⟨⟨A, ?_⟩, ⟨rfl⟩⟩
  have : DiscreteTopology ((forget₂ (Action (Type w) G) TopCat).obj A) := ⟨rfl⟩
  exact (Action.isContinuous_def A).2 <|
    continuous_prod_of_discrete_right.mpr fun _ ↦ continuous_const

/-- The one-point continuous `G`-set, as a finite continuous `G`-set. -/
def ContinuousGSet.finitePoint : (ContinuousGSet.isFinite.{u', w} G).FullSubcategory :=
  ⟨ContinuousGSet.point.{w, u'} G, (inferInstance : Finite PUnit.{w + 1})⟩

/-- The point of the one-point continuous `G`-set. -/
def ContinuousGSet.finitePointPt : (ContinuousGSet.finitePoint.{w, u'} G).obj.obj.obj.V :=
  PUnit.unit

/-- The one-point finite continuous `G`-set is terminal. -/
def ContinuousGSet.isTerminalFinitePoint :
    IsTerminal (ContinuousGSet.finitePoint.{w, u'} G) :=
  IsTerminal.ofUniqueHom
    (fun _ ↦ ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
      { hom := TypeCat.ofHom fun _ ↦ ContinuousGSet.finitePointPt G
        comm := fun _ ↦ rfl })))
    (fun _ _ ↦ by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply Action.Hom.ext
      ext x
      rfl)

variable {G}

/-- The fixed points of a continuous `G`-set. -/
def ContinuousGSet.fixedPoints (M : ContinuousGSet.{u', w} G) : Set M.obj.obj.V :=
  {x | ∀ g : G, M.obj.obj.ρ g x = x}

/-- **A morphism out of the one-point `G`-set is a fixed point.** -/
def ContinuousGSet.homFinitePointEquiv (M : (ContinuousGSet.isFinite.{u', w} G).FullSubcategory) :
    (ContinuousGSet.finitePoint.{w, u'} G ⟶ M) ≃ ContinuousGSet.fixedPoints M.obj where
  toFun f := ⟨f.hom.hom.hom.hom (ContinuousGSet.finitePointPt G), fun g ↦
    (ConcreteCategory.congr_hom (f.hom.hom.hom.comm g) (ContinuousGSet.finitePointPt G)).symm⟩
  invFun x := ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := TypeCat.ofHom fun _ ↦ x.1
      comm := fun g ↦ by
        ext
        exact (x.2 g).symm }))
  left_inv f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext y
    rfl
  right_inv x := rfl

/-- The bijection `ContinuousGSet.homFinitePointEquiv` is natural in the `G`-set. -/
theorem ContinuousGSet.homFinitePointEquiv_naturality
    {M M' : (ContinuousGSet.isFinite.{u', w} G).FullSubcategory}
    (f : ContinuousGSet.finitePoint.{w, u'} G ⟶ M) (h : M ⟶ M') :
    (ContinuousGSet.homFinitePointEquiv M' (f ≫ h)).1 =
      h.hom.hom.hom.hom (ContinuousGSet.homFinitePointEquiv M f).1 :=
  rfl

end PointGSet

end AlgebraicGeometry

namespace CategoryTheory

variable (G : Type u') [Group G] [TopologicalSpace G]

/-- **The invariants of a finite discrete `G`-module**, as a functor to abelian groups. -/
def ContinuousGAddCommGrp.finiteInvariants :
    (ContinuousGAddCommGrp.isFinite.{u', w} G).FullSubcategory ⥤ AddCommGrpCat.{w} where
  obj M := AddCommGrpCat.of M.obj.obj.obj.addInvariants
  map f := AddCommGrpCat.ofHom
    { toFun := fun x ↦ ⟨f.hom.hom.hom.hom x.1, fun g ↦
        (ConcreteCategory.congr_hom (f.hom.hom.hom.comm g) x.1).symm.trans
          (congrArg _ (x.2 g))⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ ↦ Subtype.ext (map_add _ _ _) }

end CategoryTheory

namespace Stacks.ConstantSheaf

section SectionsInvariants

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The terminal sheaf of sets, as a finite locally constant sheaf of sets: a finite limit of
finite locally constant sheaves of sets is one (Tag 093U (1)), and this is the empty limit. -/
def finiteLocallyConstantPointSheaf :
    (isFiniteLocallyConstantSetSheaf.{v, u, w} J).FullSubcategory :=
  ⟨pointSheaf J, (isFiniteLocallyConstantSetSheaf.{v, u, w} J).prop_of_isLimit
    (isTerminalPointSheaf J) (fun j ↦ j.as.elim)⟩

/-- The terminal sheaf of sets is terminal among the finite locally constant ones. -/
def isTerminalFiniteLocallyConstantPointSheaf :
    IsTerminal (finiteLocallyConstantPointSheaf.{w} J) :=
  IsTerminal.ofUniqueHom (fun X ↦ ObjectProperty.homMk ((isTerminalPointSheaf J).from X.obj))
    (fun _ _ ↦ ObjectProperty.hom_ext _ ((isTerminalPointSheaf J).hom_ext _ _))

variable {T : C} (hT : IsTerminal T) (G : Type u') [Group G] [TopologicalSpace G]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
  (e : (isFiniteLocallyConstantSetSheaf.{v, u, u} J).FullSubcategory ≌
    (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).FullSubcategory)

/-- `e` carries the terminal sheaf to the one-point `G`-set. -/
def equivalencePointSheafIso :
    e.functor.obj (finiteLocallyConstantPointSheaf J) ≅
      AlgebraicGeometry.ContinuousGSet.finitePoint.{max u v, u'} G :=
  ((isTerminalFiniteLocallyConstantPointSheaf J).isTerminalObj e.functor).uniqueUpToIso
    (AlgebraicGeometry.ContinuousGSet.isTerminalFinitePoint G)

/-- The sections over the terminal object of a finite locally constant abelian sheaf, as fixed
points of the finite `G`-set that `e` attaches to its underlying sheaf of sets. -/
def sectionsEquivFixedPoints
    (F : (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory) :
    F.obj.obj.obj (op T) ≃ AlgebraicGeometry.ContinuousGSet.fixedPoints
      (e.functor.obj ((forgetFiniteLocallyConstantAbelianSheaf J).obj F)).obj :=
  (sheafSectionsEquivHomTerminal J hT
      ((forgetFiniteLocallyConstantAbelianSheaf J).obj F).obj).trans <|
    ((ObjectProperty.fullyFaithfulι _).homEquiv (X := finiteLocallyConstantPointSheaf.{u} J)
        (Y := (forgetFiniteLocallyConstantAbelianSheaf J).obj F)).symm.trans <|
      e.fullyFaithfulFunctor.homEquiv.trans <|
        ((equivalencePointSheafIso J G e).homCongr (Iso.refl _)).trans
          (AlgebraicGeometry.ContinuousGSet.homFinitePointEquiv _)

/-- The bijection `sectionsEquivFixedPoints` is natural in the sheaf. -/
theorem sectionsEquivFixedPoints_naturality
    {F F' : (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory} (f : F ⟶ F')
    (s : F.obj.obj.obj (op T)) :
    (sectionsEquivFixedPoints J hT G e F' (f.hom.hom.app (op T) s)).1 =
      (e.functor.map ((forgetFiniteLocallyConstantAbelianSheaf J).map f)).hom.hom.hom.hom
        (sectionsEquivFixedPoints J hT G e F s).1 := by
  have h := sheafSectionsEquivHomTerminal_naturality J hT
    ((forgetFiniteLocallyConstantAbelianSheaf J).map f).hom s
  show (AlgebraicGeometry.ContinuousGSet.homFinitePointEquiv _
      ((equivalencePointSheafIso J G e).inv ≫ e.functor.map (ObjectProperty.homMk
        (sheafSectionsEquivHomTerminal J hT _
          (((forgetFiniteLocallyConstantAbelianSheaf J).map f).hom.hom.app (op T) s))) ≫
        𝟙 _)).1 = _
  rw [h]
  have key : (equivalencePointSheafIso J G e).inv ≫
      e.functor.map (ObjectProperty.homMk (X := finiteLocallyConstantPointSheaf J)
        (Y := (forgetFiniteLocallyConstantAbelianSheaf J).obj F')
        (sheafSectionsEquivHomTerminal J hT _ s ≫
          ((forgetFiniteLocallyConstantAbelianSheaf J).map f).hom)) ≫ 𝟙 _ =
      ((equivalencePointSheafIso J G e).inv ≫
        e.functor.map (ObjectProperty.homMk (sheafSectionsEquivHomTerminal J hT _ s)) ≫ 𝟙 _) ≫
        e.functor.map ((forgetFiniteLocallyConstantAbelianSheaf J).map f) := by
    simp only [Category.comp_id, Category.assoc, ← e.functor.map_comp]
    rfl
  exact (congrArg (fun φ ↦ (AlgebraicGeometry.ContinuousGSet.homFinitePointEquiv _ φ).1)
    key).trans (AlgebraicGeometry.ContinuousGSet.homFinitePointEquiv_naturality _ _)

/-- The abelian group of sections over the terminal object, as a functor on the finite locally
constant abelian sheaves. -/
abbrev finiteLocallyConstantAbelianSections :
    (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory ⥤ AddCommGrpCat.{max u v} :=
  ObjectProperty.ι _ ⋙ sheafToPresheaf J _ ⋙ (CategoryTheory.evaluation _ _).obj (op T)

variable [HasPullbacks C] in
/-- **Global sections of a finite locally constant abelian sheaf are the invariants of the
finite discrete `G`-module attached to it**, naturally in the sheaf. Here `e` is an equivalence
of the finite locally constant sheaves of sets with the finite continuous `G`-sets, the module
is the one of `Stacks.ConstantSheaf.finiteLocallyConstantAbelianEquivalenceOfSetEquivalence`,
and the sections are taken over a terminal object `T` of the site. -/
def finiteLocallyConstantAbelianSectionsIsoInvariants :
    (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor ⋙
        ContinuousGAddCommGrp.finiteInvariants G ≅
      finiteLocallyConstantAbelianSections J (T := T) :=
  haveI : HasBinaryBiproducts (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory :=
    HasBinaryBiproducts.of_hasBinaryProducts
  natIsoOfForgetAddCommGrpCat <| Iso.symm <| NatIso.ofComponents
    (fun F ↦ (sectionsEquivFixedPoints J hT G e F).toIso) (fun {F F'} f ↦ by
      ext s
      exact Subtype.ext (sectionsEquivFixedPoints_naturality J hT G e f s))

end SectionsInvariants

end Stacks.ConstantSheaf
