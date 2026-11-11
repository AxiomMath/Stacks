module

public import StacksFrontier.CategoryTheory.Sites.Topos.StructureAdjunction
public import Mathlib.CategoryTheory.Category.Pointed
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Morphisms of topoi and sheaves of pointed sets

Let `f = (f⁻¹, f_*)` be a morphism of topoi `Sh(C) → Sh(D)`. A sheaf of pointed sets is the same
thing as a sheaf of sets `F` together with a global section, i.e. a morphism `* ⟶ F` from the
final sheaf `*`. Since `f⁻¹` is left exact, `f⁻¹ *` is final, so `f⁻¹` of a pointed sheaf `(F, p)`
is pointed by `* ≅ f⁻¹ * ⟶ f⁻¹ F`; likewise `f_*` of `(G, q)` is pointed by `* ⟶ f_* * ⟶ f_* G`.
The unit and the counit of `f⁻¹ ⊣ f_*` preserve these points, because any two morphisms into a
final sheaf agree, so the adjunction on sheaves of sets restricts to an adjunction on sheaves of
pointed sets. This is case (1) of the proposition that morphisms of topoi preserve algebraic
structure.

## Main definitions

* `Stacks.Topos.pointedSheafPoint`: the distinguished global section of a sheaf of pointed sets,
  as a morphism from the final sheaf of sets.
* `Stacks.Topos.pointedSheafMk`: a sheaf of sets with a global section, as a sheaf of pointed
  sets.
* `Stacks.Topos.pointedSheafHomMk`: a morphism of underlying sheaves of sets preserving the
  points, as a morphism of sheaves of pointed sets.
* `Stacks.Topos.pointedLift`: a functor of sheaves of sets together with a pointing of the image
  of the final sheaf, as a functor of sheaves of pointed sets.
* `Stacks.Topos.pointedStructureAdjunction`: the adjoint pair `f⁻¹ ⊣ f_*` on sheaves of pointed
  sets, compatible with taking underlying sheaves of sets.

## Main results

* `Pointed.reflectsLimitsOfSize_forget`: the forgetful functor of pointed sets reflects limits of
  every size. It is what makes `pointedSheafMk` a sheaf for an arbitrary site.

## Implementation notes

The final sheaf of sets is `CategoryTheory.Sheaf.terminal` of the terminal type `PUnit`, so that
the point of a sheaf of pointed sets over an object `X` is its value at the unique element of
`PUnit`. With this choice the underlying sheaf of sets of `f⁻¹ F`, resp. `f_* G`, is *equal* to
`f⁻¹`, resp. `f_*`, of the underlying sheaf of sets, and the two comparison isomorphisms of
`Stacks.Topos.StructureAdjunction` are identities.

## References

* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public section

open CategoryTheory Limits

universe w v u v' u' a b

namespace Pointed

/-- The forgetful functor `Pointed ⥤ Type` reflects limits of every size: if the underlying
cone of types of a cone of pointed sets is a limit, the induced map of the underlying types
sends the point to the point, because both have the same projections. -/
instance reflectsLimitsOfSize_forget : ReflectsLimitsOfSize.{a, b} (forget Pointed.{w}) where
  reflectsLimitsOfShape {_} _ :=
    { reflectsLimit :=
        { reflects {c} hc :=
            have key (x y : c.pt) (h : ∀ j, (c.π.app j).toFun x = (c.π.app j).toFun y) : x = y :=
              (Types.isLimitEquivSections hc).injective (Subtype.ext (funext h))
            ⟨{ lift s :=
                { toFun := hc.lift ((forget Pointed.{w}).mapCone s)
                  map_point := key _ _ fun j ↦
                    (ConcreteCategory.congr_hom (hc.fac ((forget Pointed.{w}).mapCone s) j)
                      s.pt.point).trans
                      ((s.π.app j).map_point.trans (c.π.app j).map_point.symm) }
               fac s j := Pointed.Hom.ext (funext fun x ↦
                 ConcreteCategory.congr_hom (hc.fac ((forget Pointed.{w}).mapCone s) j) x)
               uniq s m hm := Pointed.Hom.ext (funext fun x ↦ ConcreteCategory.congr_hom
                 (hc.uniq ((forget Pointed.{w}).mapCone s) (TypeCat.ofHom m.toFun)
                   fun j ↦ ConcreteCategory.hom_ext _ _ fun y ↦
                     congrFun (congrArg Pointed.Hom.toFun (hm j)) y) x) }⟩ } }

end Pointed

namespace Stacks.Topos

section PointedSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget Pointed.{w})]

/-- The distinguished global section of a sheaf of pointed sets, as a morphism from the final
sheaf of sets to its underlying sheaf of sets. -/
def pointedSheafPoint (F : Sheaf J Pointed.{w}) :
    Sheaf.terminal J Types.isTerminalPUnit.{w} ⟶ (sheafCompose J (forget Pointed.{w})).obj F :=
  ObjectProperty.homMk
    { app X := TypeCat.ofHom fun _ ↦ (F.obj.obj X).point
      naturality _ _ g := ConcreteCategory.hom_ext _ _ fun _ ↦ (F.obj.map g).map_point.symm }

/-- A morphism of sheaves of pointed sets preserves the distinguished global sections. -/
@[reassoc (attr := simp)]
lemma pointedSheafPoint_comp {F G : Sheaf J Pointed.{w}} (φ : F ⟶ G) :
    pointedSheafPoint F ≫ (sheafCompose J (forget Pointed.{w})).map φ = pointedSheafPoint G :=
  Sheaf.hom_ext (NatTrans.ext (funext fun X ↦
    ConcreteCategory.hom_ext _ _ fun _ ↦ (φ.hom.app X).map_point))

/-- A sheaf of sets `G` with a global section `p`, as a sheaf of pointed sets: the point over
`X` is the value of `p` over `X`. Its underlying sheaf of sets is `G` itself. -/
def pointedSheafMk (G : Sheaf J (Type w)) (p : Sheaf.terminal J Types.isTerminalPUnit.{w} ⟶ G) :
    Sheaf J Pointed.{w} where
  obj :=
    { obj X := ⟨G.obj.obj X, p.hom.app X PUnit.unit⟩
      map g := ⟨G.obj.map g, (ConcreteCategory.congr_hom (p.hom.naturality g) PUnit.unit).symm⟩
      map_id X := Pointed.Hom.ext (funext fun x ↦ ConcreteCategory.congr_hom (G.obj.map_id X) x)
      map_comp f g := Pointed.Hom.ext
        (funext fun x ↦ ConcreteCategory.congr_hom (G.obj.map_comp f g) x) }
  property := Presheaf.isSheaf_of_isSheaf_comp J _ (forget Pointed.{w}) G.property

/-- The distinguished global section of `pointedSheafMk G p` is `p`. -/
@[simp]
lemma pointedSheafPoint_pointedSheafMk (G : Sheaf J (Type w))
    (p : Sheaf.terminal J Types.isTerminalPUnit.{w} ⟶ G) :
    pointedSheafPoint (pointedSheafMk G p) = p :=
  rfl

/-- A morphism of the underlying sheaves of sets of two sheaves of pointed sets which carries
the distinguished global section to the distinguished global section, as a morphism of sheaves
of pointed sets. -/
def pointedSheafHomMk {F G : Sheaf J Pointed.{w}}
    (φ : (sheafCompose J (forget Pointed.{w})).obj F ⟶ (sheafCompose J (forget Pointed.{w})).obj G)
    (h : pointedSheafPoint F ≫ φ = pointedSheafPoint G) : F ⟶ G :=
  ObjectProperty.homMk
    { app X := ⟨φ.hom.app X,
        ConcreteCategory.congr_hom (congrArg (fun ψ ↦ ψ.hom.app X) h) PUnit.unit⟩
      naturality _ _ g := Pointed.Hom.ext
        (funext fun x ↦ ConcreteCategory.congr_hom (φ.hom.naturality g) x) }

/-- The underlying morphism of sheaves of sets of `pointedSheafHomMk φ h` is `φ`. -/
@[simp]
lemma sheafCompose_map_pointedSheafHomMk {F G : Sheaf J Pointed.{w}}
    (φ : (sheafCompose J (forget Pointed.{w})).obj F ⟶ (sheafCompose J (forget Pointed.{w})).obj G)
    (h : pointedSheafPoint F ≫ φ = pointedSheafPoint G) :
    (sheafCompose J (forget Pointed.{w})).map (pointedSheafHomMk φ h) = φ :=
  rfl

end PointedSheaf

section PointedLift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget Pointed.{w})] [K.HasSheafCompose (forget Pointed.{w})]

variable (Φ : Sheaf K (Type w) ⥤ Sheaf J (Type w))
  (t : Sheaf.terminal J Types.isTerminalPUnit.{w} ⟶
    Φ.obj (Sheaf.terminal K Types.isTerminalPUnit.{w}))

/-- The image of a sheaf of pointed sets `(F, p)` under a functor `Φ` of sheaves of sets, pointed
by `t ≫ Φ p` for a morphism `t` from the final sheaf to `Φ` of the final sheaf. -/
def pointedLiftObj (F : Sheaf K Pointed.{w}) : Sheaf J Pointed.{w} :=
  pointedSheafMk (Φ.obj ((sheafCompose K (forget Pointed.{w})).obj F))
    (t ≫ Φ.map (pointedSheafPoint F))

/-- The image of a morphism of sheaves of pointed sets under a functor `Φ` of sheaves of sets:
`Φ` of the underlying morphism of sheaves of sets, which preserves the points. -/
def pointedLiftMap {F G : Sheaf K Pointed.{w}} (φ : F ⟶ G) :
    pointedLiftObj Φ t F ⟶ pointedLiftObj Φ t G :=
  pointedSheafHomMk (Φ.map ((sheafCompose K (forget Pointed.{w})).map φ)) (by
    have e : (t ≫ Φ.map (pointedSheafPoint F)) ≫ Φ.map ((sheafCompose K _).map φ) =
        t ≫ Φ.map (pointedSheafPoint G) := by
      rw [Category.assoc, ← Φ.map_comp, pointedSheafPoint_comp]
    exact e)

/-- A functor `Φ` of sheaves of sets together with a morphism `t` from the final sheaf to `Φ` of
the final sheaf gives a functor of sheaves of pointed sets: `(F, p)` goes to `Φ F` pointed by
`t ≫ Φ p`. -/
def pointedLift : Sheaf K Pointed.{w} ⥤ Sheaf J Pointed.{w} where
  obj := pointedLiftObj Φ t
  map := pointedLiftMap Φ t
  map_id F := (sheafCompose J (forget Pointed.{w})).map_injective
    (((congrArg Φ.map ((sheafCompose K (forget Pointed.{w})).map_id F)).trans
      (Φ.map_id _)).trans
        ((sheafCompose J (forget Pointed.{w})).map_id (pointedLiftObj Φ t F)).symm)
  map_comp φ ψ := (sheafCompose J (forget Pointed.{w})).map_injective
    (((congrArg Φ.map ((sheafCompose K (forget Pointed.{w})).map_comp φ ψ)).trans
      (Φ.map_comp _ _)).trans
        ((sheafCompose J (forget Pointed.{w})).map_comp (pointedLiftMap Φ t φ)
          (pointedLiftMap Φ t ψ)).symm)

/-- The underlying morphism of sheaves of sets of `pointedLift Φ t` of a morphism is `Φ` of its
underlying morphism of sheaves of sets. -/
@[simp]
lemma sheafCompose_map_pointedLift_map {F G : Sheaf K Pointed.{w}} (φ : F ⟶ G) :
    (sheafCompose J (forget Pointed.{w})).map ((pointedLift Φ t).map φ) =
      Φ.map ((sheafCompose K (forget Pointed.{w})).map φ) :=
  rfl

/-- The underlying sheaf of sets of `pointedLift Φ t` of a sheaf of pointed sets is `Φ` of its
underlying sheaf of sets; the identification is the identity. -/
def pointedLiftCompForgetIso :
    pointedLift Φ t ⋙ sheafCompose J (forget Pointed.{w}) ≅
      sheafCompose K (forget Pointed.{w}) ⋙ Φ :=
  NatIso.ofComponents (fun F ↦ Iso.refl (Φ.obj ((sheafCompose K (forget Pointed.{w})).obj F)))
    (fun φ ↦ (Category.comp_id _).trans
      ((sheafCompose_map_pointedLift_map Φ t φ).trans (Category.id_comp _).symm))

/-- The components of `pointedLiftCompForgetIso` are identities. -/
@[simp]
lemma pointedLiftCompForgetIso_hom_app (F : Sheaf K Pointed.{w}) :
    (pointedLiftCompForgetIso Φ t).hom.app F =
      𝟙 (Φ.obj ((sheafCompose K (forget Pointed.{w})).obj F)) :=
  rfl

end PointedLift

section Adjunction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))

/-- The inverse image of the final sheaf along a morphism of topoi is final, since the inverse
image is left exact. -/
noncomputable def isTerminalInverseImageTerminal :
    IsTerminal (f.inverseImage.obj (Sheaf.terminal K Types.isTerminalPUnit.{w})) :=
  haveI := f.preservesFiniteLimits
  (Sheaf.isTerminalTerminal K Types.isTerminalPUnit.{w}).isTerminalObj f.inverseImage

/-- The pointing of `f⁻¹` of the final sheaf: the unique morphism from the final sheaf. -/
noncomputable def inverseImageTerminalPoint :
    Sheaf.terminal J Types.isTerminalPUnit.{w} ⟶
      f.inverseImage.obj (Sheaf.terminal K Types.isTerminalPUnit.{w}) :=
  (isTerminalInverseImageTerminal f).from _

/-- The pointing of `f_*` of the final sheaf: the unit of `f⁻¹ ⊣ f_*` at the final sheaf
followed by `f_*` of the unique morphism `f⁻¹ * ⟶ *`. -/
def pushforwardTerminalPoint :
    Sheaf.terminal K Types.isTerminalPUnit.{w} ⟶
      f.pushforward.obj (Sheaf.terminal J Types.isTerminalPUnit.{w}) :=
  (f.adj.unit.app (Sheaf.terminal K Types.isTerminalPUnit.{w}) :
      Sheaf.terminal K Types.isTerminalPUnit.{w} ⟶
        f.pushforward.obj (f.inverseImage.obj (Sheaf.terminal K Types.isTerminalPUnit.{w}))) ≫
    f.pushforward.map ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit.{w}).from _)

variable [J.HasSheafCompose (forget Pointed.{w})] [K.HasSheafCompose (forget Pointed.{w})]

/-- The inverse image of sheaves of pointed sets along a morphism of topoi. -/
noncomputable abbrev pointedInverseImage : Sheaf K Pointed.{w} ⥤ Sheaf J Pointed.{w} :=
  pointedLift f.inverseImage (inverseImageTerminalPoint f)

/-- The direct image of sheaves of pointed sets along a morphism of topoi. -/
noncomputable abbrev pointedPushforward : Sheaf J Pointed.{w} ⥤ Sheaf K Pointed.{w} :=
  pointedLift f.pushforward (pushforwardTerminalPoint f)

/-- The unit of `f⁻¹ ⊣ f_*` at the underlying sheaf of sets of a sheaf of pointed sets preserves
the points, hence is a morphism of sheaves of pointed sets. -/
noncomputable def pointedUnitApp (F : Sheaf K Pointed.{w}) :
    F ⟶ (pointedPushforward f).obj ((pointedInverseImage f).obj F) :=
  pointedSheafHomMk (f.adj.unit.app ((sheafCompose K (forget Pointed.{w})).obj F)) (by
    have e₀ : (Sheaf.isTerminalTerminal J Types.isTerminalPUnit.{w}).from _ ≫
        inverseImageTerminalPoint f = 𝟙 _ :=
      (isTerminalInverseImageTerminal f).hom_ext _ _
    have e : pointedSheafPoint F ≫ (f.adj.unit.app ((sheafCompose K (forget Pointed.{w})).obj F) :
          (sheafCompose K (forget Pointed.{w})).obj F ⟶
            f.pushforward.obj (f.inverseImage.obj ((sheafCompose K (forget Pointed.{w})).obj F))) =
        pushforwardTerminalPoint f ≫ f.pushforward.map
          (inverseImageTerminalPoint f ≫ f.inverseImage.map (pointedSheafPoint F)) := by
      rw [show pointedSheafPoint F ≫
            (f.adj.unit.app ((sheafCompose K (forget Pointed.{w})).obj F) :
              (sheafCompose K (forget Pointed.{w})).obj F ⟶ f.pushforward.obj
                (f.inverseImage.obj ((sheafCompose K (forget Pointed.{w})).obj F))) =
          (f.adj.unit.app (Sheaf.terminal K Types.isTerminalPUnit.{w}) :
            Sheaf.terminal K Types.isTerminalPUnit.{w} ⟶
              f.pushforward.obj (f.inverseImage.obj (Sheaf.terminal K Types.isTerminalPUnit.{w}))) ≫
            f.pushforward.map (f.inverseImage.map (pointedSheafPoint F)) from
          f.adj.unit.naturality _, pushforwardTerminalPoint, Category.assoc,
        ← f.pushforward.map_comp, ← Category.assoc, e₀, Category.id_comp]
    exact e)

/-- The counit of `f⁻¹ ⊣ f_*` at the underlying sheaf of sets of a sheaf of pointed sets
preserves the points, hence is a morphism of sheaves of pointed sets. -/
noncomputable def pointedCounitApp (G : Sheaf J Pointed.{w}) :
    (pointedInverseImage f).obj ((pointedPushforward f).obj G) ⟶ G :=
  pointedSheafHomMk (f.adj.counit.app ((sheafCompose J (forget Pointed.{w})).obj G)) (by
    have e₀ : inverseImageTerminalPoint f ≫ f.inverseImage.map (pushforwardTerminalPoint f) ≫
        (f.adj.counit.app (Sheaf.terminal J Types.isTerminalPUnit.{w}) :
          f.inverseImage.obj (f.pushforward.obj (Sheaf.terminal J Types.isTerminalPUnit.{w})) ⟶
            Sheaf.terminal J Types.isTerminalPUnit.{w}) = 𝟙 _ :=
      (Sheaf.isTerminalTerminal J Types.isTerminalPUnit.{w}).hom_ext _ _
    have e : (inverseImageTerminalPoint f ≫ f.inverseImage.map
        (pushforwardTerminalPoint f ≫ f.pushforward.map (pointedSheafPoint G))) ≫
          (f.adj.counit.app ((sheafCompose J (forget Pointed.{w})).obj G) :
            f.inverseImage.obj (f.pushforward.obj ((sheafCompose J (forget Pointed.{w})).obj G)) ⟶
              (sheafCompose J (forget Pointed.{w})).obj G) =
        pointedSheafPoint G := by
      rw [Category.assoc, Functor.map_comp, Category.assoc,
        show f.inverseImage.map (f.pushforward.map (pointedSheafPoint G)) ≫
            (f.adj.counit.app ((sheafCompose J (forget Pointed.{w})).obj G) :
              f.inverseImage.obj (f.pushforward.obj ((sheafCompose J (forget Pointed.{w})).obj G)) ⟶
                (sheafCompose J (forget Pointed.{w})).obj G) =
          (f.adj.counit.app (Sheaf.terminal J Types.isTerminalPUnit.{w}) :
            f.inverseImage.obj (f.pushforward.obj (Sheaf.terminal J Types.isTerminalPUnit.{w})) ⟶
              Sheaf.terminal J Types.isTerminalPUnit.{w}) ≫ pointedSheafPoint G from
          f.adj.counit.naturality _,
        reassoc_of% e₀]
    exact e)

/-- The adjunction `f⁻¹ ⊣ f_*` on sheaves of pointed sets: its unit and counit are those of the
adjunction on sheaves of sets. -/
noncomputable def pointedAdjunction : pointedInverseImage f ⊣ pointedPushforward f where
  unit :=
    { app := pointedUnitApp f
      naturality F G φ := (sheafCompose K (forget Pointed.{w})).map_injective
        (((sheafCompose K (forget Pointed.{w})).map_comp φ (pointedUnitApp f G)).trans
          ((f.adj.unit.naturality ((sheafCompose K (forget Pointed.{w})).map φ)).trans
            ((sheafCompose K (forget Pointed.{w})).map_comp (pointedUnitApp f F)
              ((pointedPushforward f).map ((pointedInverseImage f).map φ))).symm)) }
  counit :=
    { app := pointedCounitApp f
      naturality F G φ := (sheafCompose J (forget Pointed.{w})).map_injective
        (((sheafCompose J (forget Pointed.{w})).map_comp
            ((pointedInverseImage f).map ((pointedPushforward f).map φ))
            (pointedCounitApp f G)).trans
          ((f.adj.counit.naturality ((sheafCompose J (forget Pointed.{w})).map φ)).trans
            ((sheafCompose J (forget Pointed.{w})).map_comp (pointedCounitApp f F) φ).symm)) }
  left_triangle_components F := (sheafCompose J (forget Pointed.{w})).map_injective
    ((((sheafCompose J (forget Pointed.{w})).map_comp
        ((pointedInverseImage f).map (pointedUnitApp f F))
        (pointedCounitApp f ((pointedInverseImage f).obj F))).trans
      (f.adj.left_triangle_components ((sheafCompose K (forget Pointed.{w})).obj F))).trans
      ((sheafCompose J (forget Pointed.{w})).map_id ((pointedInverseImage f).obj F)).symm)
  right_triangle_components G := (sheafCompose K (forget Pointed.{w})).map_injective
    ((((sheafCompose K (forget Pointed.{w})).map_comp
        (pointedUnitApp f ((pointedPushforward f).obj G))
        ((pointedPushforward f).map (pointedCounitApp f G))).trans
      (f.adj.right_triangle_components ((sheafCompose J (forget Pointed.{w})).obj G))).trans
      ((sheafCompose K (forget Pointed.{w})).map_id ((pointedPushforward f).obj G)).symm)

/-- The underlying morphism of sheaves of sets of the unit of `pointedAdjunction f` is the unit
of `f⁻¹ ⊣ f_*` on sheaves of sets. -/
@[simp]
lemma sheafCompose_map_pointedAdjunction_unit_app (F : Sheaf K Pointed.{w}) :
    (sheafCompose K (forget Pointed.{w})).map ((pointedAdjunction f).unit.app F) =
      f.adj.unit.app ((sheafCompose K (forget Pointed.{w})).obj F) :=
  rfl

/-- The underlying morphism of sheaves of sets of the counit of `pointedAdjunction f` is the
counit of `f⁻¹ ⊣ f_*` on sheaves of sets. -/
@[simp]
lemma sheafCompose_map_pointedAdjunction_counit_app (G : Sheaf J Pointed.{w}) :
    (sheafCompose J (forget Pointed.{w})).map ((pointedAdjunction f).counit.app G) =
      f.adj.counit.app ((sheafCompose J (forget Pointed.{w})).obj G) :=
  rfl

/-- A morphism of topoi `f` gives an adjoint pair `f⁻¹ ⊣ f_*` on sheaves of pointed sets,
compatible with taking underlying sheaves of sets: the underlying sheaf of sets of `f⁻¹ F`,
resp. `f_* G`, is `f⁻¹`, resp. `f_*`, of the underlying sheaf of sets, and the unit is the unit
of the adjunction on sheaves of sets. -/
noncomputable def pointedStructureAdjunction : StructureAdjunction f (forget Pointed.{w}) where
  inverseImage := pointedInverseImage f
  pushforward := pointedPushforward f
  adj := pointedAdjunction f
  inverseImageForgetIso := pointedLiftCompForgetIso _ _
  pushforwardForgetIso := pointedLiftCompForgetIso _ _
  forget_map_unit_app F := by
    have e : f.adj.unit.app ((sheafCompose K (forget Pointed.{w})).obj F) ≫ 𝟙 _ ≫
        f.pushforward.map (𝟙 _) = f.adj.unit.app ((sheafCompose K (forget Pointed.{w})).obj F) := by
      simp
    exact e

end Adjunction

end Stacks.Topos
