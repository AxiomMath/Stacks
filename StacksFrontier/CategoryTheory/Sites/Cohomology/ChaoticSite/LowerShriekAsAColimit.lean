module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.PointMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.RingedPoint
import StacksCore.Tactic.StacksAttribute

/-!
# Lower shriek to a point as a colimit

Let `C` be a category with the chaotic topology and let `p : C ⥤ *` be the unique functor to
the one-object category, so that `π : Sh(C) ⟶ Sh(*)` is the point morphism
`Stacks.ChaoticSite.pointMorphism`. This file proves the identification
`π_! F = colim_{Cᵒᵖ} F` of [Stacks, Tag 08PF]: the inverse image along the point, the left
adjoint of restriction, is the colimit of the underlying presheaf.

## Main definitions

* `Stacks.ChaoticSite.abelianColimitLowerShriek`: the colimit functor to abelian sheaves on
  the point.
* `Stacks.ChaoticSite.pointConstEquiv`: presheaves on the one-object category are its
  coefficient category.
* `Stacks.ChaoticSite.presheafColimitStarAdjunction`: the presheaf-level adjunction, colimit
  against restriction along the point functor.

## Main results

* `Stacks.ChaoticSite.abelianLowerShriekColimitAdjunction`: the colimit functor is left
  adjoint to restriction along the point functor.
* `Stacks.ChaoticSite.abelianLowerShriekColimitIso`: the established inverse image
  `Functor.sheafPullback` along the point is the colimit functor, naturally in the sheaf.
* `Stacks.ChaoticSite.abelianLowerShriekColimitIso_unit`: that comparison carries the unit of
  the established lower shriek to the unit of the colimit adjunction.
* `Stacks.ChaoticSite.abelianLowerShriekColimit_evalIso` and
  `abelianLowerShriekColimit_unit_cocone`: the comparison evaluated at the point is the
  ordinary colimit, and the unit is the canonical colimit cocone.
* `Stacks.ChaoticSite.constantRingIso`: the inverse-image structure sheaf of the ringed point
  is restriction along the point functor, and
  `Stacks.ChaoticSite.moduleSheafEquivalence`: modules over it are diagrams of `B`-modules.

## Implementation notes

The adjunction is not built by hand. The presheaf-level adjunction `presheafColimitStarAdjunction`
composes `CategoryTheory.Limits.colimConstAdj` with the equivalence `pointConstEquiv`, and
`Adjunction.restrictFullyFaithful` then restricts it along `sheafToPresheaf` exactly as
Mathlib's own `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous` does, both
comparison isomorphisms being `Iso.refl`. For the chaotic topology every presheaf is a sheaf,
so `trivialHasSheafify` supplies sheafification and `isoSheafify` makes the unit of
sheafification invertible; that inverse is `abelianLowerShriekColimit_evalIso`.

Every *closed* object of `(Discrete PUnit)ᵒᵖ` is the point definitionally, by structure eta
through `Opposite`, `Discrete` and `PUnit`, and every morphism is the identity by proof
irrelevance. But two distinct *free variables* of that category are never unified, because eta
needs a constructor application on one side; so the naturality proofs here destructure the
objects (`obtain ⟨⟨⟨⟩⟩⟩ := X`) rather than appealing to `Functor.map_id` directly.

`s.C` and `s.fibredSituation.C` are two spellings of one type, and instance search runs at
`instances` transparency, which does not see through the `def` `fibredSituation`. The
finite-product and continuity instances are therefore seated once per spelling —
`pointPreservesFiniteProducts` for the `s.C` spelling and `pointPreservesFiniteProducts'` for
the other — and `constantRingIso` is stated in the `s.fibredSituation.C` spelling, which is the
one forced by the site of `constantRing s`.

The universes are independent: `C : Type u` with `Category.{v} C`, coefficients in
`AddCommGrpCat.{max w (u + 1) v}`, and a module universe `m` unrelated to the ring universe.

Stacks 08PF asserts the colimit formula for modules as well as for abelian sheaves, and that
half lives in the namespace `Stacks.ChaoticSite.ModuleValued`. It is these same constructions
instantiated at `A := ModuleCat s.B`, which is possible because `presheafColimitStarAdjunction`
and `trivialHasSheafify` are stated at a general coefficient category. Note that
`moduleColimitLowerShriek` below is the functor between `SheafOfModules` categories, a
different (equivalent, via `moduleSheafEquivalence`) object from
`ModuleValued.moduleColimitLowerShriek`, which is the one the colimit formula is stated for.

## References

* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08PE](https://stacks.math.columbia.edu/tag/08PE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.ChaoticSite

universe w v u u₂ v₂ m

section Point

variable (A : Type u₂) [Category.{v₂} A]

/-- A presheaf on the one-object category is the constant presheaf at its value at the
point: every object of `(Discrete PUnit)ᵒᵖ` is the point and every morphism is an identity,
both definitionally, so all components are identities. -/
def pointConstIso (F : (Discrete PUnit.{u + 1})ᵒᵖ ⥤ A) :
    (Functor.const (Discrete PUnit.{u + 1})ᵒᵖ).obj (F.obj (op ⟨⟨⟩⟩)) ≅ F :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {X Y} g => by
    obtain ⟨⟨⟨⟩⟩⟩ := X
    obtain ⟨⟨⟨⟩⟩⟩ := Y
    obtain rfl : g = 𝟙 _ := rfl
    simp)

/-- Every component of `pointConstIso` is the identity. -/
@[simp]
lemma pointConstIso_hom_app (F : (Discrete PUnit.{u + 1})ᵒᵖ ⥤ A)
    (X : (Discrete PUnit.{u + 1})ᵒᵖ) :
    (pointConstIso A F).hom.app X = 𝟙 (F.obj X) := rfl

/-- Presheaves on the one-object category are its coefficient category. -/
def pointConstEquiv : A ≌ ((Discrete PUnit.{u + 1})ᵒᵖ ⥤ A) where
  functor := Functor.const _
  inverse := (evaluation _ A).obj (op ⟨⟨⟩⟩)
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents (pointConstIso A) (by intros; ext; simp)
  functor_unitIso_comp := by intros; ext; simp

/-- The constant presheaf on the one-object category is left adjoint to evaluation. -/
def pointConstAdjunction :
    (Functor.const (Discrete PUnit.{u + 1})ᵒᵖ : A ⥤ _) ⊣
      (evaluation (Discrete PUnit.{u + 1})ᵒᵖ A).obj (op ⟨⟨⟩⟩) :=
  (pointConstEquiv A).toAdjunction

/-- The unit of `pointConstAdjunction` is the identity. -/
@[simp]
lemma pointConstAdjunction_unit_app (X : A) :
    (pointConstAdjunction A).unit.app X = 𝟙 X := rfl

/-- Restriction along the point functor is evaluation at the point followed by the constant
presheaf: both send a presheaf on the point to the constant presheaf at its value. -/
def starWhiskerIso (C : Type u) [Category.{v} C] :
    (evaluation (Discrete PUnit.{u + 1})ᵒᵖ A).obj (op ⟨⟨⟩⟩) ⋙ Functor.const Cᵒᵖ ≅
      (Functor.whiskeringLeft Cᵒᵖ ((Discrete PUnit.{u + 1})ᵒᵖ) A).obj (Functor.star C).op :=
  NatIso.ofComponents
    (fun Q => NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      exact (Q.map_id _).symm))
    (by intros; ext; simp)

/-- Every component of `starWhiskerIso` is the identity. -/
@[simp]
lemma starWhiskerIso_hom_app_app (C : Type u) [Category.{v} C]
    (Q : (Discrete PUnit.{u + 1})ᵒᵖ ⥤ A) (X : Cᵒᵖ) :
    ((starWhiskerIso A C).hom.app Q).app X = 𝟙 (Q.obj (op ⟨⟨⟩⟩)) := rfl

variable (C : Type u) [Category.{v} C] [HasColimitsOfShape Cᵒᵖ A]

/-- The colimit of a presheaf, read as a presheaf on the point, is left adjoint to
restriction along the point functor. -/
def presheafColimitStarAdjunction :
    ((colim : (Cᵒᵖ ⥤ A) ⥤ A) ⋙ Functor.const (Discrete PUnit.{u + 1})ᵒᵖ) ⊣
      (Functor.whiskeringLeft Cᵒᵖ ((Discrete PUnit.{u + 1})ᵒᵖ) A).obj (Functor.star C).op :=
  Adjunction.ofNatIsoRight (colimConstAdj.comp (pointConstAdjunction A)) (starWhiskerIso A C)

/-- The unit of `presheafColimitStarAdjunction` at a presheaf `P` and an object `X` is the
colimit coprojection `colimit.ι P X`. -/
@[simp]
lemma presheafColimitStarAdjunction_unit_app_app (P : Cᵒᵖ ⥤ A) (X : Cᵒᵖ) :
    ((presheafColimitStarAdjunction A C).unit.app P).app X = colimit.ι P X := by
  simp [presheafColimitStarAdjunction, Adjunction.comp_unit_app]
  rfl

end Point

/-- Every presheaf is a sheaf for the chaotic topology, so sheafification exists. -/
instance trivialHasSheafify (D : Type u) [Category.{v} D] (A : Type u₂) [Category.{v₂} A] :
    HasSheafify (GrothendieckTopology.trivial D) A := by
  rw [GrothendieckTopology.trivial_eq_bot]
  infer_instance

section Abelian

variable (C : Type u) [Category.{v} C]

/-- The point functor sends every object to the point. -/
lemma star_obj_eq (X : C) : (Functor.star.{u} C).obj X = Discrete.mk PUnit.unit := rfl

/-- **Stacks 08PF.** The colimit formula, regarded as a functor to abelian sheaves on the
point. -/
def abelianColimitLowerShriek :
    Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{max w (u + 1) v} ⥤
      Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
        AddCommGrpCat.{max w (u + 1) v} :=
  sheafToPresheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{max w (u + 1) v} ⋙
    (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max w (u + 1) v}) ⥤ AddCommGrpCat.{max w (u + 1) v}) ⋙
    (Functor.const (Discrete PUnit.{u + 1})ᵒᵖ) ⋙
    presheafToSheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
      AddCommGrpCat.{max w (u + 1) v}

/-- The colimit formula is the lower shriek of an abelian sheaf, naturally in the sheaf. -/
def abelianLowerShriekColimitAdjunction :
    abelianColimitLowerShriek.{w} C ⊣
      (Functor.star C).sheafPushforwardContinuous AddCommGrpCat.{max w (u + 1) v}
        (GrothendieckTopology.trivial C)
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) :=
  ((presheafColimitStarAdjunction AddCommGrpCat.{max w (u + 1) v} C).comp
      (sheafificationAdjunction (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
        AddCommGrpCat.{max w (u + 1) v})).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

/-- Pushforward of abelian sheaves along the point functor is a right adjoint. -/
instance pointAbelian_isRightAdjoint :
    ((Functor.star C).sheafPushforwardContinuous AddCommGrpCat.{max w (u + 1) v}
      (GrothendieckTopology.trivial C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).IsRightAdjoint :=
  (abelianLowerShriekColimitAdjunction.{w} C).isRightAdjoint

/-- **Stacks 08PF.** The established inverse image along the point, left adjoint to
restriction, is canonically the colimit functor. -/
@[stacks 08PF "lower_shriek_colimit"]
def abelianLowerShriekColimitIso :
    (Functor.star C).sheafPullback AddCommGrpCat.{max w (u + 1) v}
      (GrothendieckTopology.trivial C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) ≅
      abelianColimitLowerShriek.{w} C :=
  Adjunction.leftAdjointUniq
    ((Functor.star C).sheafAdjunctionContinuous AddCommGrpCat.{max w (u + 1) v}
      (GrothendieckTopology.trivial C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})))
    (abelianLowerShriekColimitAdjunction.{w} C)

/-- **Stacks 08PF.** The abelian comparison preserves the canonical unit. -/
@[stacks 08PF "lower_shriek_colimit"]
theorem abelianLowerShriekColimitIso_unit
    (F : Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{max w (u + 1) v}) :
    ((Functor.star C).sheafAdjunctionContinuous AddCommGrpCat.{max w (u + 1) v}
      (GrothendieckTopology.trivial C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).unit.app F ≫
      ((Functor.star C).sheafPushforwardContinuous AddCommGrpCat.{max w (u + 1) v}
        (GrothendieckTopology.trivial C)
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).map
          ((abelianLowerShriekColimitIso.{w} C).hom.app F) =
    (abelianLowerShriekColimitAdjunction.{w} C).unit.app F :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ F

/-- **Stacks 08PF.** At each object, the colimit presentation evaluated at the point is the
colimit of the underlying presheaf. -/
@[stacks 08PF "lower_shriek_colimit"]
def abelianLowerShriekColimit_evalIso
    (F : Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{max w (u + 1) v}) :
    ((abelianColimitLowerShriek.{w} C).obj F).obj.obj
      (op (Discrete.mk PUnit.unit)) ≅ colimit F.obj :=
  ((isoSheafify (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
      (P := (Functor.const (Discrete PUnit.{u + 1})ᵒᵖ).obj (colimit F.obj))
      (by
        simpa only [GrothendieckTopology.trivial_eq_bot] using
          Presheaf.isSheaf_bot
            ((Functor.const (Discrete PUnit.{u + 1})ᵒᵖ).obj (colimit F.obj)))).app
    (op (Discrete.mk PUnit.unit))).symm

/-- **Stacks 08PF.** At each object, the unit of the colimit presentation is the canonical
map into the colimit of the underlying presheaf. -/
@[stacks 08PF "lower_shriek_colimit"]
theorem abelianLowerShriekColimit_unit_cocone
    (F : Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{max w (u + 1) v}) (U : C) :
    ((abelianLowerShriekColimitAdjunction.{w} C).unit.app F).hom.app (op U) ≫
      (abelianLowerShriekColimit_evalIso.{w} C F).hom =
      colimit.ι F.obj (op U) := by
  have key := Adjunction.map_restrictFullyFaithful_unit_app
    (L := abelianColimitLowerShriek.{w} C)
    (R := (Functor.star C).sheafPushforwardContinuous AddCommGrpCat.{max w (u + 1) v}
      (GrothendieckTopology.trivial C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})))
    ((presheafColimitStarAdjunction AddCommGrpCat.{max w (u + 1) v} C).comp
      (sheafificationAdjunction (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
        AddCommGrpCat.{max w (u + 1) v}))
    (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _) F
  have h3 : ((abelianLowerShriekColimitAdjunction.{w} C).unit.app F).hom.app (op U)
      = colimit.ι F.obj (op U) ≫ (abelianLowerShriekColimit_evalIso.{w} C F).inv := by
    refine (congrArg (fun f => f.app (op U)) key).trans ?_
    simp [abelianLowerShriekColimit_evalIso, Adjunction.comp_unit_app]
    dsimp only [star_obj_eq]
    rfl
  refine (congrArg (fun g => g ≫ (abelianLowerShriekColimit_evalIso.{w} C F).hom) h3).trans ?_
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

-- This general law specifies the lower-shriek comparison on adjunction units.
add_to_stacks 08PF "lower_shriek_colimit"
  CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app
add_to_sga "4 IV 3.1.1" "partial" CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app

end Abelian

section Modules

variable (s : RingedPointSituation.{w, v, u})

/-- The structure sheaf of the ringed point, as a sheaf of rings. -/
abbrev pointRing :
    Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) RingCat.{max w u v} :=
  (sheafCompose (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
    (forget₂ CommRingCat.{max w u v} RingCat.{max w u v})).obj s.pointRingSheaf

/-- The constant structure sheaf of the ringed point situation, as a sheaf of rings. -/
abbrev constantRing :
    Sheaf s.fibredSituation.topology RingCat.{max w u v} :=
  (sheafCompose s.fibredSituation.topology
    (forget₂ CommRingCat.{max w u v} RingCat.{max w u v})).obj s.constantRingSheaf

/-- The point functor is continuous for the topology of the ringed point situation. -/
instance pointContinuous : (Functor.star s.C).IsContinuous s.fibredSituation.topology
    (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) :=
  s.fibredSituation.isContinuous

/-- Pushforward of sheaves of types along the point functor preserves finite products. -/
instance pointPreservesFiniteProducts : PreservesFiniteProducts
    ((Functor.star s.C).sheafPushforwardContinuous (Type (max w u v))
      s.fibredSituation.topology (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))) :=
  have h : PreservesFiniteProducts (s.fibredSituation.p.sheafPushforwardContinuous
      (Type (max w u v)) s.fibredSituation.topology s.fibredSituation.base.J) := inferInstance
  h

/-- The inverse image of the projection preserves finite products. -/
instance projPreservesFiniteProducts :
    PreservesFiniteProducts s.fibredSituation.projection.inverseImage :=
  have := s.fibredSituation.projection.preservesFiniteLimits
  inferInstance

/-- The point functor of `s.fibredSituation.C` is continuous. -/
instance pointContinuous' : (Functor.star s.fibredSituation.C).IsContinuous
    s.fibredSituation.topology (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) :=
  s.fibredSituation.isContinuous

/-- Pushforward of sheaves of types along the point functor of `s.fibredSituation.C`
preserves finite products. -/
instance pointPreservesFiniteProducts' : PreservesFiniteProducts
    ((Functor.star s.fibredSituation.C).sheafPushforwardContinuous (Type (max w u v))
      s.fibredSituation.topology (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))) :=
  have h : PreservesFiniteProducts (s.fibredSituation.p.sheafPushforwardContinuous
      (Type (max w u v)) s.fibredSituation.topology s.fibredSituation.base.J) := inferInstance
  h

/-- The canonical ring inverse image agrees with restriction along the point functor. -/
noncomputable def constantRingIso : constantRing s ≅
    ((Functor.star s.fibredSituation.C).sheafPushforwardContinuous RingCat.{max w u v}
      s.fibredSituation.topology
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).obj (pointRing s) := by
  let e : s.constantRingSheaf ≅
      ((Functor.star s.C).sheafPushforwardContinuous CommRingCat.{max w u v}
        s.fibredSituation.topology
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).obj s.pointRingSheaf := by
    have h : (⟨s.fibredSituation.projection.inverseImage, projPreservesFiniteProducts s⟩ :
          { H : _ ⥤ _ // PreservesFiniteProducts H }) =
        ⟨(Functor.star s.fibredSituation.C).sheafPushforwardContinuous (Type (max w u v))
          s.fibredSituation.topology (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})),
          pointPreservesFiniteProducts' s⟩ :=
      Subtype.ext s.fibredSituation.inducedProjection.inverseImage_eq
    let image : { H :
        Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) (Type (max w u v)) ⥤
          Sheaf s.fibredSituation.topology (Type (max w u v)) // PreservesFiniteProducts H } →
        Sheaf s.fibredSituation.topology CommRingCat.{max w u v} := fun H =>
      letI := H.property
      pullbackCommRingSheaf (K := GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
        s.fibredSituation.topology H.val s.fibredSituation.liftedBaseSheaf
    exact (eqToIso (congrArg image h) ≪≫
      restrictionCommRingIso s.fibredSituation.topology
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
        (Functor.star s.fibredSituation.C)
        s.fibredSituation.liftedBaseSheaf) ≪≫
      ((Functor.star s.fibredSituation.C).sheafPushforwardContinuous CommRingCat.{max w u v}
        s.fibredSituation.topology
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).mapIso
          s.pointRingSheafLiftIso
  exact (sheafCompose s.fibredSituation.topology
    (forget₂ CommRingCat.{max w u v} RingCat.{max w u v})).mapIso e

section ModuleTransport

variable (e : constantRing s ≅
  ((Functor.star s.fibredSituation.C).sheafPushforwardContinuous RingCat.{max w u v}
    s.fibredSituation.topology
    (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).obj (pointRing s))

/-- The diagram of `B`-modules underlying a module over the accepted constant ring sheaf. -/
noncomputable def modulePresheafOfIso : SheafOfModules.{m} (constantRing s) ⥤
    (s.Cᵒᵖ ⥤ ModuleCat.{m} s.B) where
  obj F :=
    let M := (PresheafOfModules.restrictScalars e.inv.hom).obj F.val
    { obj X := M.obj X
      map f := M.map f
      map_id X := by ext x; exact congrArg (fun f => f x) (M.map_id X)
      map_comp f g := by ext x; exact congrArg (fun f => f x) (M.map_comp f g) }
  map f :=
    { app X := (ModuleCat.restrictScalars (e.inv.hom.app X).hom).map
        (f.val.app X)
      naturality X Y g := by ext x; exact PresheafOfModules.naturality_apply f.val g x }
  map_id F := by ext X x; rfl
  map_comp f g := by ext X x; rfl

/-- A `B`-module regarded as a module sheaf on the ringed point. -/
noncomputable def pointModuleSheaf :
    ModuleCat.{m} s.B ⥤ SheafOfModules.{m} (pointRing s) where
  obj M :=
    { val := { obj _ := M, map _ := 𝟙 M }
      isSheaf := by
        have h (P : (Discrete PUnit.{u + 1})ᵒᵖ ⥤ AddCommGrpCat.{m}) :
            Presheaf.IsSheaf (GrothendieckTopology.trivial _) P := by
          simpa only [GrothendieckTopology.trivial_eq_bot] using Presheaf.isSheaf_bot P
        exact h _ }
  map f := { val := { app _ := f } }
  map_id F := by ext X x; rfl
  map_comp f g := by ext X x; rfl

/-- A diagram of `B`-modules, transported to the accepted inverse-image ring sheaf. -/
noncomputable def moduleSheafOfIso : (s.Cᵒᵖ ⥤ ModuleCat.{m} s.B) ⥤
    SheafOfModules.{m} (constantRing s) where
  obj F :=
    { val := (PresheafOfModules.restrictScalars e.hom.hom).obj
        { obj := F.obj
          map := F.map
          map_id X := by ext x; exact congrArg (fun f => f x) (F.map_id X)
          map_comp f g := by ext x; exact congrArg (fun f => f x) (F.map_comp f g) }
      isSheaf := by
        have h (P : s.Cᵒᵖ ⥤ AddCommGrpCat.{m}) :
            Presheaf.IsSheaf s.fibredSituation.topology P := by
          simp only [s.topology_eq_trivial, GrothendieckTopology.trivial_eq_bot]
          exact Presheaf.isSheaf_bot P
        exact h _ }
  map f :=
    { val := (PresheafOfModules.restrictScalars e.hom.hom).map
        { app := f.app
          naturality g := by ext x; exact congrArg (fun f => f x) (f.naturality g) } }
  map_id F := by ext X x; rfl
  map_comp f g := by ext X x; rfl

/-- Modules over the accepted constant ring sheaf are exactly diagrams of `B`-modules. -/
noncomputable def moduleSheafEquivalenceOfIso : SheafOfModules.{m} (constantRing s) ≌
    (s.Cᵒᵖ ⥤ ModuleCat.{m} s.B) where
  functor := modulePresheafOfIso s e
  inverse := moduleSheafOfIso s e
  unitIso := NatIso.ofComponents (fun F =>
    (SheafOfModules.fullyFaithfulForget _).preimageIso (PresheafOfModules.isoMk
      (fun X => (ModuleCat.restrictScalarsId _).symm.app (F.val.obj X) ≪≫
        ModuleCat.restrictScalarsComp'App
          (e.hom.hom.app X).hom
          (e.inv.hom.app X).hom (RingHom.id _)
          (by exact (congrArg (fun f => (f.hom.app X).hom)
            e.hom_inv_id).symm) (F.val.obj X))
      (by intro X Y f; ext x; rfl))) (by intro F G f; ext X x; rfl)
  counitIso := NatIso.ofComponents (fun F => NatIso.ofComponents
      (fun X => (ModuleCat.restrictScalarsComp'App
          (e.inv.hom.app X).hom
          (e.hom.hom.app X).hom (RingHom.id _)
          (by exact (congrArg (fun f => (f.hom.app X).hom)
            e.inv_hom_id).symm) (F.obj X)).symm ≪≫
        (ModuleCat.restrictScalarsId _).app (F.obj X))
      (by intro X Y f; ext x; rfl)) (by intro F G f; ext X x; rfl)
  functor_unitIso_comp F := by ext X x; rfl

end ModuleTransport

/-- A module sheaf on the ringed point is the constant one at its value at the point. -/
noncomputable def pointModuleSheafIso (F : SheafOfModules.{m} (pointRing s)) :
    (pointModuleSheaf s).obj (F.val.obj (op ⟨⟨⟩⟩)) ≅ F :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (fun {X Y} g => by
      obtain ⟨⟨⟨⟩⟩⟩ := X
      obtain ⟨⟨⟨⟩⟩⟩ := Y
      obtain rfl : g = 𝟙 _ := rfl
      ext x
      simp
      rfl))

/-- `B`-modules are exactly module sheaves on the ringed point. -/
noncomputable def pointModuleEquiv :
    ModuleCat.{m} s.B ≌ SheafOfModules.{m} (pointRing s) where
  functor := pointModuleSheaf s
  inverse := SheafOfModules.evaluation (pointRing s) (op ⟨⟨⟩⟩)
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents (pointModuleSheafIso s) (by
    intro F G f
    ext X x
    obtain ⟨⟨⟨⟩⟩⟩ := X
    rfl)
  functor_unitIso_comp := by
    intro M
    ext X x
    obtain ⟨⟨⟨⟩⟩⟩ := X
    rfl

/-- The underlying diagram of modules, using the canonical structure-sheaf comparison. -/
noncomputable abbrev modulePresheaf : SheafOfModules.{m} (constantRing s) ⥤
    (s.Cᵒᵖ ⥤ ModuleCat.{m} s.B) := modulePresheafOfIso s (constantRingIso s)

/-- Transport a diagram of modules to the accepted structure sheaf. -/
noncomputable abbrev moduleSheaf : (s.Cᵒᵖ ⥤ ModuleCat.{m} s.B) ⥤
    SheafOfModules.{m} (constantRing s) := moduleSheafOfIso s (constantRingIso s)

/-- The canonical equivalence with diagrams of `B`-modules. -/
noncomputable abbrev moduleSheafEquivalence : SheafOfModules.{m} (constantRing s) ≌
    (s.Cᵒᵖ ⥤ ModuleCat.{m} s.B) := moduleSheafEquivalenceOfIso s (constantRingIso s)

/-- The colimit of the underlying diagram of `B`-modules, as a module sheaf on the point. -/
noncomputable def moduleColimitLowerShriek :
    SheafOfModules.{max m u v} (constantRing s) ⥤
      SheafOfModules.{max m u v} (pointRing s) :=
  modulePresheaf s ⋙ colim ⋙ pointModuleSheaf s

end Modules

end Stacks.ChaoticSite
