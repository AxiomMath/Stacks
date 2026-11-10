module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.SkyscraperPushforward.Basic

/-!
# The inverse-image stalk comparison on germs, and the algebra structure on the stalk

The comparison `(f⁻¹F)_x ≅ F_{f(x)}` of `Stacks.SkyscraperPushforward.stalkSheafPullbackMateNatIso`
carries the germ at `f x` of a section `s` to the germ at `x` of the image of `s` under the unit of
the inverse-image/direct-image adjunction. For a morphism of schemes `g : T ⟶ S`, under this
comparison the stalk of `AlgebraicGeometry.inverseImageStructureMap g` is
`AlgebraicGeometry.Scheme.Hom.stalkMap`.

## Main results

* `Stacks.AlgebraPullbackQcoh.stalkSkyscraperSheafAdjunction_unit_app`: the sections of the unit
  of the stalk/skyscraper adjunction over an open containing the point are the germ map.
* `Stacks.AlgebraPullbackQcoh.germ_comp_skyscraperSheafAdjunction_unit`: a morphism out of a
  stalk, precomposed with a germ, read off the sections of its adjoint transpose.
* `Stacks.AlgebraPullbackQcoh.germ_stalkSheafPullbackMateNatIso`: the inverse-image stalk
  comparison on germs.
* `Stacks.AlgebraPullbackQcoh.stalkInverseImageMate_inverseImageStructureMap`: under the
  comparison, the stalk at `t` of `g⁻¹𝒪_S ⟶ 𝒪_T` is
  `AlgebraicGeometry.Scheme.Hom.stalkMap g t : 𝒪_{S,g(t)} ⟶ 𝒪_{T,t}`.
* `Stacks.AlgebraPullbackQcoh.germ_comp_inverseImageStructureMap`: the adjoint transpose of
  `inverseImageStructureMap` is the comorphism of `g`, on sections.

## Implementation notes

* `TopCat.Sheaf`, `TopCat.Sheaf.forget`, `TopCat.Presheaf.stalk` and the three skyscraper
  definitions are made implicitly reducible. Without them the goals below are not type-correct at
  implicit transparency — a germ has codomain `F.presheaf.stalk x` while an adjoint transpose has
  domain `(TopCat.Sheaf.forget ⋙ TopCat.Presheaf.stalkFunctor x).obj F`, and the skyscraper's
  value on an open is `(skyscraperPresheaf x c).obj (op V)` where the cast out of it is written
  `if x ∈ V then c else ⊤` — so every rewrite fails to build a motive.
* `Stacks.SkyscraperPushforward.stalkSheafPullbackMateNatIso` is built with
  `Classical.propDecidable` as a local instance; the same local instance is needed here, or the
  adjunctions named below are different terms from the ones that definition used.
* The two casts into the skyscraper's value are cancelled by `simp`, not by `rw`: they are
  produced at two different spellings of the same object, so `CategoryTheory.eqToHom_trans` does
  not match syntactically.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe v u

noncomputable section

namespace Stacks.AlgebraPullbackQcoh

section Skyscraper

attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] TopCat.Sheaf TopCat.Presheaf.stalk TopCat.Sheaf.forget
  skyscraperSheafFunctor skyscraperSheaf skyscraperPresheaf

variable {C : Type u} [Category.{v} C] [HasTerminal C] [HasColimits C] {X : TopCat.{v}}

/-- Over an open containing the point, the unit of the stalk/skyscraper adjunction is the germ map,
followed by the cast identifying the skyscraper's value with the stalk. -/
public theorem stalkSkyscraperSheafAdjunction_unit_app (x : X) (F : TopCat.Sheaf C X)
    (V : Opens X) (hV : x ∈ V) :
    ((stalkSkyscraperSheafAdjunction x).unit.app F).hom.app (op V) =
      TopCat.Presheaf.germ F.presheaf V x hV ≫ eqToHom (ite_eq_left hV).symm := by
  have key : ((stalkSkyscraperSheafAdjunction x).unit.app F).hom =
      (StalkSkyscraperPresheafAdjunctionAuxs.unit x).app F.presheaf := rfl
  rw [key]
  refine (dite_eq_left hV).trans ?_
  simp only [Functor.id_obj, unop_op, Category.id_comp]

/-- Over an open containing the point, the sections of the unit of the stalk/skyscraper
adjunction, followed by the cast out of the skyscraper's value, are the germ map. -/
public theorem stalkSkyscraperSheafAdjunction_unit_app_comp (x : X) (F : TopCat.Sheaf C X)
    (V : Opens X) (hV : x ∈ V) :
    ((stalkSkyscraperSheafAdjunction x).unit.app F).hom.app (op V) ≫
        eqToHom (ite_eq_left hV) =
      TopCat.Presheaf.germ F.presheaf V x hV := by
  rw [stalkSkyscraperSheafAdjunction_unit_app x F V hV]
  simp

/-- For `ψ : F_x ⟶ c` the composite of the germ over an open containing `x` with `ψ` is the
sections of the adjoint transpose `F ⟶ skyscraperSheaf x c`, followed by the cast out of the
skyscraper's value. -/
public theorem germ_comp_skyscraperSheafAdjunction_unit (x : X) (F : TopCat.Sheaf C X) (c : C)
    (ψ : (TopCat.Sheaf.forget C X ⋙ TopCat.Presheaf.stalkFunctor C x).obj F ⟶ c)
    (V : Opens X) (hV : x ∈ V) :
    TopCat.Presheaf.germ F.presheaf V x hV ≫ ψ =
      ((stalkSkyscraperSheafAdjunction x).unit.app F ≫
          (skyscraperSheafFunctor x).map ψ).hom.app (op V) ≫ eqToHom (ite_eq_left hV) := by
  change _ = (((stalkSkyscraperSheafAdjunction x).unit.app F).hom.app (op V) ≫
    (SkyscraperPresheafFunctor.map' x ψ).app (op V)) ≫ eqToHom (ite_eq_left hV)
  rw [stalkSkyscraperSheafAdjunction_unit_app x F V hV]
  have h3 : (SkyscraperPresheafFunctor.map' x ψ).app (op V) =
      eqToHom (ite_eq_left hV) ≫ ψ ≫ eqToHom (ite_eq_left hV).symm := dite_eq_left hV
  rw [h3]
  simp

end Skyscraper

section StalkPullback

attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] TopCat.Sheaf TopCat.Presheaf.stalk TopCat.Sheaf.forget
  skyscraperSheafFunctor skyscraperSheaf skyscraperPresheaf

variable (A : Type u) [Category.{v} A] {FA : A → A → Type*} {CA : A → Type v}
variable [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{v} A FA] [HasColimits A]
variable [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]
variable {X Y : TopCat.{v}}

/-- The comparison `F_{f(x)} ≅ (f⁻¹F)_x` of
`Stacks.SkyscraperPushforward.stalkSheafPullbackMateNatIso` carries the germ at `f x` of a section
of `F` over `V` to the germ at `x` of its image under the unit of the inverse-image/direct-image
adjunction, a section of `f⁻¹F` over `f⁻¹V`. -/
public theorem germ_stalkSheafPullbackMateNatIso (f : X ⟶ Y) (x : X) (F : TopCat.Sheaf A Y)
    (V : Opens Y) (hV : f x ∈ V) :
    TopCat.Presheaf.germ F.presheaf V (f x) hV ≫
        (Stacks.SkyscraperPushforward.stalkSheafPullbackMateNatIso A f x).hom.app F =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction A f).unit.app F).hom.app (op V) ≫
        TopCat.Presheaf.germ ((TopCat.Sheaf.pullback A f).obj F).presheaf
          ((Opens.map f).obj V) x hV := by
  have h : (TopCat.Sheaf.pullbackPushforwardAdjunction A f).unit.app F ≫
        (TopCat.Sheaf.pushforward A f).map
          ((stalkSkyscraperSheafAdjunction x).unit.app ((TopCat.Sheaf.pullback A f).obj F)) =
      (stalkSkyscraperSheafAdjunction (f x)).unit.app F ≫
        (skyscraperSheafFunctor (f x)).map
          ((Stacks.SkyscraperPushforward.stalkSheafPullbackMateNatIso A f x).hom.app F) :=
    (Adjunction.comp_unit_app (TopCat.Sheaf.pullbackPushforwardAdjunction A f)
          (stalkSkyscraperSheafAdjunction x) F).symm.trans
      ((Category.comp_id _).symm.trans
        (unit_conjugateEquiv_symm
          ((TopCat.Sheaf.pullbackPushforwardAdjunction A f).comp
            (stalkSkyscraperSheafAdjunction x))
          (stalkSkyscraperSheafAdjunction (f x))
          (Stacks.SkyscraperPushforward.skyscraperSheafPushforwardIso f x).hom F))
  rw [germ_comp_skyscraperSheafAdjunction_unit (f x) F _
    ((Stacks.SkyscraperPushforward.stalkSheafPullbackMateNatIso A f x).hom.app F) V hV, ← h]
  have h2 : ((TopCat.Sheaf.pullbackPushforwardAdjunction A f).unit.app F ≫
        (TopCat.Sheaf.pushforward A f).map
          ((stalkSkyscraperSheafAdjunction x).unit.app
            ((TopCat.Sheaf.pullback A f).obj F))).hom.app (op V) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction A f).unit.app F).hom.app (op V) ≫
        ((stalkSkyscraperSheafAdjunction x).unit.app
          ((TopCat.Sheaf.pullback A f).obj F)).hom.app (op ((Opens.map f).obj V)) := rfl
  rw [h2]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun m => ((TopCat.Sheaf.pullbackPushforwardAdjunction A f).unit.app F).hom.app
        (op V) ≫ m)
      (stalkSkyscraperSheafAdjunction_unit_app_comp x ((TopCat.Sheaf.pullback A f).obj F)
        ((Opens.map f).obj V) hV))

end StalkPullback

section Schemes

attribute [local implicit_reducible] TopCat.Sheaf TopCat.Presheaf.stalk TopCat.Sheaf.forget

variable {T S : Scheme.{u}} (g : T ⟶ S) (t : T)

/-- On sections over an open `V` of `S`, the unit of the inverse-image/direct-image adjunction
followed by the structural map is `g.c` over `V`. -/
public theorem germ_comp_inverseImageStructureMap (V : S.Opens) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).unit.app
          S.sheaf).hom.app (op V) ≫
        (AlgebraicGeometry.inverseImageStructureMap g).hom.app
          (op ((Opens.map g.base).obj V)) =
      g.c.app (op V) := by
  have h : (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).homEquiv
      S.sheaf T.sheaf (AlgebraicGeometry.inverseImageStructureMap g) =
      (⟨g.c⟩ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj T.sheaf) :=
    Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun φ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj
    T.sheaf => φ.hom.app (op V)) h

attribute [local instance] Classical.propDecidable

/-- Under `Stacks.SkyscraperPushforward.stalkSheafPullbackMateNatIso`, the stalk at `t` of the
structural map `g⁻¹𝒪_S ⟶ 𝒪_T` of `AlgebraicGeometry.inverseImageStructureMap` is Mathlib's
`AlgebraicGeometry.Scheme.Hom.stalkMap g t : 𝒪_{S,g(t)} ⟶ 𝒪_{T,t}`. -/
public theorem stalkInverseImageMate_inverseImageStructureMap :
    (Stacks.SkyscraperPushforward.stalkSheafPullbackMateNatIso CommRingCat.{u} g.base t).hom.app
          S.sheaf ≫
        (TopCat.Presheaf.stalkFunctor CommRingCat.{u} t).map
          (AlgebraicGeometry.inverseImageStructureMap g).hom =
      g.stalkMap t := by
  refine TopCat.Presheaf.stalk_hom_ext S.sheaf.presheaf fun V hV => ?_
  rw [← Category.assoc, germ_stalkSheafPullbackMateNatIso CommRingCat.{u} g.base t S.sheaf V hV]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun m => ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      g.base).unit.app S.sheaf).hom.app (op V) ≫ m)
    (TopCat.Presheaf.stalkFunctor_map_germ ((Opens.map g.base).obj V) t hV
      (AlgebraicGeometry.inverseImageStructureMap g).hom)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun m => m ≫ TopCat.Presheaf.germ T.sheaf.presheaf
      ((Opens.map g.base).obj V) t hV) (germ_comp_inverseImageStructureMap g V)).trans ?_
  exact (g.germ_stalkMap V t hV).symm

end Schemes

end Stacks.AlgebraPullbackQcoh

end

end
