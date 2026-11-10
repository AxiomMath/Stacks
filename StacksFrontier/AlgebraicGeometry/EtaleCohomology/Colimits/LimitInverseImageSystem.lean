module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitSiteBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.UniversalPullbackSystem
-- the levels of the canonical system of Stacks 0EYL are indexed by `Iᵒᵖ` itself; the body of
-- `affineEtaleSiteColimit` is needed to see it
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.ColimitSite

/-!
# The inverse images of a sheaf on the bottom level, on the sites of Stacks 0EYL

Let `I` be a directed set with a least element `⊥`, let `(X_i)` be an inverse system of schemes
over `I` with affine transition morphisms and let `X = lim X_i`. For a sheaf `F` on Mathlib's small
étale site of `X_⊥`, the inverse images `f_i⁻¹F` along the morphisms `f_i : X_i ⟶ X_⊥`, restricted
to the strict small models of Stacks 0EYL (`Stacks.EtaleCohomology.LimitSiteBridge`), are the
system of inverse images of the restriction of `F` in the sense of
`Stacks.WeakSites.PullbackSystem`, and the restriction of the inverse image of `F` to `X` is its
colimit on the site of the limit.

The inverse image is any left adjoint of the direct image of sheaves along base change, so the
statements apply to sheaves of sets and to abelian sheaves, with the inverse image functors the
library uses for each.

## Main definitions

* `bottom`, `bottom_isTerminal`: the level of `X_⊥`, terminal in the index of the system.
* `levelRestrict`, `limitRestrict`: restriction of sheaves to a level and to the site of the limit.
* `levelSheaf`, `levelε`, `limitε`: the restricted inverse images and their universal arrows.

## Main results

* `isUniversalArrow_levelε`, `existsUnique_limitε`: the universal properties.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u w'' w'

namespace Stacks.EtaleCohomology.LimitSiteBridge

open Stacks.EtaleCohomology.AffineLimitCohomology Stacks.WeakSites.PullbackSystem

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [OrderBot I]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-- The level of the system modelling `X_⊥`. -/
@[no_expose]
def bottom : (sys D c B hD hX hc).I := (op ⊥ : Iᵒᵖ)

/-- `op ⊥` is terminal in `Iᵒᵖ`. -/
def opBot_isTerminal : IsTerminal (op (⊥ : I)) :=
  IsTerminal.ofUniqueHom (fun Y => (homOfLE (bot_le : ⊥ ≤ Y.unop)).op)
    (fun _ _ => Subsingleton.elim _ _)

/-- The level of `X_⊥` is terminal in the index of the system. -/
@[no_expose]
def bottom_isTerminal : IsTerminal (bottom D c B hD hX hc) :=
  opBot_isTerminal (I := I)

section Generic

variable (A : Type w'') [Category.{w'} A]
  [∀ (i : (sys D c B hD hX hc).I) (Y : (lvl D c B hD hX hc i).Etaleᵒᵖ),
    HasLimitsOfShape (StructuredArrow Y (levelToEtale D c B hD hX hc i).op) A]
  [∀ Y : c.pt.Etaleᵒᵖ, HasLimitsOfShape (StructuredArrow Y (limitToEtale D c B hX).op) A]

/-- Restriction of sheaves on `X_i` to the level `i`: an equivalence. -/
abbrev levelRestrict (i : (sys D c B hD hX hc).I) :
    Sheaf (lvl D c B hD hX hc i).smallEtaleTopology A ⥤ Sheaf ((sys D c B hD hX hc).J i) A :=
  (levelToEtale D c B hD hX hc i).sheafPushforwardContinuous A _ _

/-- Restriction of sheaves on `X` to the raised small affine étale site of `X`: an equivalence. -/
abbrev limitRestrict :
    Sheaf c.pt.smallEtaleTopology A ⥤ Sheaf (limitSitePrecoverage D c B hX).toGrothendieck A :=
  (limitToEtale D c B hX).sheafPushforwardContinuous A _ _

/-- The morphism `f_i : X_i ⟶ X_⊥` from the scheme modelled by the bottom level. -/
abbrev toBottom (i : (sys D c B hD hX hc).I) :
    lvl D c B hD hX hc i ⟶ lvl D c B hD hX hc (bottom D c B hD hX hc) :=
  lvlMap D c B hD hX hc ((bottom_isTerminal D c B hD hX hc).from i)

/-- The morphism from the scheme modelled by a level to `X_⊥` itself. -/
abbrev toBot (i : (sys D c B hD hX hc).I) : lvl D c B hD hX hc i ⟶ D.obj (op ⊥) :=
  D.map ((opBot_isTerminal (I := I)).from (idx D c B hD hX hc i))

/-- The scheme modelled by the bottom level is `X_⊥`. -/
theorem lvl_bottom : lvl D c B hD hX hc (bottom D c B hD hX hc) = D.obj (op ⊥) := by
  change D.obj (op ⊥) = D.obj (op ⊥)
  rfl

/-- The morphism from a level to `X_⊥` factors through `f_i` and the morphism of the bottom
level. -/
theorem toBot_eq (i : (sys D c B hD hX hc).I) :
    toBot D c B hD hX hc i =
      toBottom D c B hD hX hc i ≫ toBot D c B hD hX hc (bottom D c B hD hX hc) := by
  rw [← D.map_comp]
  exact congrArg D.map (Subsingleton.elim _ _)

/-- The morphisms to `X_⊥` are compatible with the transition morphisms of the system. -/
theorem toBot_lvlMap {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) :
    toBot D c B hD hX hc j = lvlMap D c B hD hX hc a ≫ toBot D c B hD hX hc i := by
  rw [← D.map_comp]
  exact congrArg D.map (Subsingleton.elim _ _)

/-- The direct image along `f_i`, restricted to the bottom level, is the direct image along the
transition of the system of the restriction to the level `i`. -/
def levelPushforwardIso (i : (sys D c B hD hX hc).I) :
    (smallEtaleBaseChange (toBottom D c B hD hX hc i)).sheafPushforwardContinuous A _ _ ⋙
        levelRestrict D c B hD hX hc A (bottom D c B hD hX hc) ≅
      levelRestrict D c B hD hX hc A i ⋙
        (letI := (sys D c B hD hX hc).continuous ((bottom_isTerminal D c B hD hX hc).from i)
        ((sys D c B hD hX hc).u
          ((bottom_isTerminal D c B hD hX hc).from i)).sheafPushforwardContinuous A _ _) :=
  letI := (sys D c B hD hX hc).continuous ((bottom_isTerminal D c B hD hX hc).from i)
  letI := Functor.isContinuous_comp (levelToEtale D c B hD hX hc (bottom D c B hD hX hc))
    (smallEtaleBaseChange (toBottom D c B hD hX hc i)) ((sys D c B hD hX hc).J _)
    (lvl D c B hD hX hc (bottom D c B hD hX hc)).smallEtaleTopology
    (lvl D c B hD hX hc i).smallEtaleTopology
  letI := Functor.isContinuous_comp
    ((sys D c B hD hX hc).u ((bottom_isTerminal D c B hD hX hc).from i))
    (levelToEtale D c B hD hX hc i) ((sys D c B hD hX hc).J _) ((sys D c B hD hX hc).J i)
    (lvl D c B hD hX hc i).smallEtaleTopology
  Functor.sheafPushforwardContinuousComp' (Iso.refl _) A _ _ _ ≪≫
    Functor.sheafPushforwardContinuousIso
      (transitionBaseChangeIso D c B hD hX hc ((bottom_isTerminal D c B hD hX hc).from i)).symm
      A _ _ ≪≫
    (Functor.sheafPushforwardContinuousComp' (Iso.refl _) A _ _ _).symm

/-- The direct image along the projection `X ⟶ X_⊥`, restricted to the bottom level, is the
direct image along the functor to the site of the limit of the restriction to that site. -/
def limitPushforwardIso :
    (smallEtaleBaseChange (lvlπ D c B hD hX hc (bottom D c B hD hX hc))).sheafPushforwardContinuous
        A _ _ ⋙ levelRestrict D c B hD hX hc A (bottom D c B hD hX hc) ≅
      limitRestrict D c B hX A ⋙
        (letI : (toLimitSmall D c B hD hX hc (bottom D c B hD hX hc)).IsContinuous
            ((sys D c B hD hX hc).J _) (limitSitePrecoverage D c B hX).toGrothendieck :=
          toLimitSmall_isContinuous D c B hD hX hc _
        (toLimitSmall D c B hD hX hc (bottom D c B hD hX hc)).sheafPushforwardContinuous A _ _) :=
  letI : (toLimitSmall D c B hD hX hc (bottom D c B hD hX hc)).IsContinuous
      ((sys D c B hD hX hc).J _) (limitSitePrecoverage D c B hX).toGrothendieck :=
    toLimitSmall_isContinuous D c B hD hX hc _
  letI := Functor.isContinuous_comp (levelToEtale D c B hD hX hc (bottom D c B hD hX hc))
    (smallEtaleBaseChange (lvlπ D c B hD hX hc (bottom D c B hD hX hc))) ((sys D c B hD hX hc).J _)
    (lvl D c B hD hX hc (bottom D c B hD hX hc)).smallEtaleTopology c.pt.smallEtaleTopology
  letI := Functor.isContinuous_comp (toLimitSmall D c B hD hX hc (bottom D c B hD hX hc))
    (limitToEtale D c B hX) ((sys D c B hD hX hc).J _)
    (limitSitePrecoverage D c B hX).toGrothendieck c.pt.smallEtaleTopology
  Functor.sheafPushforwardContinuousComp' (Iso.refl _) A _ _ _ ≪≫
    Functor.sheafPushforwardContinuousIso
      (toLimitBaseChangeIso D c B hD hX hc (bottom D c B hD hX hc)).symm A _ _ ≪≫
    (Functor.sheafPushforwardContinuousComp' (Iso.refl _) A _ _ _).symm

/-! ### Restricted inverse images for an arbitrary inverse-image functor -/

variable {D c B hD hX hc A} (L : ∀ i : (sys D c B hD hX hc).I,
    Sheaf (lvl D c B hD hX hc (bottom D c B hD hX hc)).smallEtaleTopology A ⥤
      Sheaf (lvl D c B hD hX hc i).smallEtaleTopology A)
  (adj : ∀ i, L i ⊣ (smallEtaleBaseChange (toBottom D c B hD hX hc i)).sheafPushforwardContinuous
    A _ _)
  (F : Sheaf (lvl D c B hD hX hc (bottom D c B hD hX hc)).smallEtaleTopology A)

/-- The universal arrow of the restricted inverse image `(L i) F`, for an arbitrary left adjoint
`L i` of the direct image: the restriction of the unit, read through `levelPushforwardIso`. -/
def levelεOf (i : (sys D c B hD hX hc).I) :
    ((levelRestrict D c B hD hX hc A (bottom D c B hD hX hc)).obj F).obj ⟶
      ((sys D c B hD hX hc).u ((bottom_isTerminal D c B hD hX hc).from i)).op ⋙
        ((levelRestrict D c B hD hX hc A i).obj ((L i).obj F)).obj :=
  ((levelRestrict D c B hD hX hc A (bottom D c B hD hX hc)).map ((adj i).unit.app F) ≫
    (levelPushforwardIso D c B hD hX hc A i).hom.app ((L i).obj F)).hom

omit [∀ Y : c.pt.Etaleᵒᵖ, HasLimitsOfShape (StructuredArrow Y (limitToEtale D c B hX).op) A] in
/-- `levelεOf` is a universal arrow. -/
theorem isUniversalArrow_levelεOf (i : (sys D c B hD hX hc).I) :
    IsUniversalArrow (sys D c B hD hX hc) (bottom_isTerminal D c B hD hX hc)
      (F := fun i => (levelRestrict D c B hD hX hc A i).obj ((L i).obj F))
      (levelεOf L adj F) i := by
  intro M g
  let := (sys D c B hD hX hc).continuous ((bottom_isTerminal D c B hD hX hc).from i)
  obtain ⟨h, hh, hu⟩ := existsUnique_of_adjunction (adj i)
    (levelRestrict D c B hD hX hc A i).asEquivalence
    (Functor.FullyFaithful.ofFullyFaithful
      (levelRestrict D c B hD hX hc A (bottom D c B hD hX hc)))
    (((sys D c B hD hX hc).u ((bottom_isTerminal D c B hD hX hc).from i)).sheafPushforwardContinuous
      A _ _)
    (levelPushforwardIso D c B hD hX hc A i) F M (ObjectProperty.homMk g)
  exact ⟨h, congrArg (fun φ => φ.hom) hh, fun h' hh' => hu h' (Sheaf.hom_ext hh')⟩

end Generic

/-! ### The abelian case -/

section Abelian

variable {D c B hD hX hc} (F : Sheaf (lvl D c B hD hX hc (bottom D c B hD hX hc)).smallEtaleTopology
  Ab.{max u v + 1})

/-- The inverse image `f_i⁻¹F` of `F` to `X_i`. -/
abbrev levelInverseImage (i : (sys D c B hD hX hc).I) :
    Sheaf (lvl D c B hD hX hc i).smallEtaleTopology Ab.{max u v + 1} :=
  (etaleAbelianInverseImage.{max u v, 0} (toBottom D c B hD hX hc i)).obj F

/-- The restriction of `f_i⁻¹F` to the level `i`. -/
abbrev levelSheaf (i : (sys D c B hD hX hc).I) :
    Sheaf ((sys D c B hD hX hc).J i) Ab.{max u v + 1} :=
  (levelRestrict D c B hD hX hc Ab.{max u v + 1} i).obj (levelInverseImage F i)

/-- The universal arrow of the restricted inverse image: the restriction of the adjunction unit
`F ⟶ f_{i,*}f_i⁻¹F`, read through `levelPushforwardIso`. -/
def levelε (i : (sys D c B hD hX hc).I) :
    ((levelRestrict D c B hD hX hc Ab.{max u v + 1} (bottom D c B hD hX hc)).obj F).obj ⟶
      ((sys D c B hD hX hc).u ((bottom_isTerminal D c B hD hX hc).from i)).op ⋙
        (levelSheaf F i).obj :=
  ((levelRestrict D c B hD hX hc Ab.{max u v + 1} (bottom D c B hD hX hc)).map
      ((etaleAbelianInverseImageDirectImageAdj.{max u v, 0}
        (toBottom D c B hD hX hc i)).unit.app F) ≫
    (levelPushforwardIso D c B hD hX hc Ab.{max u v + 1} i).hom.app
      (levelInverseImage F i)).hom

/-- **The restricted inverse images are inverse images**: `levelε` is a universal arrow. -/
theorem isUniversalArrow_levelε (i : (sys D c B hD hX hc).I) :
    IsUniversalArrow (sys D c B hD hX hc) (bottom_isTerminal D c B hD hX hc)
      (levelε F) i :=
  isUniversalArrow_levelεOf (A := Ab.{max u v + 1}) (fun _ => _) (fun _ => _) F i

omit [Nonempty I] [IsDirected I (· ≤ ·)] [OrderBot I]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- Abelian presheaves on the small étale site of `X` admit sheafification. -/
theorem hasSheafify_limit : HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{max u v + 1} :=
  inferInstance

attribute [local instance] hasSheafify_limit

/-- The inverse image of `F` to the limit `X`. -/
abbrev limitInverseImage : Sheaf c.pt.smallEtaleTopology Ab.{max u v + 1} :=
  (etaleAbelianInverseImage.{max u v, 0} (lvlπ D c B hD hX hc (bottom D c B hD hX hc))).obj F

/-- The restriction of the inverse image of `F` to the raised site of the limit. -/
abbrev limitSheaf : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1} :=
  (limitRestrict D c B hX Ab.{max u v + 1}).obj (limitInverseImage F)

/-- The universal arrow of the restricted inverse image on the site of the limit. -/
def limitε :
    ((levelRestrict D c B hD hX hc Ab.{max u v + 1} (bottom D c B hD hX hc)).obj F).obj ⟶
      (toLimitSmall D c B hD hX hc (bottom D c B hD hX hc)).op ⋙ (limitSheaf F).obj :=
  ((levelRestrict D c B hD hX hc Ab.{max u v + 1} (bottom D c B hD hX hc)).map
      ((etaleAbelianInverseImageDirectImageAdj.{max u v, 0}
        (lvlπ D c B hD hX hc (bottom D c B hD hX hc))).unit.app F) ≫
    (limitPushforwardIso D c B hD hX hc Ab.{max u v + 1}).hom.app (limitInverseImage F)).hom

/-- **The restriction of the inverse image to the limit is an inverse image**: `limitε` is a
universal arrow. -/
theorem existsUnique_limitε (H : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck
      Ab.{max u v + 1})
    (g : ((levelRestrict D c B hD hX hc Ab.{max u v + 1} (bottom D c B hD hX hc)).obj F).obj ⟶
      (toLimitSmall D c B hD hX hc (bottom D c B hD hX hc)).op ⋙ H.obj) :
    ∃! h : limitSheaf F ⟶ H,
      limitε F ≫ Functor.whiskerLeft (toLimitSmall D c B hD hX hc _).op h.hom = g := by
  let : (toLimitSmall D c B hD hX hc (bottom D c B hD hX hc)).IsContinuous
      ((sys D c B hD hX hc).J _) (limitSitePrecoverage D c B hX).toGrothendieck :=
    toLimitSmall_isContinuous D c B hD hX hc _
  obtain ⟨h, hh, hu⟩ := existsUnique_of_adjunction
    (etaleAbelianInverseImageDirectImageAdj.{max u v, 0}
      (lvlπ D c B hD hX hc (bottom D c B hD hX hc)))
    (limitRestrict D c B hX Ab.{max u v + 1}).asEquivalence
    (Functor.FullyFaithful.ofFullyFaithful
      (levelRestrict D c B hD hX hc Ab.{max u v + 1} (bottom D c B hD hX hc)))
    ((toLimitSmall D c B hD hX hc (bottom D c B hD hX hc)).sheafPushforwardContinuous
      Ab.{max u v + 1} _ _)
    (limitPushforwardIso D c B hD hX hc Ab.{max u v + 1}) F H (ObjectProperty.homMk g)
  exact ⟨h, congrArg (fun φ => φ.hom) hh, fun h' hh' => hu h' (Sheaf.hom_ext hh')⟩

/-- **The system of Stacks 0EXZ of the inverse images of `F`** on the levels of the system of
Stacks 0EYL. -/
abbrev levelSystem :
    InverseSystemOfFiniteSites.AbelianSheafSystem.{v, v,
      max v (max u v + 1), max v (max u v + 1)} (sys D c B hD hX hc) :=
  abelianSystem (isUniversalArrow_levelε F)

/-- The structure maps `f_i⁻¹F_i ⟶ F|_X` of the inverse image on the limit, in adjoint form. -/
abbrev limitι (i : (sys D c B hD hX hc).I) :=
  letI : ∀ i, (toLimitSmall D c B hD hX hc i).IsContinuous ((sys D c B hD hX hc).J i)
      (limitSitePrecoverage D c B hX).toGrothendieck := toLimitSmall_isContinuous D c B hD hX hc
  ι (sys D c B hD hX hc) (bottom_isTerminal D c B hD hX hc) (levelε F)
    (isUniversalArrow_levelε F) (toLimitSmall D c B hD hX hc)
    (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX).toGrothendieck
    (limitε F) i

/-- **The inverse image of `F` to the limit presents `colim f_i⁻¹(f_{i⊥}⁻¹F)`** on the raised
small affine étale site of the limit, in the sense of Stacks 09YP. -/
theorem isColimitPresentation_levelSystem :
    Stacks.WeakSites.ColimitSiteCohomology.IsColimitPresentation.{v, v, max v (max u v + 1),
      max v (max u v + 1)} (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) (levelSystem F)
      (limitSheaf F) (limitι F) :=
  let : ∀ i, (toLimitSmall D c B hD hX hc i).IsContinuous ((sys D c B hD hX hc).J i)
      (limitSitePrecoverage D c B hX).toGrothendieck := toLimitSmall_isContinuous D c B hD hX hc
  isColimitPresentation_abelianSystem (isUniversalArrow_levelε F) (toLimitSmall D c B hD hX hc)
    (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) (limitε F)
    (existsUnique_limitε F)

end Abelian

end Stacks.EtaleCohomology.LimitSiteBridge
