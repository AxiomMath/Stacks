module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitInverseImageSystem
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.UniversalPullbackSections
-- the levels of the canonical system of Stacks 0EYL are indexed by `Iᵒᵖ` itself; the body of
-- `affineEtaleSiteColimit` is needed to see it
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.ColimitSite

/-!
# Sections of the inverse image of a sheaf of sets to a limit of schemes, on the sites of 0EYL

Let `I` be a directed set with a least element `⊥`, let `(X_i)` be an inverse system of schemes
over `I` with affine transition morphisms and let `X = lim X_i`. Let `F` be a sheaf of sets on
the small étale site of `X_⊥`, and let inverse images of sheaves of sets along the morphisms
`f_i : X_i ⟶ X_⊥` and `f : X ⟶ X_⊥` be given as arbitrary left adjoints of the direct images.

On the strict small models of the sites of Stacks 0EYL (`Stacks.EtaleCohomology.LimitSiteBridge`)
the restrictions of the inverse images are the system of inverse images of the restriction of `F`
and the restriction of `f⁻¹F` is its colimit; so the weak-system form of Stacks 09YN applies: for
every object `Y` of a level `i`, the sections of `f⁻¹F` over the image of `Y` in the site of the
limit are the filtered colimit of the sections of `f_j⁻¹F` over the transition images of `Y`.

## Main definitions

* `limitεOf`: the universal arrow of the restricted inverse image on the site of the limit, for an
  arbitrary inverse-image adjunction.

## Main results

* `existsUnique_limitεOf`: its universal property.
* `sections_colimit_levelOf`: the colimit description of the sections over the limit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

namespace Stacks.EtaleCohomology.LimitSiteBridge

open Stacks.EtaleCohomology.AffineLimitCohomology Stacks.WeakSites.PullbackSystem

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [OrderBot I]
  {D : Iᵒᵖ ⥤ Scheme.{max u v}} {c : Cone D}
  {B : BigEtaleSite.{max u v}}
  {hD : ∀ i, B.Contains (D.obj i)} {hX : B.Contains c.pt}
  {hc : IsLimit c}
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  (L : ∀ i : (sys D c B hD hX hc).I,
    Sheaf (lvl D c B hD hX hc (bottom D c B hD hX hc)).smallEtaleTopology (Type (max u v + 1)) ⥤
      Sheaf (lvl D c B hD hX hc i).smallEtaleTopology (Type (max u v + 1)))
  (adj : ∀ i, L i ⊣ (smallEtaleBaseChange (toBottom D c B hD hX hc i)).sheafPushforwardContinuous
    (Type (max u v + 1)) _ _)
  (LT : Sheaf (lvl D c B hD hX hc (bottom D c B hD hX hc)).smallEtaleTopology (Type (max u v + 1)) ⥤
      Sheaf c.pt.smallEtaleTopology (Type (max u v + 1)))
  (adjT : LT ⊣
    (smallEtaleBaseChange (lvlπ D c B hD hX hc (bottom D c B hD hX hc))).sheafPushforwardContinuous
      (Type (max u v + 1)) _ _)
  (F : Sheaf (lvl D c B hD hX hc (bottom D c B hD hX hc)).smallEtaleTopology (Type (max u v + 1)))

/-- The universal arrow of the restricted inverse image on the site of the limit, for an arbitrary
left adjoint `LT` of the direct image along `X ⟶ X_⊥`: the restriction of the unit, read through
`limitPushforwardIso`. -/
def limitεOf :
    ((levelRestrict D c B hD hX hc (Type (max u v + 1)) (bottom D c B hD hX hc)).obj F).obj ⟶
      (toLimitSmall D c B hD hX hc (bottom D c B hD hX hc)).op ⋙
        ((limitRestrict D c B hX (Type (max u v + 1))).obj (LT.obj F)).obj :=
  ((levelRestrict D c B hD hX hc (Type (max u v + 1)) (bottom D c B hD hX hc)).map
      (adjT.unit.app F) ≫
    (limitPushforwardIso D c B hD hX hc (Type (max u v + 1))).hom.app (LT.obj F)).hom

/-- **The restriction of the inverse image to the site of the limit is an inverse image**:
`limitεOf` is a universal arrow. -/
theorem existsUnique_limitεOf (H : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck
      (Type (max u v + 1)))
    (g : ((levelRestrict D c B hD hX hc (Type (max u v + 1)) (bottom D c B hD hX hc)).obj F).obj ⟶
      (toLimitSmall D c B hD hX hc (bottom D c B hD hX hc)).op ⋙ H.obj) :
    ∃! h : (limitRestrict D c B hX (Type (max u v + 1))).obj (LT.obj F) ⟶ H,
      limitεOf LT adjT F ≫ Functor.whiskerLeft (toLimitSmall D c B hD hX hc _).op h.hom = g := by
  let : (toLimitSmall D c B hD hX hc (bottom D c B hD hX hc)).IsContinuous
      ((sys D c B hD hX hc).J _) (limitSitePrecoverage D c B hX).toGrothendieck :=
    toLimitSmall_isContinuous D c B hD hX hc _
  obtain ⟨h, hh, hu⟩ := existsUnique_of_adjunction adjT
    (limitRestrict D c B hX (Type (max u v + 1))).asEquivalence
    (Functor.FullyFaithful.ofFullyFaithful
      (levelRestrict D c B hD hX hc (Type (max u v + 1)) (bottom D c B hD hX hc)))
    ((toLimitSmall D c B hD hX hc (bottom D c B hD hX hc)).sheafPushforwardContinuous
      (Type (max u v + 1)) _ _)
    (limitPushforwardIso D c B hD hX hc (Type (max u v + 1))) F H (ObjectProperty.homMk g)
  exact ⟨h, congrArg (fun φ => φ.hom) hh, fun h' hh' => hu h' (Sheaf.hom_ext hh')⟩

/-- The restriction to the level `j` of the inverse image `(L j) F`. -/
abbrev levelSheafOf (j : (sys D c B hD hX hc).I) :
    Sheaf ((sys D c B hD hX hc).J j) (Type (max u v + 1)) :=
  (levelRestrict D c B hD hX hc (Type (max u v + 1)) j).obj ((L j).obj F)

/-- The restriction to the site of the limit of the inverse image `LT F`. -/
abbrev limitSheafOf : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck (Type (max u v + 1)) :=
  (limitRestrict D c B hX (Type (max u v + 1))).obj (LT.obj F)

/-- The transition maps of the system of restricted inverse images, read off from the universal
arrows. -/
def levelψOf {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) :
    (levelSheafOf L F i).obj ⟶ ((sys D c B hD hX hc).u a).op ⋙ (levelSheafOf L F j).obj :=
  ψ (sys D c B hD hX hc) (bottom_isTerminal D c B hD hX hc) (levelεOf L adj F)
    (isUniversalArrow_levelεOf L adj F) a

/-- The structure maps of the restricted inverse image on the site of the limit, as the colimit of
the restricted inverse images on the levels, read off from the universal arrows. -/
def limitιOf (j : (sys D c B hD hX hc).I) :
    (levelSheafOf L F j).obj ⟶ (toLimitSmall D c B hD hX hc j).op ⋙ (limitSheafOf LT F).obj :=
  letI : ∀ i, (toLimitSmall D c B hD hX hc i).IsContinuous ((sys D c B hD hX hc).J i)
      (limitSitePrecoverage D c B hX).toGrothendieck :=
    fun i => toLimitSmall_isContinuous D c B hD hX hc i
  ι (sys D c B hD hX hc) (bottom_isTerminal D c B hD hX hc) (levelεOf L adj F)
    (isUniversalArrow_levelεOf L adj F) (toLimitSmall D c B hD hX hc)
    (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX).toGrothendieck
    (limitεOf LT adjT F) j

/-- The map from the sections of the restricted inverse image on a level `j` over a transition
image `u_a(Y)` to the sections of the restricted inverse image on the limit over the image of
`Y`. -/
def limitρOf {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) (Y : (sys D c B hD hX hc).C i) :
    (levelSheafOf L F j).obj.obj (op (((sys D c B hD hX hc).u a).obj Y)) ⟶
      (limitSheafOf LT F).obj.obj (op ((toLimitSmall D c B hD hX hc i).obj Y)) :=
  (limitιOf L adj LT adjT F j).app (op (((sys D c B hD hX hc).u a).obj Y)) ≫
    (limitSheafOf LT F).obj.map
      (eqToHom (congrArg op (Functor.congr_obj (toLimitSmall_transition D c B hD hX hc a) Y)))

/-- **Stacks 09YN for the inverse images of a sheaf of sets on `X_⊥`, on the sites of 0EYL.** For
every object `Y` of a level `i`, every section of the restriction of `f⁻¹F` over the image of `Y`
comes from a section of the restriction of `f_j⁻¹F` over a transition image of `Y`, and two such
sections with the same image agree after a further transition. -/
theorem sections_colimit_levelOf (i : (sys D c B hD hX hc).I) (Y : (sys D c B hD hX hc).C i) :
    (∀ s : (limitSheafOf LT F).obj.obj (op ((toLimitSmall D c B hD hX hc i).obj Y)),
        ∃ (j : (sys D c B hD hX hc).I) (a : j ⟶ i)
          (t' : (levelSheafOf L F j).obj.obj (op (((sys D c B hD hX hc).u a).obj Y))),
          limitρOf L adj LT adjT F a Y t' = s) ∧
      ∀ (j : (sys D c B hD hX hc).I) (a : j ⟶ i)
        (t₁ t₂ : (levelSheafOf L F j).obj.obj (op (((sys D c B hD hX hc).u a).obj Y))),
        limitρOf L adj LT adjT F a Y t₁ = limitρOf L adj LT adjT F a Y t₂ →
          ∃ (k : (sys D c B hD hX hc).I) (b : k ⟶ j),
            (levelψOf L adj F b).app (op (((sys D c B hD hX hc).u a).obj Y)) t₁ =
              (levelψOf L adj F b).app (op (((sys D c B hD hX hc).u a).obj Y)) t₂ :=
  @sections_colimit_of_universal (sys D c B hD hX hc) _
    (bottom_isTerminal D c B hD hX hc) _ _ (levelεOf L adj F) (isUniversalArrow_levelεOf L adj F)
    _ _ (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
    (toLimitSmall_obj_descends D c B hD hX hc) (toLimitSmall_hom_descends D c B hD hX hc)
    (toLimitSmall_hom_eventually_eq D c B hD hX hc) (limitSitePrecoverage D c B hX)
    (mem_limitSitePrecoverage_iff D c B hD hX hc)
    (fun i => toLimitSmall_isContinuous D c B hD hX hc i)
    _ (limitεOf LT adjT F) (existsUnique_limitεOf LT adjT F) i Y

end Stacks.EtaleCohomology.LimitSiteBridge
