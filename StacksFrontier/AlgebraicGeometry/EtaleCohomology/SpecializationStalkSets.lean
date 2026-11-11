module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SpecializationStalkIdentifications

/-!
# The specialization map on stalks of étale sheaves of sets, and Stacks 0GJ3

Let `S` be a scheme, `s` a geometric point of `S`, `p : Spec(𝒪^{sh}_{S,s}) ⟶ S` the structure
morphism of the strict henselization of `S` at `s`, and `t` a geometric point of
`Spec(𝒪^{sh}_{S,s})`. Section 0GJ2 of the Stacks project constructs, for any sheaf `F` on
`S_étale`, the specialization map

`sp : F_s ⟶ F_{t ≫ p}`

sending the germ at `s` of a section `σ` over an étale neighbourhood `(U, u)` of `s` to the germ
of `σ` at the étale neighbourhood `(U, v)` of `t ≫ p`, where `v` is the image of `t` under the
unique morphism `Spec(𝒪^{sh}_{S,s}) ⟶ U` over `S` carrying the canonical geometric point to `u`.
[Stacks, Tag 0GJ3] describes the same map using the identifications

`F_s = Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)`  and  `F_{t ≫ p} = Γ(t, t⁻¹p⁻¹F)`

of Theorem 03Q9 (applied to `id_S`) and Lemma 03Q1: under them, `sp` is pullback of sections
along `t`.

This file does this for sheaves of sets, that is, sheaves with values in `Type (u + 1)` on the
small étale site `S.Etale`. It builds the inverse image of sheaves of sets on small étale sites
with its adjunction, the stalk at a geometric point and its behaviour under inverse image, the
specialization map, the two identifications (proving that both are isomorphisms), and the
description of `sp` asserted by Tag 0GJ3.

## Main definitions

* `Stacks.EtaleCohomology.smallEtalePullbackSet` — inverse image of sheaves of sets along a
  morphism of schemes, the left adjoint of restriction along base change.
* `Stacks.EtaleCohomology.smallEtaleStalkSet` — the stalk of a sheaf of sets at a geometric
  point.
* `AlgebraicGeometry.smallEtaleSpecializationStalkSet` — **the specialization map of Section
  0GJ2** for sheaves of sets.
* `AlgebraicGeometry.etaleStalkSectionsSetIso` — the identification
  `F_s ≅ Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)` (Theorem 03Q9 at `id_S`, in degree zero).
* `AlgebraicGeometry.geometricStalkPullbackSectionsSetIso` — the identification
  `F_x ≅ Γ(x, x⁻¹F)` (Lemma 03Q1).

## Main results

* `AlgebraicGeometry.smallEtaleSpecializationStalkSet_eq_sectionsRestrictionSet` —
  **[Stacks, Tag 0GJ3]** for sheaves of sets: `sp` is the first identification, followed by
  pullback of sections along `t`, followed by the inverse of the second identification.

## References

* [Stacks Project, Section 0GJ2](https://stacks.math.columbia.edu/tag/0GJ2)
* [Stacks Project, Tag 0GJ3](https://stacks.math.columbia.edu/tag/0GJ3)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### Inverse image of sheaves of sets -/

section Images

variable {X Y Z : Scheme.{u}}

/-- Inverse image of sheaves of sets on the small étale sites along `f : X ⟶ Y`: the left
adjoint of restriction along the base-change functor `smallEtaleBaseChange f`. -/
abbrev smallEtalePullbackSet (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology Y) (Type (u + 1)) ⥤ Sheaf (smallEtaleTopology X) (Type (u + 1)) :=
  (smallEtaleBaseChange f).sheafPullback (Type (u + 1)) (smallEtaleTopology Y)
    (smallEtaleTopology X)

/-- The inverse-image/direct-image adjunction for sheaves of sets on the small étale sites of `X`
and `Y`, induced by a morphism `f : X ⟶ Y`. -/
def smallEtaleAdjunctionSet (f : X ⟶ Y) :
    smallEtalePullbackSet f ⊣ (smallEtaleBaseChange f).sheafPushforwardContinuous
      (Type (u + 1)) (smallEtaleTopology Y) (smallEtaleTopology X) :=
  Functor.sheafAdjunctionContinuous (smallEtaleBaseChange f) (Type (u + 1))
    (smallEtaleTopology Y) (smallEtaleTopology X)

/-- The composition isomorphism `a⁻¹ ∘ b⁻¹ ≅ (a ≫ b)⁻¹` for inverse image of sheaves of sets on
the small étale sites: the conjugate, under the inverse-image/direct-image adjunctions, of the
composition isomorphism `Stacks.EtaleCohomology.smallEtalePushforwardCompIso` for direct
image. -/
def smallEtalePullbackSetCompIso (a : X ⟶ Y) (b : Y ⟶ Z) :
    smallEtalePullbackSet b ⋙ smallEtalePullbackSet a ≅ smallEtalePullbackSet (a ≫ b) :=
  Adjunction.leftAdjointUniq ((smallEtaleAdjunctionSet b).comp (smallEtaleAdjunctionSet a))
    (Adjunction.ofNatIsoRight (smallEtaleAdjunctionSet (a ≫ b))
      (smallEtalePushforwardCompIso.{u, 0} a b).symm)

end Images

/-! ### Restriction of sections to global sections of an inverse image -/

section Sections

variable {Z T : Scheme.{u}} (p : T ⟶ Z) (W : Z.Etale) (r : T ⟶ W.left)

/-- Restriction of sections of a sheaf of sets over an étale object `W` of the small étale site
of `Z` to global sections of its inverse image on `T`, along a morphism `r : T ⟶ W.left` lying
over `p : T ⟶ Z`: carry a section over `W` to a section of the inverse image over the base change
of `W`, restrict it along the morphism determined by `r`, and read the result as a global
section. -/
def smallEtaleSectionsPullbackSet (hr : r ≫ W.hom = p) :
    (sheafSections (smallEtaleTopology Z) (Type (u + 1))).obj (op W) ⟶
      smallEtalePullbackSet p ⋙ Sheaf.Γ (smallEtaleTopology T) (Type (u + 1)) :=
  Stacks.Sites.sectionsPullbackComparison (smallEtaleBaseChange p) (Type (u + 1))
      (smallEtaleTopology Z) (smallEtaleTopology T) (smallEtaleAdjunctionSet p)
      (smallEtaleBaseChangeLift p W r hr) ≫
    Functor.whiskerLeft (smallEtalePullbackSet p)
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) (Type (u + 1))
        (isTerminalEtaleMkId T)).inv

/-- The morphism of étale objects determined by `r`, followed by the base change of a morphism
`m : W ⟶ V` of étale objects, is the morphism determined by `r ≫ m.left`. -/
theorem smallEtaleBaseChangeLift_comp_map_left {V : Z.Etale} (m : W ⟶ V)
    (hr : r ≫ W.hom = p) (hrm : (r ≫ m.left) ≫ V.hom = p) :
    smallEtaleBaseChangeLift p W r hr ≫ (smallEtaleBaseChange p).map m =
      smallEtaleBaseChangeLift p V (r ≫ m.left) hrm := by
  have hm1 : ((smallEtaleBaseChange p).map m).left ≫ pullback.fst V.hom p =
      pullback.fst W.hom p ≫ m.left := pullback.lift_fst _ _ _
  refine smallEtaleBaseChangeLift_eq p V (r ≫ m.left) hrm _ ?_
  change ((smallEtaleBaseChangeLift p W r hr).left ≫ ((smallEtaleBaseChange p).map m).left) ≫
    pullback.fst V.hom p = r ≫ m.left
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (smallEtaleBaseChangeLift p W r hr).left ≫ z) hm1).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ m.left)
          (pullback.lift_fst r (𝟙 T) (hr.trans (Category.id_comp p).symm)))))

/-- Restricting a section along a morphism of étale objects over `Z` and then pulling it back is
pulling it back along the composite. -/
theorem map_comp_smallEtaleSectionsPullbackSet {V : Z.Etale} (m : W ⟶ V)
    (hr : r ≫ W.hom = p) (hrm : (r ≫ m.left) ≫ V.hom = p) :
    (sheafSections (smallEtaleTopology Z) (Type (u + 1))).map m.op ≫
        smallEtaleSectionsPullbackSet p W r hr =
      smallEtaleSectionsPullbackSet p V (r ≫ m.left) hrm := by
  have key := Stacks.Sites.map_comp_sectionsPullbackComparison (smallEtaleBaseChange p)
    (Type (u + 1)) (smallEtaleTopology Z) (smallEtaleTopology T) (smallEtaleAdjunctionSet p) m
    (smallEtaleBaseChangeLift p W r hr)
  rw [smallEtaleBaseChangeLift_comp_map_left p W r m hr hrm] at key
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) key)

/-- The restriction of sections depends only on the morphism into the étale object, not on the
proof that it lies over `p`. -/
theorem smallEtaleSectionsPullbackSet_congr {r' : T ⟶ W.left} (hr : r ≫ W.hom = p)
    (hr' : r' ≫ W.hom = p) (h : r = r') :
    smallEtaleSectionsPullbackSet p W r hr = smallEtaleSectionsPullbackSet p W r' hr' := by
  subst h
  rfl

end Sections

/-! ### Restriction of global sections along a morphism over the base -/

section Restriction

variable {Z T T' : Scheme.{u}} (g : T ⟶ Z) (c : T' ⟶ T) (g' : T' ⟶ Z)

/-- Restriction of global sections of a sheaf of sets on the small étale site of `T` to global
sections of its inverse image on `T'`, along a morphism of schemes `c : T' ⟶ T`. -/
def smallEtaleGlobalSectionsRestrictionSet :
    Sheaf.Γ (smallEtaleTopology T) (Type (u + 1)) ⟶
      smallEtalePullbackSet c ⋙ Sheaf.Γ (smallEtaleTopology T') (Type (u + 1)) :=
  (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) (Type (u + 1)) (isTerminalEtaleMkId T)).hom ≫
    smallEtaleSectionsPullbackSet c (Scheme.Etale.mk (𝟙 T)) c (Category.comp_id c)

/-- Restriction of global sections of an inverse image of a sheaf of sets along a morphism
`c : T' ⟶ T` of schemes over `Z`: restrict the section along `c`, which gives a global section of
`c⁻¹g⁻¹F` on `T'`, and read that as a global section of `(g')⁻¹F` by the composition isomorphism
for inverse images, `g'` being the composite `c ≫ g`. -/
def smallEtaleSectionsRestrictionSet (hc : c ≫ g = g') :
    smallEtalePullbackSet g ⋙ Sheaf.Γ (smallEtaleTopology T) (Type (u + 1)) ⟶
      smallEtalePullbackSet g' ⋙ Sheaf.Γ (smallEtaleTopology T') (Type (u + 1)) :=
  Functor.whiskerLeft (smallEtalePullbackSet g) (smallEtaleGlobalSectionsRestrictionSet c) ≫
    Functor.whiskerRight ((smallEtalePullbackSetCompIso c g).hom ≫
      eqToHom (congrArg (fun m : T' ⟶ Z => smallEtalePullbackSet m) hc))
      (Sheaf.Γ (smallEtaleTopology T') (Type (u + 1)))

/-- At the composite itself, restriction of sections is restriction along `c` followed by the
composition isomorphism for inverse images, with no transport. -/
theorem smallEtaleSectionsRestrictionSet_comp :
    smallEtaleSectionsRestrictionSet g c (c ≫ g) rfl =
      Functor.whiskerLeft (smallEtalePullbackSet g) (smallEtaleGlobalSectionsRestrictionSet c) ≫
        Functor.whiskerRight (smallEtalePullbackSetCompIso c g).hom
          (Sheaf.Γ (smallEtaleTopology T') (Type (u + 1))) := by
  simp [smallEtaleSectionsRestrictionSet]

end Restriction

/-! ### Transitivity in the scheme over the base -/

section Transitivity

variable {Z T T' : Scheme.{u}} (p : T ⟶ Z) (W : Z.Etale) (c : T' ⟶ T) (p' : T' ⟶ Z)

/-- **Restriction of sections over an étale object is transitive in the scheme over the base.**
Restricting a section of a sheaf of sets over `W` to a global section of its inverse image on `T`
along `r`, and then restricting that along `c : T' ⟶ T`, is restricting the section directly
along `r' = c ≫ r`. -/
theorem smallEtaleSectionsPullbackSet_comp_sectionsRestrictionSet
    (r : T ⟶ W.left) (hr : r ≫ W.hom = p) (hc : c ≫ p = p')
    (r' : T' ⟶ W.left) (hr' : r' ≫ W.hom = p') (hcr : c ≫ r = r') :
    smallEtaleSectionsPullbackSet p W r hr ≫ smallEtaleSectionsRestrictionSet p c p' hc =
      smallEtaleSectionsPullbackSet p' W r' hr' := by
  subst hc
  rw [smallEtaleSectionsRestrictionSet_comp]
  have ha := Stacks.Sites.sectionsPullbackComparison_comp (smallEtaleBaseChange p)
    (smallEtaleBaseChange c) (smallEtaleBaseChange (c ≫ p)) (Type (u + 1))
    (smallEtaleTopology Z) (smallEtaleTopology T) (smallEtaleTopology T')
    (smallEtaleAdjunctionSet p) (smallEtaleAdjunctionSet c) (smallEtaleAdjunctionSet (c ≫ p))
    (smallEtalePullbackSetCompIso c p) ((smallEtaleBaseChangeComp c p).symm.hom.app W)
    (fun F => Stacks.Sites.unit_comp_leftAdjointUniq_app (smallEtaleBaseChange p)
      (smallEtaleBaseChange c) (smallEtaleBaseChange (c ≫ p)) (Type (u + 1))
      (smallEtaleTopology Z) (smallEtaleTopology T) (smallEtaleTopology T')
      (smallEtaleAdjunctionSet p) (smallEtaleAdjunctionSet c) (smallEtaleAdjunctionSet (c ≫ p))
      (smallEtaleBaseChangeComp c p).symm F W)
    (smallEtaleBaseChangeLift p W r hr)
    (smallEtaleBaseChangeLift c (Scheme.Etale.mk (𝟙 T)) c (Category.comp_id c))
    (smallEtaleBaseChangeLift (c ≫ p) W r' hr')
    (smallEtaleBaseChangeLift_comp p c W r hr r' hr' hcr)
  simp only [smallEtaleSectionsPullbackSet, smallEtaleGlobalSectionsRestrictionSet]
  rw [← ha]
  refine NatTrans.ext (funext fun F => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T') (Type (u + 1))
    (isTerminalEtaleMkId T')).inv.naturality]

end Transitivity

/-! ### The stalk of a sheaf of sets at a geometric point -/

section Stalk

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)

/-- The stalk `F ↦ F_x` of a sheaf of sets on the small étale site of `X` at the point of that
site determined by a geometric point `x` of `X`: the filtered colimit of the sections of `F` over
the étale neighbourhoods of `x`. -/
abbrev smallEtaleStalkSet : Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ Type (u + 1) :=
  (Scheme.pointSmallEtale x).sheafFiber (A := Type (u + 1))

/-- Two maps out of the stalk of an étale sheaf of sets at a geometric point agree as soon as they
agree on the germ of every section over every étale neighbourhood of that point. -/
theorem smallEtaleStalkSet_hom_ext (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    {T : Type (u + 1)} {f g : (smallEtaleStalkSet x).obj F ⟶ T}
    (h : ∀ (W : X.Etale) (v : (Scheme.pointSmallEtale x).fiber.obj W),
      (Scheme.pointSmallEtale x).toPresheafFiber W v F.obj ≫ f =
        (Scheme.pointSmallEtale x).toPresheafFiber W v F.obj ≫ g) :
    f = g :=
  (Scheme.pointSmallEtale x).presheafFiber_hom_ext h

variable (K : Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ Type (u + 1))
  (stage : ∀ (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (W : X.Etale),
    (Scheme.pointSmallEtale x).fiber.obj W → (F.obj.obj (op W) ⟶ K.obj F))

/-- A family of maps out of the sections of étale sheaves of sets over the étale neighbourhoods of
a geometric point, compatible with restriction along morphisms of neighbourhoods and natural in
the sheaf, descends to a natural transformation out of the stalk functor at that point. -/
def smallEtaleStalkSetDesc
    (hstage : ∀ (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) ⦃W V : X.Etale⦄ (m : W ⟶ V)
      (v : (Scheme.pointSmallEtale x).fiber.obj W),
      F.obj.map m.op ≫ stage F W v = stage F V ((Scheme.pointSmallEtale x).fiber.map m v))
    (hnat : ∀ {F G : Sheaf (smallEtaleTopology X) (Type (u + 1))} (α : F ⟶ G) (W : X.Etale)
      (v : (Scheme.pointSmallEtale x).fiber.obj W),
      α.hom.app (op W) ≫ stage G W v = stage F W v ≫ K.map α) :
    smallEtaleStalkSet x ⟶ K where
  app F := (Scheme.pointSmallEtale x).presheafFiberDesc (stage F) (hstage F)
  naturality F G α := by
    apply (Scheme.pointSmallEtale x).presheafFiber_hom_ext
    intro W v
    change (Scheme.pointSmallEtale x).toPresheafFiber W v F.obj ≫
        ((Scheme.pointSmallEtale x).presheafFiber.map α.hom ≫
          (Scheme.pointSmallEtale x).presheafFiberDesc (stage G) (hstage G)) =
      (Scheme.pointSmallEtale x).toPresheafFiber W v F.obj ≫
        ((Scheme.pointSmallEtale x).presheafFiberDesc (stage F) (hstage F) ≫ K.map α)
    rw [(Scheme.pointSmallEtale x).toPresheafFiber_naturality_assoc α.hom W v,
      (Scheme.pointSmallEtale x).toPresheafFiber_presheafFiberDesc (stage G) (hstage G),
      (Scheme.pointSmallEtale x).toPresheafFiber_presheafFiberDesc_assoc (stage F) (hstage F)]
    exact hnat α W v

/-- The descended transformation has the prescribed value on the germ at the geometric point of a
section over an étale neighbourhood. -/
theorem toPresheafFiber_comp_smallEtaleStalkSetDesc
    (hstage : ∀ (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) ⦃W V : X.Etale⦄ (m : W ⟶ V)
      (v : (Scheme.pointSmallEtale x).fiber.obj W),
      F.obj.map m.op ≫ stage F W v = stage F V ((Scheme.pointSmallEtale x).fiber.map m v))
    (hnat : ∀ {F G : Sheaf (smallEtaleTopology X) (Type (u + 1))} (α : F ⟶ G) (W : X.Etale)
      (v : (Scheme.pointSmallEtale x).fiber.obj W),
      α.hom.app (op W) ≫ stage G W v = stage F W v ≫ K.map α)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (W : X.Etale)
    (v : (Scheme.pointSmallEtale x).fiber.obj W) :
    (Scheme.pointSmallEtale x).toPresheafFiber W v F.obj ≫
        (smallEtaleStalkSetDesc x K stage hstage hnat).app F =
      stage F W v :=
  (Scheme.pointSmallEtale x).toPresheafFiber_presheafFiberDesc (stage F) (hstage F) W v

end Stalk

/-! ### The stalk of an inverse image of a sheaf of sets -/

section StalkPullback

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X')

/-- **Stalks of an inverse image of étale sheaves of sets.** For `g : X' ⟶ X` and a geometric
point `s : Spec Ω ⟶ X'`, the stalk at `s` of the inverse image `g⁻¹F` of a sheaf of sets `F` on
the small étale site of `X` is the stalk of `F` at the image geometric point `s ≫ g`, naturally
in `F`. -/
def smallEtaleStalkPullbackSetIso :
    smallEtalePullbackSet g ⋙ smallEtaleStalkSet s ≅ smallEtaleStalkSet (s ≫ g) :=
  ((Scheme.pointSmallEtale s).sheafFiberComapIso (smallEtaleBaseChange g)
      (coverPreserving_smallEtaleBaseChange g) (Type (u + 1))).symm ≪≫
    (Point.sheafFiberIsoOfFiberIso (A := Type (u + 1)) (Scheme.pointSmallEtale (s ≫ g))
      ((Scheme.pointSmallEtale s).comap (smallEtaleBaseChange g)
        (coverPreserving_smallEtaleBaseChange g)) (pointSmallEtaleComapFiberIso g s)).symm

/-- On the germ at `s ≫ g` of a section of an étale sheaf of sets `F` over an étale neighbourhood
`W` of that point, the comparison of stalks is the unit of the inverse-image/direct-image
adjunction followed by the germ at the corresponding lift of `s` to the base change `W ×_X X'`. -/
theorem toPresheafFiber_comp_smallEtaleStalkPullbackSetIso_inv
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (W : X.Etale)
    (v : (Scheme.pointSmallEtale (s ≫ g)).fiber.obj W) :
    (Scheme.pointSmallEtale (s ≫ g)).toPresheafFiber W v F.obj ≫
        (smallEtaleStalkPullbackSetIso g s).inv.app F =
      ((smallEtaleAdjunctionSet g).unit.app F).hom.app (op W) ≫
        (Scheme.pointSmallEtale s).toPresheafFiber ((smallEtaleBaseChange g).obj W)
          ((pointSmallEtaleComapFiberIso g s).hom.app W v)
          ((smallEtalePullbackSet g).obj F).obj := by
  have h1 := Point.toPresheafFiber_presheafFiberIsoOfFiberIso (A := Type (u + 1))
    (Scheme.pointSmallEtale (s ≫ g))
    ((Scheme.pointSmallEtale s).comap (smallEtaleBaseChange g)
      (coverPreserving_smallEtaleBaseChange g)) (pointSmallEtaleComapFiberIso g s) F.obj W v
  have h2 := Point.toSheafFiber_sheafFiberComapIso_hom (Scheme.pointSmallEtale s)
    (smallEtaleBaseChange g) (coverPreserving_smallEtaleBaseChange g) F W
    ((pointSmallEtaleComapFiberIso g s).hom.app W v)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ ((Scheme.pointSmallEtale s).sheafFiberComapIso (smallEtaleBaseChange g)
      (coverPreserving_smallEtaleBaseChange g) (Type (u + 1))).hom.app F) h1).trans h2)

end StalkPullback

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

/-! ### Stalks and sections over an initial étale neighbourhood -/

section InitialNeighborhood

variable {X T : Scheme.{u}} (g : T ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (σ : Spec (.of Ω) ⟶ T)

/-- The comparison `Γ(T, G) ⟶ G_σ` from the global sections of a sheaf of sets on the small étale
site of `T` to its stalk at a geometric point `σ` of `T`: read a global section as a section over
the identity object of the small étale site, which is terminal, and take its germ at `σ` along a
chosen lift `eσ` of `σ` to that object. -/
def smallEtaleGlobalSectionsToStalkSet
    (eσ : (Scheme.pointSmallEtale σ).fiber.obj (Scheme.Etale.mk (𝟙 T))) :
    Sheaf.Γ (smallEtaleTopology T) (Type (u + 1)) ⟶ smallEtaleStalkSet σ :=
  (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) (Type (u + 1))
      (isTerminalEtaleMkId T)).hom ≫
    Functor.whiskerLeft (sheafToPresheaf (smallEtaleTopology T) (Type (u + 1)))
      ((Scheme.pointSmallEtale σ).toPresheafFiberNatTrans (Scheme.Etale.mk (𝟙 T)) eσ)

/-- **Global sections are the stalk at a geometric point admitting an initial lift to the
identity object.** If the identity object of the small étale site of `T`, with a chosen lift `eσ`
of a geometric point `σ`, is an initial étale neighbourhood of `σ`, then the comparison
`Γ(T, G) ⟶ G_σ` is an isomorphism, naturally in the sheaf of sets `G`. -/
theorem isIso_smallEtaleGlobalSectionsToStalkSet
    (eσ : (Scheme.pointSmallEtale σ).fiber.obj (Scheme.Etale.mk (𝟙 T)))
    (hinit : IsInitial (show (Scheme.pointSmallEtale σ).fiber.Elements from
      Functor.elementsMk _ (Scheme.Etale.mk (𝟙 T)) eσ)) :
    IsIso (smallEtaleGlobalSectionsToStalkSet σ eσ) := by
  have happ : ∀ G : Sheaf (smallEtaleTopology T) (Type (u + 1)),
      IsIso ((smallEtaleGlobalSectionsToStalkSet σ eσ).app G) := by
    intro G
    have : IsIso ((Scheme.pointSmallEtale σ).toPresheafFiber (Scheme.Etale.mk (𝟙 T)) eσ G.obj) :=
      ((Scheme.pointSmallEtale σ).isColimitPresheafFiberCocone G.obj).isIso_ι_app_of_isTerminal
        (op (Functor.elementsMk _ (Scheme.Etale.mk (𝟙 T)) eσ)) hinit.op
    change IsIso ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) (Type (u + 1))
        (isTerminalEtaleMkId T)).hom.app G ≫
      (Scheme.pointSmallEtale σ).toPresheafFiber (Scheme.Etale.mk (𝟙 T)) eσ G.obj)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Restriction of a section over an étale neighbourhood `W` of `σ ≫ g` to a global section of
the inverse image on `T`, followed by the germ at `σ` of that global section, is the unit of the
inverse-image/direct-image adjunction followed by the germ at the lift of `σ` to the base change
`W ×_X T` determined by the chosen lift of `σ ≫ g`. -/
theorem smallEtaleSectionsPullbackSet_comp_toPresheafFiber
    (eσ : (Scheme.pointSmallEtale σ).fiber.obj (Scheme.Etale.mk (𝟙 T))) (heσ : eσ.left = σ)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (W : X.Etale)
    (v : (Scheme.pointSmallEtale (σ ≫ g)).fiber.obj W)
    (r : T ⟶ W.left) (hr : r ≫ W.hom = g) (hσr : σ ≫ r = v.left) :
    (smallEtaleSectionsPullbackSet g W r hr).app F ≫
        ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) (Type (u + 1))
            (isTerminalEtaleMkId T)).hom.app ((smallEtalePullbackSet g).obj F) ≫
          (Scheme.pointSmallEtale σ).toPresheafFiber (Scheme.Etale.mk (𝟙 T)) eσ
            ((smallEtalePullbackSet g).obj F).obj) =
      ((smallEtaleAdjunctionSet g).unit.app F).hom.app (op W) ≫
        (Scheme.pointSmallEtale σ).toPresheafFiber
          ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj W)
          ((pointSmallEtaleComapFiberIso g σ).hom.app W v)
          ((smallEtalePullbackSet g).obj F).obj := by
  rw [smallEtaleSectionsPullbackSet, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  have hw : ((smallEtalePullbackSet g).obj F).obj.map
        (smallEtaleBaseChangeLift g W r hr).op ≫
      (Scheme.pointSmallEtale σ).toPresheafFiber (Scheme.Etale.mk (𝟙 T)) eσ
        ((smallEtalePullbackSet g).obj F).obj =
      (Scheme.pointSmallEtale σ).toPresheafFiber
        ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj W)
        ((pointSmallEtaleComapFiberIso g σ).hom.app W v)
        ((smallEtalePullbackSet g).obj F).obj := by
    refine Eq.trans (GrothendieckTopology.Point.toPresheafFiber_w (Scheme.pointSmallEtale σ)
      (smallEtaleBaseChangeLift g W r hr) eσ ((smallEtalePullbackSet g).obj F).obj) ?_
    congr 1
    refine pointSmallEtaleBaseChangeFiber_ext g σ W ?_
    have hleft : ((Scheme.pointSmallEtale σ).fiber.map
        (smallEtaleBaseChangeLift g W r hr) eσ).left =
        eσ.left ≫ (smallEtaleBaseChangeLift g W r hr).left := rfl
    rw [hleft, heσ, pointSmallEtaleComapFiberIso_hom_app_left_fst,
      smallEtaleBaseChangeLift_left]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => σ ≫ z) (pullback.lift_fst r (𝟙 T)
        (hr.trans (Category.id_comp g).symm))).trans hσr)
  refine Eq.trans (congrArg (fun z => z ≫ (Scheme.pointSmallEtale σ).toPresheafFiber
      (Scheme.Etale.mk (𝟙 T)) eσ ((smallEtalePullbackSet g).obj F).obj)
    (Stacks.Sites.sectionsPullbackComparison_app (Stacks.EtaleCohomology.smallEtaleBaseChange g)
      (Type (u + 1))
      (smallEtaleTopology X) (smallEtaleTopology T) (smallEtaleAdjunctionSet g)
      (smallEtaleBaseChangeLift g W r hr) F)) ?_
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z => ((smallEtaleAdjunctionSet g).unit.app F).hom.app (op W) ≫ z) hw)

/-- **The stalk is the sections over an initial étale neighbourhood, for sheaves of sets.** Let
`g : T ⟶ X` be a morphism of schemes and `σ` a geometric point of `T` whose image in `X` is `x`,
and suppose that the identity object of the small étale site of `T`, with the lift `eσ` of `σ`, is
initial among the étale neighbourhoods of `σ`. Suppose moreover that each étale neighbourhood
`(W, v)` of `x` receives a morphism `ρ W v` from `T` over `X` carrying `σ` to `v`. Then the
canonical map `A : F_x ⟶ Γ(T, g⁻¹F)`, which restricts the germ at `x` of a section over `(W, v)`
along `ρ W v`, is an isomorphism. -/
theorem isIso_stalkToSectionsSet_of_isInitial
    (eσ : (Scheme.pointSmallEtale σ).fiber.obj (Scheme.Etale.mk (𝟙 T))) (heσ : eσ.left = σ)
    (hinit : IsInitial (show (Scheme.pointSmallEtale σ).fiber.Elements from
      Functor.elementsMk _ (Scheme.Etale.mk (𝟙 T)) eσ))
    {x : Spec (.of Ω) ⟶ X} (hx : σ ≫ g = x)
    (A : smallEtaleStalkSet x ⟶
      smallEtalePullbackSet g ⋙ Sheaf.Γ (smallEtaleTopology T) (Type (u + 1)))
    (ρ : ∀ W : X.Etale, (Scheme.pointSmallEtale x).fiber.obj W → (T ⟶ W.left))
    (hρ : ∀ (W : X.Etale) (v : (Scheme.pointSmallEtale x).fiber.obj W), ρ W v ≫ W.hom = g)
    (hσρ : ∀ (W : X.Etale) (v : (Scheme.pointSmallEtale x).fiber.obj W),
      σ ≫ ρ W v = CategoryTheory.Over.Hom.left v)
    (hA : ∀ (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (W : X.Etale)
      (v : (Scheme.pointSmallEtale x).fiber.obj W),
      (Scheme.pointSmallEtale x).toPresheafFiber W v F.obj ≫ A.app F =
        (smallEtaleSectionsPullbackSet g W (ρ W v) (hρ W v)).app F) :
    IsIso A := by
  subst hx
  have key : A ≫ Functor.whiskerLeft (smallEtalePullbackSet g)
      (smallEtaleGlobalSectionsToStalkSet σ eσ) =
      (smallEtaleStalkPullbackSetIso g σ).inv := by
    ext F : 2
    refine smallEtaleStalkSet_hom_ext (σ ≫ g) F fun W v => ?_
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (smallEtaleGlobalSectionsToStalkSet σ eσ).app
            ((smallEtalePullbackSet g).obj F)) (hA F W v)).trans
        ((smallEtaleSectionsPullbackSet_comp_toPresheafFiber g σ eσ heσ F W v (ρ W v)
              (hρ W v) (hσρ W v)).trans
          (toPresheafFiber_comp_smallEtaleStalkPullbackSetIso_inv g σ F W v).symm))
  have := isIso_smallEtaleGlobalSectionsToStalkSet σ eσ hinit
  have : IsIso (Functor.whiskerLeft (smallEtalePullbackSet g)
      (smallEtaleGlobalSectionsToStalkSet σ eσ)) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso (A ≫ Functor.whiskerLeft (smallEtalePullbackSet g)
      (smallEtaleGlobalSectionsToStalkSet σ eσ)) := by
    rw [key]; infer_instance
  exact IsIso.of_isIso_comp_right A (Functor.whiskerLeft (smallEtalePullbackSet g)
    (smallEtaleGlobalSectionsToStalkSet σ eσ))

end InitialNeighborhood

/-! ### The second identification of Stacks 0GJ3: Lemma 03Q1 -/

section PullbackSections

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)

/-- The germ-level map: restriction of a section of an étale sheaf of sets over an étale
neighbourhood `(W, v)` of a geometric point `x` of `X` to a global section over the spectrum of
the residue field of `x` of the inverse image of that sheaf, along the lift `v`. -/
def geometricStalkPullbackSectionsStageSet (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    (W : X.Etale) (v : (Scheme.pointSmallEtale x).fiber.obj W) :
    F.obj.obj (op W) ⟶
      (smallEtalePullbackSet x ⋙
        Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) (Type (u + 1))).obj F :=
  (smallEtaleSectionsPullbackSet x W v.left (Over.w v)).app F

/-- The germ-level maps are compatible with restriction along a morphism of étale
neighbourhoods. -/
theorem map_comp_geometricStalkPullbackSectionsStageSet
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) {W V : X.Etale} (m : W ⟶ V)
    (v : (Scheme.pointSmallEtale x).fiber.obj W) :
    F.obj.map m.op ≫ geometricStalkPullbackSectionsStageSet x F W v =
      geometricStalkPullbackSectionsStageSet x F V
        ((Scheme.pointSmallEtale x).fiber.map m v) := by
  have hleft : ((Scheme.pointSmallEtale x).fiber.map m v).left = v.left ≫ m.left := rfl
  have h := map_comp_smallEtaleSectionsPullbackSet x W v.left m (Over.w v)
    (hleft ▸ Over.w ((Scheme.pointSmallEtale x).fiber.map m v))
  exact congrArg (fun σ => NatTrans.app σ F)
    (h.trans (smallEtaleSectionsPullbackSet_congr x V (v.left ≫ m.left) _
      (Over.w ((Scheme.pointSmallEtale x).fiber.map m v)) hleft.symm))

/-- The canonical map `F_x ⟶ Γ(x, x⁻¹F)` from the stalk of a sheaf of sets on the small étale site
of `X` at a geometric point `x` to the global sections of its inverse image on the spectrum of
the residue field of `x`. On the germ of a section over an étale neighbourhood of `x` it is
restriction of that section along the chosen lift of `x`. -/
def geometricStalkToPullbackSectionsSet :
    smallEtaleStalkSet x ⟶
      smallEtalePullbackSet x ⋙ Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) (Type (u + 1)) :=
  smallEtaleStalkSetDesc x _ (geometricStalkPullbackSectionsStageSet x)
    (fun F _ _ m v => map_comp_geometricStalkPullbackSectionsStageSet x F m v)
    (fun α W v => (smallEtaleSectionsPullbackSet x W v.left (Over.w v)).naturality α)

/-- On the germ at `x` of a section over an étale neighbourhood `(W, v)`, the comparison to
sections on the geometric point is restriction of that section along `v`. -/
theorem geometricStalkToPullbackSectionsSet_toPresheafFiber
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (W : X.Etale)
    (v : (Scheme.pointSmallEtale x).fiber.obj W) :
    (Scheme.pointSmallEtale x).toPresheafFiber W v F.obj ≫
        (geometricStalkToPullbackSectionsSet x).app F =
      (smallEtaleSectionsPullbackSet x W v.left (Over.w v)).app F :=
  toPresheafFiber_comp_smallEtaleStalkSetDesc x _ (geometricStalkPullbackSectionsStageSet x)
    (fun F _ _ m v => map_comp_geometricStalkPullbackSectionsStageSet x F m v)
    (fun α W v => (smallEtaleSectionsPullbackSet x W v.left (Over.w v)).naturality α) F W v

/-- **Stacks 03Q1 for sheaves of sets: the stalk at a geometric point is the sections of the
inverse image there.** The canonical map `F_x ⟶ Γ(x, x⁻¹F)` is an isomorphism. -/
theorem isIso_geometricStalkToPullbackSectionsSet :
    IsIso (geometricStalkToPullbackSectionsSet x) :=
  isIso_stalkToSectionsSet_of_isInitial x (𝟙 (Spec (.of Ω)))
    (pointSmallEtaleIdElement Ω) rfl (isInitialPointSmallEtaleIdElement Ω) (Category.id_comp x)
    (geometricStalkToPullbackSectionsSet x) (fun _ v => v.left)
    (fun _ v => CategoryTheory.Over.w v) (fun _ v => Category.id_comp v.left)
    (fun F W v => geometricStalkToPullbackSectionsSet_toPresheafFiber x F W v)

/-- **The second identification displayed in Stacks 0GJ3**, `F_x = Γ(x, x⁻¹F)`, for sheaves of
sets: the stalk of an étale sheaf of sets at a geometric point `x` of `X` is the set of global
sections of its inverse image on the spectrum of the residue field of `x`, naturally in the
sheaf. The isomorphism is the canonical map
`AlgebraicGeometry.geometricStalkToPullbackSectionsSet`, invertible by Lemma 03Q1. -/
def geometricStalkPullbackSectionsSetIso :
    smallEtaleStalkSet x ≅
      smallEtalePullbackSet x ⋙ Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) (Type (u + 1)) :=
  letI := isIso_geometricStalkToPullbackSectionsSet x
  asIso (geometricStalkToPullbackSectionsSet x)

/-- The identification `F_x = Γ(x, x⁻¹F)` is the canonical map, on the nose. -/
theorem geometricStalkPullbackSectionsSetIso_hom :
    (geometricStalkPullbackSectionsSetIso x).hom = geometricStalkToPullbackSectionsSet x :=
  rfl

end PullbackSections

/-! ### The specialization map of Section 0GJ2 for sheaves of sets -/

section Specialization

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (t : GeometricPoint (strictHenselization B S hS s))

/-- The germ-level map of the specialization map: the germ at `t ≫ p` of a section of a sheaf of
sets over an étale neighbourhood `(W, v)` of `s`, taken at the lift of `t ≫ p` determined by
`(W, v)`. -/
def specializationStalkStageSet (F : Sheaf (smallEtaleTopology S) (Type (u + 1)))
    (W : S.Etale) (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    F.obj.obj (op W) ⟶
      (smallEtaleStalkSet (t.hom ≫ strictHenselizationToBase B S hS s)).obj F :=
  (Scheme.pointSmallEtale (t.hom ≫ strictHenselizationToBase B S hS s)).toPresheafFiber W
    (specializationEtaleNeighborhoodLift B S hS s t W v) F.obj

/-- The germ-level maps of the specialization map are compatible with restriction along a
morphism of étale neighbourhoods. -/
theorem map_comp_specializationStalkStageSet (F : Sheaf (smallEtaleTopology S) (Type (u + 1)))
    {W V : S.Etale} (m : W ⟶ V) (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    F.obj.map m.op ≫ specializationStalkStageSet B S hS s t F W v =
      specializationStalkStageSet B S hS s t F V
        ((Scheme.pointSmallEtale s.hom).fiber.map m v) :=
  ((Scheme.pointSmallEtale (t.hom ≫ strictHenselizationToBase B S hS s)).toPresheafFiber_w m
      (specializationEtaleNeighborhoodLift B S hS s t W v) F.obj).trans
    (congrArg
      (fun w => (Scheme.pointSmallEtale
        (t.hom ≫ strictHenselizationToBase B S hS s)).toPresheafFiber V w F.obj)
      (specializationEtaleNeighborhoodLift_naturality B S hS s t m v))

/-- The naturality in the sheaf of the germ-level maps of the specialization map. -/
theorem specializationStalkStageSet_naturality
    {F G : Sheaf (smallEtaleTopology S) (Type (u + 1))} (α : F ⟶ G) (W : S.Etale)
    (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    α.hom.app (op W) ≫ specializationStalkStageSet B S hS s t G W v =
      specializationStalkStageSet B S hS s t F W v ≫
        (smallEtaleStalkSet (t.hom ≫ strictHenselizationToBase B S hS s)).map α :=
  ((Scheme.pointSmallEtale
    (t.hom ≫ strictHenselizationToBase B S hS s)).toPresheafFiber_naturality α.hom W
      (specializationEtaleNeighborhoodLift B S hS s t W v)).symm

/-- **The specialization map on stalks of sheaves of sets (Stacks, Section 0GJ2).** For a sheaf
of sets `F` on the small étale site of `S`, a geometric point `s` of `S` and a geometric point `t`
of the strict henselization `Spec(𝒪^{sh}_{S,s})`, the map `sp : F_s ⟶ F_{t ≫ p}` which carries
the germ at `s` of a section over an étale neighbourhood `(W, v)` of `s` to the germ at `t ≫ p`
of the same section over the same `W`, taken at the lift of `t ≫ p` determined by `(W, v)`;
natural in `F`. -/
def smallEtaleSpecializationStalkSet :
    smallEtaleStalkSet s.hom ⟶
      smallEtaleStalkSet (t.hom ≫ strictHenselizationToBase B S hS s) :=
  smallEtaleStalkSetDesc s.hom _ (specializationStalkStageSet B S hS s t)
    (fun F _ _ m v => map_comp_specializationStalkStageSet B S hS s t F m v)
    (fun α W v => specializationStalkStageSet_naturality B S hS s t α W v)

/-- The specialization map carries the germ at `s` of a section over an étale neighbourhood
`(W, v)` to the germ at `t ≫ p` of that section over `(W, v')`, where `v'` is the lift of the
specialized point determined by `(W, v)`. -/
theorem smallEtaleSpecializationStalkSet_toPresheafFiber
    (F : Sheaf (smallEtaleTopology S) (Type (u + 1))) (W : S.Etale)
    (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    (Scheme.pointSmallEtale s.hom).toPresheafFiber W v F.obj ≫
        (smallEtaleSpecializationStalkSet B S hS s t).app F =
      specializationStalkStageSet B S hS s t F W v :=
  toPresheafFiber_comp_smallEtaleStalkSetDesc s.hom _ (specializationStalkStageSet B S hS s t)
    (fun F _ _ m v => map_comp_specializationStalkStageSet B S hS s t F m v)
    (fun α W v => specializationStalkStageSet_naturality B S hS s t α W v) F W v

end Specialization

/-! ### The map from a stalk to sections over a scheme over the strict henselization -/

section StalkToSections

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)
  {T : Scheme.{u}} (q : T ⟶ strictHenselization B X hX x)

/-- The germ-level map: the restriction of a section of an étale sheaf of sets over an étale
neighbourhood `W` of `x` to a global section over `T` of its inverse image, along the composite
`T ⟶ Spec 𝒪^{sh}_{X,x} ⟶ W`. -/
def etaleStalkSectionsStageSet (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (W : X.Etale)
    (v : (Scheme.pointSmallEtale x.hom).fiber.obj W) :
    F.obj.obj (op W) ⟶
      (smallEtalePullbackSet (q ≫ strictHenselizationToBase B X hX x) ⋙
        Sheaf.Γ (smallEtaleTopology T) (Type (u + 1))).obj F :=
  (smallEtaleSectionsPullbackSet (q ≫ strictHenselizationToBase B X hX x) W
    (q ≫ strictHenselizationNeighborhoodLift B X hX x W v)
    (by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp])).app F

/-- The germ-level maps are compatible with restriction along a morphism of étale
neighbourhoods. -/
theorem map_comp_etaleStalkSectionsStageSet
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) {W V : X.Etale} (m : W ⟶ V)
    (v : (Scheme.pointSmallEtale x.hom).fiber.obj W) :
    F.obj.map m.op ≫ etaleStalkSectionsStageSet B X hX x q F W v =
      etaleStalkSectionsStageSet B X hX x q F V
        ((Scheme.pointSmallEtale x.hom).fiber.map m v) := by
  have hlift : (q ≫ strictHenselizationNeighborhoodLift B X hX x W v) ≫ m.left =
      q ≫ strictHenselizationNeighborhoodLift B X hX x V
        ((Scheme.pointSmallEtale x.hom).fiber.map m v) := by
    rw [Category.assoc, strictHenselizationNeighborhoodLift_comp_left]
  have hr : ∀ (U : X.Etale) (u : (Scheme.pointSmallEtale x.hom).fiber.obj U),
      (q ≫ strictHenselizationNeighborhoodLift B X hX x U u) ≫ U.hom =
        q ≫ strictHenselizationToBase B X hX x := fun U u => by
    rw [Category.assoc, strictHenselizationNeighborhoodLift_comp]
  have hrm : ((q ≫ strictHenselizationNeighborhoodLift B X hX x W v) ≫ m.left) ≫ V.hom =
      q ≫ strictHenselizationToBase B X hX x := by
    rw [hlift]
    exact hr _ _
  have h := map_comp_smallEtaleSectionsPullbackSet (q ≫ strictHenselizationToBase B X hX x) W
    (q ≫ strictHenselizationNeighborhoodLift B X hX x W v) m (hr W v) hrm
  exact congrArg (fun σ => NatTrans.app σ F)
    (h.trans (smallEtaleSectionsPullbackSet_congr (q ≫ strictHenselizationToBase B X hX x) V
      ((q ≫ strictHenselizationNeighborhoodLift B X hX x W v) ≫ m.left) hrm (hr V _) hlift))

/-- The map `F_x ⟶ Γ(T, g⁻¹F)` on sheaves of sets on the small étale site of `X`, for a scheme
`T` over the strict henselization at the geometric point `x` with structure morphism
`g : T ⟶ X`. On the germ of a section over an étale neighbourhood of `x` it is restriction of
that section along the composite `T ⟶ Spec 𝒪^{sh}_{X,x} ⟶ W`. -/
def etaleStalkToSectionsSet :
    smallEtaleStalkSet x.hom ⟶
      smallEtalePullbackSet (q ≫ strictHenselizationToBase B X hX x) ⋙
        Sheaf.Γ (smallEtaleTopology T) (Type (u + 1)) :=
  smallEtaleStalkSetDesc x.hom _ (etaleStalkSectionsStageSet B X hX x q)
    (fun F _ _ m v => map_comp_etaleStalkSectionsStageSet B X hX x q F m v)
    (fun α W v => (smallEtaleSectionsPullbackSet (q ≫ strictHenselizationToBase B X hX x) W
      (q ≫ strictHenselizationNeighborhoodLift B X hX x W v)
      (by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp])).naturality α)

/-- On the germ at `x` of a section over an étale neighbourhood `W`, the map on sheaves of sets is
restriction of that section along the composite `T ⟶ Spec 𝒪^{sh}_{X,x} ⟶ W`. -/
theorem etaleStalkToSectionsSet_toPresheafFiber
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (W : X.Etale)
    (v : (Scheme.pointSmallEtale x.hom).fiber.obj W) :
    (Scheme.pointSmallEtale x.hom).toPresheafFiber W v F.obj ≫
        (etaleStalkToSectionsSet B X hX x q).app F =
      etaleStalkSectionsStageSet B X hX x q F W v :=
  toPresheafFiber_comp_smallEtaleStalkSetDesc x.hom _ (etaleStalkSectionsStageSet B X hX x q)
    (fun F _ _ m v => map_comp_etaleStalkSectionsStageSet B X hX x q F m v)
    (fun α W v => (smallEtaleSectionsPullbackSet (q ≫ strictHenselizationToBase B X hX x) W
      (q ≫ strictHenselizationNeighborhoodLift B X hX x W v)
      (by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp])).naturality α) F W v

/-- **The map from an étale stalk of a sheaf of sets to sections is transitive in the scheme
over the strict henselization.** For schemes `T` and `T'` over `Spec 𝒪^{sh}_{X,x}` and a morphism
`c : T' ⟶ T` over it, the map `F_x ⟶ Γ(T', ·)` is the map `F_x ⟶ Γ(T, ·)` followed by
restriction of sections along `c`. -/
theorem etaleStalkToSectionsSet_comp_sectionsRestrictionSet {T' : Scheme.{u}} (c : T' ⟶ T)
    (q' : T' ⟶ strictHenselization B X hX x) (hq : c ≫ q = q') :
    etaleStalkToSectionsSet B X hX x q ≫
        smallEtaleSectionsRestrictionSet (q ≫ strictHenselizationToBase B X hX x) c
          (q' ≫ strictHenselizationToBase B X hX x)
          ((Category.assoc c q (strictHenselizationToBase B X hX x)).symm.trans
            (congrArg (fun y : T' ⟶ strictHenselization B X hX x =>
              y ≫ strictHenselizationToBase B X hX x) hq)) =
      etaleStalkToSectionsSet B X hX x q' := by
  ext F : 2
  refine smallEtaleStalkSet_hom_ext x.hom F fun W v => ?_
  refine (Category.assoc _ _ _).symm.trans
    ((congrArg (fun y => y ≫ _)
        (etaleStalkToSectionsSet_toPresheafFiber B X hX x q F W v)).trans
      ((congrArg (fun σ => NatTrans.app σ F)
          (smallEtaleSectionsPullbackSet_comp_sectionsRestrictionSet
            (q ≫ strictHenselizationToBase B X hX x) W c
            (q' ≫ strictHenselizationToBase B X hX x)
            (q ≫ strictHenselizationNeighborhoodLift B X hX x W v)
            (by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp])
            ((Category.assoc c q (strictHenselizationToBase B X hX x)).symm.trans
              (congrArg (fun y : T' ⟶ strictHenselization B X hX x =>
                y ≫ strictHenselizationToBase B X hX x) hq))
            (q' ≫ strictHenselizationNeighborhoodLift B X hX x W v)
            (by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp])
            (by rw [← Category.assoc, hq]))).trans
        (etaleStalkToSectionsSet_toPresheafFiber B X hX x q' F W v).symm))

end StalkToSections

/-! ### The first identification, and the remark -/

section SpecializationIso

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (t : GeometricPoint (strictHenselization B S hS s))

/-- **Stacks 03Q9 at the identity morphism of `S`, for sheaves of sets.** The canonical map
`F_s ⟶ Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)` of `AlgebraicGeometry.etaleStalkToSectionsSet`, taken at the
identity morphism of the strict henselization, is an isomorphism. -/
theorem isIso_etaleStalkToSectionsSet_id :
    IsIso (etaleStalkToSectionsSet B S hS s (𝟙 (strictHenselization B S hS s))) :=
  isIso_stalkToSectionsSet_of_isInitial
    (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s)
    (geometricPointToStrictHenselization B S hS s)
    (pointSmallEtaleClosedPointElement (geometricPointToStrictHenselization B S hS s)) rfl
    (isInitialPointSmallEtaleClosedPointElement
      (geometricPointToStrictHenselization B S hS s)
      (geometricPointToStrictHenselization_base_default B S hS s))
    (by rw [Category.id_comp]; exact geometricPointToStrictHenselization_comp B S hS s)
    (etaleStalkToSectionsSet B S hS s (𝟙 (strictHenselization B S hS s)))
    (fun W v => 𝟙 (strictHenselization B S hS s) ≫
      strictHenselizationNeighborhoodLift B S hS s W v)
    (fun W v => by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp])
    (fun W v => by
      rw [Category.id_comp]
      exact geometricPointToStrictHenselization_comp_neighborhoodLift B S hS s W v)
    (fun F W v => etaleStalkToSectionsSet_toPresheafFiber B S hS s
      (𝟙 (strictHenselization B S hS s)) F W v)

/-- **The first identification displayed in Stacks 0GJ3**, `F_s = Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)`,
for sheaves of sets: the stalk of an étale sheaf of sets at a geometric point `s` of `S` is the
set of global sections of its inverse image on the strict henselization at `s`, naturally in the
sheaf. The isomorphism is the canonical map `AlgebraicGeometry.etaleStalkToSectionsSet` at the
identity morphism of the strict henselization, invertible by Theorem 03Q9 applied to
`id_S : S ⟶ S` in degree zero. -/
def etaleStalkSectionsSetIso :
    smallEtaleStalkSet s.hom ≅
      smallEtalePullbackSet
          (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s) ⋙
        Sheaf.Γ (smallEtaleTopology (strictHenselization B S hS s)) (Type (u + 1)) :=
  letI := isIso_etaleStalkToSectionsSet_id B S hS s
  asIso (etaleStalkToSectionsSet B S hS s (𝟙 (strictHenselization B S hS s)))

/-- The identification `F_s = Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)` is the canonical map, on the nose. -/
theorem etaleStalkSectionsSetIso_hom :
    (etaleStalkSectionsSetIso B S hS s).hom =
      etaleStalkToSectionsSet B S hS s (𝟙 (strictHenselization B S hS s)) :=
  rfl

/-- **The specialization map is pullback by `t`, for sheaves of sets.** Composed with the
comparison `F_{t ≫ p} ⟶ Γ(t, (t ≫ p)⁻¹F)` of Lemma 03Q1, the specialization map on stalks is the
map `F_s ⟶ Γ(t, (t ≫ p)⁻¹F)` which restricts the germ at `s` of a section over an étale
neighbourhood `W` along the composite `t ⟶ Spec(𝒪^{sh}_{S,s}) ⟶ W`. -/
theorem etaleStalkToSectionsSet_eq_smallEtaleSpecializationStalkSet :
    etaleStalkToSectionsSet B S hS s t.hom =
      smallEtaleSpecializationStalkSet B S hS s t ≫
        geometricStalkToPullbackSectionsSet (t.hom ≫ strictHenselizationToBase B S hS s) := by
  ext F : 2
  refine smallEtaleStalkSet_hom_ext s.hom F fun W v => ?_
  rw [etaleStalkToSectionsSet_toPresheafFiber, NatTrans.comp_app]
  refine Eq.symm (Eq.trans (Eq.symm (Category.assoc
    ((Scheme.pointSmallEtale s.hom).toPresheafFiber W v F.obj)
    ((smallEtaleSpecializationStalkSet B S hS s t).app F)
    ((geometricStalkToPullbackSectionsSet
      (t.hom ≫ strictHenselizationToBase B S hS s)).app F))) ?_)
  rw [smallEtaleSpecializationStalkSet_toPresheafFiber]
  exact geometricStalkToPullbackSectionsSet_toPresheafFiber
    (t.hom ≫ strictHenselizationToBase B S hS s) F W
    (specializationEtaleNeighborhoodLift B S hS s t W v)

/-- **Stacks 0GJ3 (alternative description of the specialization map), for sheaves of sets.**
Let `S` be a scheme, `s` a geometric point of `S`, `p : Spec(𝒪^{sh}_{S,s}) ⟶ S` the structure
morphism of the strict henselization at `s`, and `t` a geometric point of `Spec(𝒪^{sh}_{S,s})`.
For every sheaf of sets `F` on the small étale site of `S`, use the two identifications

`F_s = Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)`  and  `F_{t ≫ p} = Γ(t, t⁻¹p⁻¹F)`,

the first of which is Theorem 03Q9 applied to `id_S : S ⟶ S` and the second Lemma 03Q1. Then the
specialization map `sp : F_s ⟶ F_{t ≫ p}` of Section 0GJ2 *is* the map induced between them by
pullback of sections along `t`: it is the composite of the first identification, the
restriction of sections along `t`, and the inverse of the second, as natural transformations of
functors on sheaves of sets.

Here the first identification is `AlgebraicGeometry.etaleStalkSectionsSetIso`, the second is
`AlgebraicGeometry.geometricStalkPullbackSectionsSetIso`, restriction of sections along `t` is
`Stacks.EtaleCohomology.smallEtaleSectionsRestrictionSet`, and `sp` is
`AlgebraicGeometry.smallEtaleSpecializationStalkSet`. -/
@[stacks 0GJ3 "for every sheaf of sets F on the small étale site of S: sp : F_s ⟶ F_{t ≫ p} \
of Section 0GJ2 equals the identification F_s ≅ Γ(Spec 𝒪^sh_{S,s}, p⁻¹F) (03Q9 at id_S), \
followed by pullback of sections along t, followed by the inverse of the identification \
F_{t ≫ p} ≅ Γ(t, t⁻¹p⁻¹F) (03Q1); both identifications are proved to be isomorphisms"]
theorem smallEtaleSpecializationStalkSet_eq_sectionsRestrictionSet :
    smallEtaleSpecializationStalkSet B S hS s t =
      (etaleStalkSectionsSetIso B S hS s).hom ≫
        smallEtaleSectionsRestrictionSet
            (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s) t.hom
            (t.hom ≫ strictHenselizationToBase B S hS s)
            ((Category.assoc t.hom (𝟙 (strictHenselization B S hS s))
                (strictHenselizationToBase B S hS s)).symm.trans
              (congrArg (fun y : t.source ⟶ strictHenselization B S hS s =>
                y ≫ strictHenselizationToBase B S hS s) (Category.comp_id t.hom))) ≫
          (geometricStalkPullbackSectionsSetIso
            (t.hom ≫ strictHenselizationToBase B S hS s)).inv :=
  ((Iso.eq_comp_inv _).mpr
      (((etaleStalkToSectionsSet_comp_sectionsRestrictionSet B S hS s
          (𝟙 (strictHenselization B S hS s)) t.hom t.hom (Category.comp_id t.hom)).trans
        (etaleStalkToSectionsSet_eq_smallEtaleSpecializationStalkSet B S hS s t)).symm)).trans
    (Category.assoc _ _ _)

end SpecializationIso

end AlgebraicGeometry

end
