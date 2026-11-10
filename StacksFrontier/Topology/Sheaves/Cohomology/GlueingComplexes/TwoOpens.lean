module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.KInjectiveRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.OpenImmersionPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.UnboundedDerivedPushforward

/-!
# Glueing objects of the derived category along a cover by two opens

Let `X` be a ringed space covered by two open subspaces `U` and `V` with intersection `W`. An
object `A` of `D(𝒪_U)`, an object `B` of `D(𝒪_V)` and an isomorphism `c : A|_W ≅ B|_W` are the
glueing data of [Stacks, Tag 08DG]; they come from an object `F` of `D(𝒪_X)` whose restrictions
to `U` and to `V` are `A` and `B`, compatibly with `c`, and — once `U` and `V` cover `X` — every
pair of maps from `A` and from `B` into the two restrictions of an object `E` of `D(𝒪_X)` that
agrees on `W` through `c` comes from a map `F ⟶ E`.

The glued object is the fibre of the difference map
`Rj_{U*}A ⊕ Rj_{V*}B ⟶ Rj_{W*}(B|_W)` built from the two unit maps and from `c`. Restricting
that triangle to `U` makes the second component of the difference invertible, so the restricted
triangle is the biproduct triangle of `A` and the third term, which exhibits `F|_U ≅ A`; the
same argument on `V` gives `F|_V ≅ B`.

## Main definitions

* `Stacks.Cohomology.GlueingComplexes.derivedRestrict` — restriction of unbounded derived
  modules along a morphism of ringed spaces, as derived pullback.
* `Stacks.Cohomology.GlueingComplexes.overlapIso` — the canonical comparison of the two
  iterated restrictions to the intersection.
* `Stacks.Cohomology.GlueingComplexes.Glueing` — an object of `D(𝒪_X)` together with
  isomorphisms identifying its two restrictions with `A` and `B`, compatibly with `c`.

## Main results

* `Stacks.Cohomology.GlueingComplexes.exists_glueing` — **[Stacks, Tag 08DG]**: glueing data
  along a cover by two opens comes from an object of `D(𝒪_X)`.
* `Stacks.Cohomology.GlueingComplexes.exists_hom_of_compatible` — **[Stacks, Tag 08DG]**: for a
  cover, a pair of maps `A ⟶ E|_U` and `B ⟶ E|_V` agreeing on `W` through `c` comes from a map
  out of the glued object.
* `Stacks.Cohomology.GlueingComplexes.isZero_of_restrict_isZero` and
  `Stacks.Cohomology.GlueingComplexes.isIso_of_restrict_isIso` — restriction to the two members
  of a cover detects vanishing, and detects invertibility.

## Implementation notes

The two opens and their intersection are presented by a Cartesian square of open immersions of
ringed spaces rather than by two elements of `Opens X`, so that the restricted structure sheaves
are never identified by definitional unfolding.

Restriction is derived pullback. Along an open immersion that is the honest restriction: pullback
of sheaves of modules along an open immersion is exact
(`Stacks.Cohomology.openImmersionModulePullback_preservesHomology`), so the canonical
comparison from the derived pullback to the degreewise one is invertible, and the derived
pullback is simultaneously a *right* derived functor of the degreewise pullback. That second
reading is what lets the restriction of a derived direct image be computed by
[Stacks, Tag 08FE].

The glued object is the third vertex of a distinguished triangle, so it is determined only up to
isomorphism; this is why the source, and the statement below, assert existence. The compatibility
with `c` is not an extra condition imposed afterwards but a consequence of the triangle: the
composite of the two components of `F ⟶ Rj_{U*}A ⊕ Rj_{V*}B` with the difference map vanishes,
and transposing that identity across the two adjunctions is exactly the required equality. That
transposition is a bijection (`cone_of_overlap_eq` is the converse of `overlap_eq_of_cone`), and
it is the converse direction that the second half of the tag uses: a compatible pair of maps is
*precisely* a cone over the difference map, hence factors through its fibre.

The second half of the tag does need the cover, and uses it exactly once: an object of `D(𝒪_X)`
is the glueing of its own two restrictions, which is the assertion that the canonical map from
`E` to the fibre of the difference map of that glueing datum — the factorisation of the pair of
adjunction units, which is inverse on each open to the identification of the first half — is
invertible. Restriction to the two members of a cover detects invertibility: that is
`isIso_of_restrict_isIso`, read off the relative Mayer--Vietoris triangle of
[Stacks, Tag 08HZ] at the identity of `X`, where the four derived direct images of the triangle
become the identity functor and the three restricted direct images attached to `U`, `V` and
`U ∩ V`.

## References

* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.GlueingComplexes

universe u

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- The unbounded derived category of modules on a ringed space. -/
abbrev DerivedModules (X : RingedSpace.{u, u}) :=
  DerivedCategory (SheafOfModules.{u} (structureSheafRing X))

/-- Restriction of unbounded derived modules along a morphism of ringed spaces, taken as the
derived pullback. Along an open immersion it is the honest restriction. -/
abbrev derivedRestrict {Y X : RingedSpace.{u, u}} (j : Y ⟶ X) :
    DerivedModules X ⥤ DerivedModules Y :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback j

/-- The derived direct image of unbounded derived modules. -/
abbrev derivedPush {Y X : RingedSpace.{u, u}} (j : Y ⟶ X) :
    DerivedModules Y ⥤ DerivedModules X :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward j

/-- Transport of restriction along an equality of morphisms. -/
def restrictEqIso {X W : RingedSpace.{u, u}} {f g : W ⟶ X} (h : f = g) :
    derivedRestrict f ≅ derivedRestrict g :=
  eqToIso (congrArg (fun k : W ⟶ X => derivedRestrict k) h)

/-- Transport of derived direct image along an equality of morphisms. -/
def pushEqIso {X W : RingedSpace.{u, u}} {f g : W ⟶ X} (h : f = g) :
    derivedPush f ≅ derivedPush g :=
  eqToIso (congrArg (fun k : W ⟶ X => derivedPush k) h)

/-- For a commutative square of morphisms of ringed spaces, the canonical comparison between
the two iterated restrictions to the common source. -/
def overlapIso {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X)
    (iU : W ⟶ U) (iV : W ⟶ V) (h : iU ≫ jU = iV ≫ jV) :
    derivedRestrict jU ⋙ derivedRestrict iU ≅ derivedRestrict jV ⋙ derivedRestrict iV :=
  Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iU jU ≪≫
    restrictEqIso h ≪≫
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iV jV).symm

private theorem overlapIso_inv {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X)
    (iU : W ⟶ U) (iV : W ⟶ V) (h : iU ≫ jU = iV ≫ jV) :
    (overlapIso jU jV iU iV h).inv =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iV jV).hom ≫
        (restrictEqIso h).inv ≫
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iU jU).inv := by
  simp [overlapIso, Iso.trans_inv, Iso.symm_inv, Category.assoc]

/-- `Stacks.Cohomology.GlueingComplexes.overlapIso_inv` read at an object, with the three
components displayed.

The splitting of the components is `CategoryTheory.NatTrans.comp_app`, which holds by
definition, but it is taken here as a definitional unification against a *stated* type rather
than by `simp only [NatTrans.comp_app]`: matching that rewrite against a goal in which the
transport `restrictEqIso` meets the two composition isomorphisms makes the unifier compare the
derived pullbacks along `iU ≫ jU` and along `iV ≫ jV`, and that does not terminate inside the
heartbeat budget. -/
private theorem overlapIso_inv_app {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X)
    (iU : W ⟶ U) (iV : W ⟶ V) (h : iU ≫ jU = iV ≫ jV) (F : DerivedModules X) :
    (overlapIso jU jV iU iV h).inv.app F =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iV jV).hom.app F ≫
        (restrictEqIso h).inv.app F ≫
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iU jU).inv.app F :=
  congrArg (fun α => α.app F) (overlapIso_inv jU jV iU iV h)

/-! ### Elementary lemmas on biproducts and isomorphisms -/

private lemma isoCancelRight {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y) (e : Y ≅ Z) :
    (f ≫ e.hom) ≫ e.inv = 𝟙 X ≫ f := by
  simp [Category.assoc]

private lemma isoInvPrecompEq {C : Type*} [Category C] {A B Z : C} (e : A ≅ B) (f : A ⟶ Z)
    (g : B ⟶ Z) (h : e.inv ≫ f = g) : f = e.hom ≫ g := by
  apply (cancel_epi e.inv).1
  simpa [Category.assoc] using h

private lemma eq_natIso_hom_comp {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (θ : F ≅ G) (K : C) {Z : D} (x : F.obj K ⟶ Z) (y : G.obj K ⟶ Z)
    (hxy : θ.inv.app K ≫ x = y) : x = θ.hom.app K ≫ y := by
  rw [← hxy, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

private lemma eq_inv_comp_of_hom_comp_eq {C : Type*} [Category C] {A B Z : C} (e : A ≅ B)
    (f : B ⟶ Z) (g : A ⟶ Z) (hfg : e.hom ≫ f = g) : f = e.inv ≫ g := by
  rw [← hfg, Iso.inv_hom_id_assoc]

/-- **The backward half of `Stacks.Cohomology.GlueingComplexes.overlap_eq_iff_mid`, in a single
arbitrary category with every object and every morphism a variable.**

`e₁` is the composition isomorphism on the `V` side, `e₂` the transport along the equality of
the two factorisations, `e₃` the composition isomorphism on the `U` side; `m` and `n` are the
two restricted composites, which the caller splits by `CategoryTheory.Functor.map_comp`
through `hm` and `hn`.

It is stated this way, and applied by `exact`, because the rewriting tactics do not survive the
goal in its own context: the three isomorphisms live over three different spellings of one
restriction, and matching a rewrite against them makes the unifier compare the derived pullbacks
along `iU ≫ jU` and along `iV ≫ jV`, which exceeds the heartbeat budget. -/
private lemma transportBack {C : Type*} [Category C] {w x y p aU aV bU bV : C}
    {e₁ : w ⟶ x} {e₁' : x ⟶ w} {e₂' : x ⟶ y} {e₃' : y ⟶ p}
    {m : p ⟶ bU} {γ : bU ⟶ bV} {n : w ⟶ bV}
    {α : p ⟶ aU} {β : aU ⟶ bU} {δ : w ⟶ aV} {ε : aV ⟶ bV}
    (he : e₁' ≫ e₁ = 𝟙 x) (hm : m = α ≫ β) (hn : n = δ ≫ ε)
    (hh : (e₁ ≫ e₂' ≫ e₃') ≫ m ≫ γ = n) :
    e₂' ≫ e₃' ≫ (α ≫ β) ≫ γ = e₁' ≫ (δ ≫ ε) := by
  subst hm
  subst hn
  rw [← hh]
  simp only [Category.assoc]
  rw [← Category.assoc e₁' e₁, he, Category.id_comp]

private lemma compBiprodDesc {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {A B Z T : C} (f : T ⟶ A ⊞ B) (g : A ⟶ Z) (h : B ⟶ Z) :
    f ≫ biprod.desc g h = (f ≫ biprod.fst) ≫ g + (f ≫ biprod.snd) ≫ h := by
  rw [Limits.biprod.desc_eq, Preadditive.comp_add]
  simp [Category.assoc]

private lemma biprodDescNegZero {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {A B Z T : C} (f : T ⟶ A ⊞ B) (g : A ⟶ Z) (h : B ⟶ Z)
    (hz : f ≫ biprod.desc g (-h) = 0) :
    (f ≫ biprod.fst) ≫ g = (f ≫ biprod.snd) ≫ h := by
  have hs : (f ≫ biprod.fst) ≫ g + (f ≫ biprod.snd) ≫ (-h) = 0 := by
    rw [compBiprodDesc] at hz
    exact hz
  have hs' : ((f ≫ biprod.fst) ≫ g) - ((f ≫ biprod.snd) ≫ h) = 0 := by
    have hneg := Preadditive.comp_neg (f ≫ biprod.snd) h
    rw [sub_eq_add_neg, ← hneg]
    exact hs
  exact sub_eq_zero.mp hs'

private lemma biprodLiftDescNegZero {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {A B Z T : C} (p : T ⟶ A) (q : T ⟶ B) (g : A ⟶ Z) (k : B ⟶ Z)
    (hpq : p ≫ g = q ≫ k) : biprod.lift p q ≫ biprod.desc g (-k) = 0 := by
  rw [compBiprodDesc]
  simp [hpq]

private lemma comp_biprodLift_components {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {A B S T : C} (χ : T ⟶ S) (f : S ⟶ A ⊞ B) (p : T ⟶ A) (q : T ⟶ B)
    (hχ : biprod.lift p q = χ ≫ f) :
    χ ≫ f ≫ biprod.fst = p ∧ χ ≫ f ≫ biprod.snd = q := by
  constructor
  · rw [← Category.assoc, ← hχ, biprod.lift_fst]
  · rw [← Category.assoc, ← hχ, biprod.lift_snd]

private lemma mapBiprodFst {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C]
    [HasZeroMorphisms D] [HasBinaryBiproducts C] [HasBinaryBiproducts D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] {X Y : C} [PreservesBinaryBiproduct X Y F] :
    (F.mapBiprod X Y).hom ≫ biprod.fst = F.map biprod.fst := by
  rw [Functor.mapBiprod_hom]
  exact biprod.lift_fst _ _

private lemma mapBiprodSnd {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C]
    [HasZeroMorphisms D] [HasBinaryBiproducts C] [HasBinaryBiproducts D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] {X Y : C} [PreservesBinaryBiproduct X Y F] :
    (F.mapBiprod X Y).hom ≫ biprod.snd = F.map biprod.snd := by
  rw [Functor.mapBiprod_hom]
  exact biprod.lift_snd _ _

/-! ### The glueing datum -/

/-- Two identifications of the restrictions of `F` agree on the intersection, through `c`: the
transition isomorphism `g|_W ∘ (f|_W)⁻¹` is the canonical comparison `c`. -/
def CompatibleOnOverlap {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X) (iU : W ⟶ U)
    (iV : W ⟶ V) (h : iU ≫ jU = iV ≫ jV) {A : DerivedModules U} {B : DerivedModules V}
    (c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B) (F : DerivedModules X)
    (f : (derivedRestrict jU).obj F ≅ A) (g : (derivedRestrict jV).obj F ≅ B) : Prop :=
  (derivedRestrict iU).map f.hom ≫ c.hom =
    (overlapIso jU jV iU iV h).hom.app F ≫ (derivedRestrict iV).map g.hom

/-- An object of `D(𝒪_X)` identified with prescribed objects on the two members of a cover by
two opens, compatibly on their intersection. -/
structure Glueing {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X) (iU : W ⟶ U)
    (iV : W ⟶ V) (h : iU ≫ jU = iV ≫ jV) (A : DerivedModules U) (B : DerivedModules V)
    (c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B) where
  /-- The glued object on `X`. -/
  F : DerivedModules X
  /-- The identification of its restriction to `U` with `A`. -/
  f : (derivedRestrict jU).obj F ≅ A
  /-- The identification of its restriction to `V` with `B`. -/
  g : (derivedRestrict jV).obj F ≅ B
  /-- The two identifications agree on the intersection, through `c`. -/
  compatible : CompatibleOnOverlap jU jV iU iV h c F f g

/-! ### Restricting a derived direct image -/

/-- The canonical map `Rj_* A ⟶ R(i ≫ j)_* (A|_U')` attached to a morphism `i` into the source
of `j`: the unit of `Li^* ⊣ Ri_*` followed by the composition isomorphism for derived direct
image. -/
def pushforwardRestrictionMap {X U W : RingedSpace.{u, u}} (j : U ⟶ X) (i : W ⟶ U)
    (A : DerivedModules U) :
    (derivedPush j).obj A ⟶ (derivedPush (i ≫ j)).obj ((derivedRestrict i).obj A) :=
  (derivedPush j).map
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction i).unit.app A) ≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso i j).hom.app
      ((derivedRestrict i).obj A)

/-- The counit identity for a composite of two adjunctions, in the shape in which the two
composition isomorphisms of derived pullback and derived direct image present it. -/
private lemma adjunctionComp_counit_unit_bridge {C D E : Type u} [Category C] [Category D]
    [Category E] (P : C ⥤ D) (Q : D ⥤ E) (R : D ⥤ C) (S : E ⥤ D) (H : C ⥤ E) (T : E ⥤ C)
    (p : P ⋙ Q ≅ H) (r : S ⋙ R ≅ T) (adjP : P ⊣ R) (adjQ : Q ⊣ S) (adjH : H ⊣ T)
    (hcomp : ∀ (K : E), H.map (r.hom.app K) ≫ adjH.counit.app K =
      p.inv.app (R.obj (S.obj K)) ≫ Q.map (adjP.counit.app (S.obj K)) ≫ adjQ.counit.app K)
    (A : D) :
    p.hom.app (R.obj A) ≫
        H.map (R.map (adjQ.unit.app A) ≫ r.hom.app (Q.obj A)) ≫ adjH.counit.app (Q.obj A) =
      Q.map (adjP.counit.app A) := by
  have hnatp := p.inv.naturality (R.map (adjQ.unit.app A))
  have hnatp' : H.map (R.map (adjQ.unit.app A)) ≫ p.inv.app (R.obj (S.obj (Q.obj A))) =
      p.inv.app (R.obj A) ≫ (P ⋙ Q).map (R.map (adjQ.unit.app A)) := by
    simpa only [Functor.comp_obj, Functor.id_obj] using hnatp
  calc
    _ = p.hom.app (R.obj A) ≫ H.map (R.map (adjQ.unit.app A)) ≫
          H.map (r.hom.app (Q.obj A)) ≫ adjH.counit.app (Q.obj A) := by
          simp only [Functor.map_comp, Category.assoc]
    _ = p.hom.app (R.obj A) ≫ H.map (R.map (adjQ.unit.app A)) ≫
          p.inv.app (R.obj (S.obj (Q.obj A))) ≫
          Q.map (adjP.counit.app (S.obj (Q.obj A))) ≫ adjQ.counit.app (Q.obj A) := by
          rw [hcomp]
    _ = p.hom.app (R.obj A) ≫
          (p.inv.app (R.obj A) ≫ (P ⋙ Q).map (R.map (adjQ.unit.app A))) ≫
          Q.map (adjP.counit.app (S.obj (Q.obj A))) ≫ adjQ.counit.app (Q.obj A) := by
          calc
            _ = p.hom.app (R.obj A) ≫
                  (H.map (R.map (adjQ.unit.app A)) ≫
                    p.inv.app (R.obj (S.obj (Q.obj A)))) ≫
                  Q.map (adjP.counit.app (S.obj (Q.obj A))) ≫ adjQ.counit.app (Q.obj A) := by
                  simp only [Category.assoc]
            _ = _ := by
                simpa only [Category.assoc] using
                  congrArg (fun z => p.hom.app (R.obj A) ≫ z ≫
                    (Q.map (adjP.counit.app (S.obj (Q.obj A))) ≫
                      adjQ.counit.app (Q.obj A))) hnatp'
    _ = (P ⋙ Q).map (R.map (adjQ.unit.app A)) ≫
          Q.map (adjP.counit.app (S.obj (Q.obj A))) ≫ adjQ.counit.app (Q.obj A) := by
          simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    _ = Q.map (P.map (R.map (adjQ.unit.app A)) ≫ adjP.counit.app (S.obj (Q.obj A))) ≫
          adjQ.counit.app (Q.obj A) := by
          simpa only [Functor.comp_map, Category.assoc] using
            congrArg (fun z => z ≫ adjQ.counit.app (Q.obj A))
              (Q.map_comp (P.map (R.map (adjQ.unit.app A)))
                (adjP.counit.app (S.obj (Q.obj A)))).symm
    _ = Q.map (adjP.counit.app A ≫ adjQ.unit.app A) ≫ adjQ.counit.app (Q.obj A) := by
          simp
    _ = Q.map (adjP.counit.app A) := by
          simp [Category.assoc, Functor.map_comp, adjQ.left_triangle_components A]

/-- Restricting `pushforwardRestrictionMap` to the intersection and composing with the counit
there recovers the restriction of the counit on `U`. -/
private lemma pushforwardRestrictionMap_counit {X U W : RingedSpace.{u, u}} (j : U ⟶ X)
    (i : W ⟶ U) (A : DerivedModules U) :
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical i j).hom.app
        ((derivedPush j).obj A) ≫
      (derivedRestrict (i ≫ j)).map (pushforwardRestrictionMap j i A) ≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
        (i ≫ j)).counit.app ((derivedRestrict i).obj A) =
    (derivedRestrict i).map
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction j).counit.app A) := by
  simpa only [pushforwardRestrictionMap] using
    (adjunctionComp_counit_unit_bridge
      (P := derivedRestrict j) (Q := derivedRestrict i) (R := derivedPush j)
      (S := derivedPush i) (H := derivedRestrict (i ≫ j)) (T := derivedPush (i ≫ j))
      (p := Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical i j)
      (r := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso i j)
      (adjP := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction j)
      (adjQ := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction i)
      (adjH := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction (i ≫ j))
      (hcomp :=
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_comp_counit i j)
      A)

private theorem eqTransport {α : Sort*} {a b : α} (w : a = b) (P : ∀ {x y : α}, x = y → Prop)
    (h : P (Eq.refl a)) : P w := by
  cases w
  exact h

private lemma natIsoMapCounitBridge {C D : Type*} [Category C] [Category D] (F H : C ⥤ D)
    (e : F ≅ H) {X₀ X₁ X₂ : C} {Y : D} (q : X₀ ⟶ X₁) (t : X₁ ⟶ X₂) (epsK : F.obj X₁ ⟶ Y)
    (epsL : H.obj X₂ ⟶ Y) (s : F.obj X₀ ⟶ Y)
    (hEq : H.map t ≫ epsL = e.inv.app X₁ ≫ epsK)
    (hNat : H.map q ≫ e.inv.app X₁ = e.inv.app X₀ ≫ F.map q)
    (hLocal : F.map q ≫ epsK = s) :
    H.map q ≫ H.map t ≫ epsL = e.inv.app X₀ ≫ s := by
  calc
    _ = H.map q ≫ (e.inv.app X₁ ≫ epsK) := by rw [hEq]
    _ = e.inv.app X₀ ≫ F.map q ≫ epsK := by rw [← Category.assoc, hNat, Category.assoc]
    _ = e.inv.app X₀ ≫ s := by rw [hLocal]

/-! ### Restriction along an open immersion is exact -/

private lemma modulePullback_preservesFiniteLimits {X U : RingedSpace.{u, u}} (i : U ⟶ X)
    [SheafedSpace.IsOpenImmersion i] : PreservesFiniteLimits (modulePullback i) :=
  let := Stacks.Cohomology.openImmersionModulePullback_preservesHomology i
  (modulePullback i).preservesFiniteLimits_of_preservesHomology

private lemma modulePullback_preservesFiniteColimits {X U : RingedSpace.{u, u}} (i : U ⟶ X)
    [SheafedSpace.IsOpenImmersion i] : PreservesFiniteColimits (modulePullback i) :=
  let := Stacks.Cohomology.openImmersionModulePullback_preservesHomology i
  (modulePullback i).preservesFiniteColimits_of_preservesHomology

private lemma openImmersionDerivedPullbackComparison_isIso {X U : RingedSpace.{u, u}}
    (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i] :
    IsIso (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison i) := by
  let := modulePullback_preservesFiniteLimits i
  let := modulePullback_preservesFiniteColimits i
  let : (modulePullback i).PreservesHomology := Functor.preservesHomologyOfExact _
  exact Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback i)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison i)
    (Stacks.DerivedFunctor.HigherDerivedOfExact.mapHomotopyCategory_inverts_quasiIso
      (modulePullback i))

/-- Along an open immersion the derived pullback is also a *right* derived functor of the
degreewise pullback, the latter being exact. -/
private def openImmersionDerivedPullbackUnitIso {X U : RingedSpace.{u, u}} (i : U ⟶ X)
    [SheafedSpace.IsOpenImmersion i] :
    (modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      DerivedCategory.Qh ⋙ derivedRestrict i :=
  let := openImmersionDerivedPullbackComparison_isIso i
  (asIso (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison i)).symm

private theorem openImmersionDerivedPullback_isRightDerivedFunctor {X U : RingedSpace.{u, u}}
    (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i] :
    (derivedRestrict i).IsRightDerivedFunctor (openImmersionDerivedPullbackUnitIso i).hom
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (derivedRestrict i) (openImmersionDerivedPullbackUnitIso i).symm

/-- [Stacks, Tag 08FE] for the chosen derived direct images and the derived pullbacks along the
two open immersions of a Cartesian square. -/
private def pushforwardRestrictIso {X Y U V : RingedSpace.{u, u}} (f : X ⟶ Y) (i : U ⟶ X)
    (j : V ⟶ Y) (g : U ⟶ V) [SheafedSpace.IsOpenImmersion i] [SheafedSpace.IsOpenImmersion j]
    (h : IsPullback i g f j) :
    derivedPush f ⋙ derivedRestrict j ≅ derivedRestrict i ⋙ derivedPush g :=
  let := openImmersionDerivedPullback_isRightDerivedFunctor i
  let := openImmersionDerivedPullback_isRightDerivedFunctor j
  Stacks.Cohomology.derivedPushforwardRestrictIso f i j g h (derivedPush f) (derivedPush g)
    (derivedRestrict i) (derivedRestrict j)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit g)
    (openImmersionDerivedPullbackUnitIso i).hom (openImmersionDerivedPullbackUnitIso j).hom

/-! ### The identity morphism -/

private def mapHomotopyCategoryIdIso {C : Type*} [Category C] [Preadditive C] (F : C ⥤ C)
    [F.Additive] (e : F ≅ 𝟭 C) :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ≅ 𝟭 (HomotopyCategory C (ComplexShape.up ℤ)) := by
  apply Quotient.natIsoLift
  exact F.mapHomotopyCategoryFactors (ComplexShape.up ℤ) ≪≫
    Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ))
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)) ≪≫
    Functor.leftUnitor (HomotopyCategory.quotient C (ComplexShape.up ℤ)) ≪≫
    (Functor.rightUnitor (HomotopyCategory.quotient C (ComplexShape.up ℤ))).symm

private def derivedPushIdIso (X : RingedSpace.{u, u}) : derivedPush (𝟙 X) ≅ 𝟭 _ := by
  let C := SheafOfModules.{u} (structureSheafRing X)
  let W := HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
  let e : DerivedCategory.Qh (C := C) ⋙ 𝟭 (DerivedCategory C) ≅
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pushforwardToDerivedCategory (𝟙 X) :=
    Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight
        (mapHomotopyCategoryIdIso (modulePushforward (𝟙 X))
          (RingedSpaceModuleAdjunction.modulePushforwardId X)).symm
        DerivedCategory.Qh
  let : (𝟭 (DerivedCategory C)).IsRightDerivedFunctor e.inv W :=
    Functor.isRightDerivedFunctor_of_inverts W (𝟭 (DerivedCategory C)) e
  exact Functor.rightDerivedUnique (derivedPush (𝟙 X)) (𝟭 (DerivedCategory C))
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit (𝟙 X)) e.inv W

private def derivedRestrictIdIso (X : RingedSpace.{u, u}) : derivedRestrict (𝟙 X) ≅ 𝟭 _ := by
  let C := SheafOfModules.{u} (structureSheafRing X)
  let W := HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
  let e : DerivedCategory.Qh (C := C) ⋙ 𝟭 (DerivedCategory C) ≅
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy (𝟙 X) :=
    Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight
        (mapHomotopyCategoryIdIso (modulePullback (𝟙 X))
          (Stacks.PullbackPseudofunctor.modulePullbackIdIso X)).symm
        DerivedCategory.Qh
  let := Functor.isLeftDerivedFunctor_of_inverts W (𝟭 (DerivedCategory C)) e
  exact Functor.leftDerivedUnique _ _
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison (𝟙 X)) e.hom W

/-- The comparison exhibiting `Rj_* ⋙ Lj^*` as the identity for an open immersion `j`: the
Cartesian square with both vertical maps `j` and both horizontal maps the identity. -/
private def derivedPushRestrictSelfComparison {X U : RingedSpace.{u, u}} (j : U ⟶ X)
    [SheafedSpace.IsOpenImmersion j] :
    derivedPush j ⋙ derivedRestrict j ≅ 𝟭 (DerivedModules U) :=
  pushforwardRestrictIso j (𝟙 U) j (𝟙 U) (IsPullback.of_vert_isIso_mono ⟨by simp⟩) ≪≫
    Functor.isoWhiskerRight (derivedRestrictIdIso U) (derivedPush (𝟙 U)) ≪≫
    Functor.isoWhiskerLeft (𝟭 (DerivedModules U)) (derivedPushIdIso U) ≪≫
    Functor.leftUnitor (𝟭 (DerivedModules U))

/-- Restricting the derived direct image along an open immersion back to its source returns the
object: the counit of `Lj^* ⊣ Rj_*` is invertible. -/
private def derivedPushRestrictSelfIso {X U : RingedSpace.{u, u}} (j : U ⟶ X)
    [SheafedSpace.IsOpenImmersion j] :
    derivedPush j ⋙ derivedRestrict j ≅ 𝟭 (DerivedModules U) :=
  let : IsIso (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction j).counit :=
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction j).isIso_counit_of_iso
      (derivedPushRestrictSelfComparison j)
  asIso (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction j).counit

private lemma derivedPushRestrictSelfIso_hom_app {X U : RingedSpace.{u, u}} (j : U ⟶ X)
    [SheafedSpace.IsOpenImmersion j] (A : DerivedModules U) :
    (derivedPushRestrictSelfIso j).hom.app A =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction j).counit.app A :=
  rfl

/-! ### Splitting off a biproduct summand in a distinguished triangle -/

private lemma isIso_triangle_front_of_biprod_desc {C : Type u} [Category C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [HasShift C ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C] {F A B Z : C}
    (f : F ⟶ A ⊞ B) (d : A ⊞ B ⟶ Z) (δ : Z ⟶ F⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f d δ ∈ distTriang C) (a : A ⟶ Z) (b : B ⟶ Z) (hb : IsIso b)
    (hd : d = biprod.desc a (-b)) : IsIso (f ≫ biprod.fst) := by
  let T := Triangle.mk f d δ
  let T' := Pretriangulated.binaryBiproductTriangle A Z
  let q : A ⊞ B ⟶ A ⊞ Z := biprod.lift biprod.fst d
  have hq : IsIso q := by
    change IsIso (biprod.lift biprod.fst d)
    rw [hd]
    let r : A ⊞ Z ⟶ A ⊞ B :=
      biprod.desc (biprod.lift (𝟙 A) (a ≫ inv b)) ((-(inv b)) ≫ biprod.inr)
    have hr₁ : biprod.lift biprod.fst (biprod.desc a (-b)) ≫ r = 𝟙 _ := by
      ext <;> simp [r, Category.assoc, ← sub_eq_add_neg]
    have hr₂ : r ≫ biprod.lift biprod.fst (biprod.desc a (-b)) = 𝟙 _ := by
      ext <;> simp [r]
    exact ⟨⟨r, hr₁, hr₂⟩⟩
  have hqSnd : q ≫ biprod.snd = d := by simp [q]
  have : IsSplitEpi d :=
    IsSplitEpi.mk' ⟨(-(inv b)) ≫ biprod.inr, by simp [hd]⟩
  have hz : δ = 0 := by
    have hδ : d ≫ δ = 0 := by simpa [T] using (comp_distTriang_mor_zero₂₃ T hT)
    apply (cancel_epi d).1
    simpa using hδ
  have hfd : f ≫ d = 0 := comp_distTriang_mor_zero₁₂ T hT
  let φ : T ⟶ T' := Triangle.homMk T T' (T.mor₁ ≫ biprod.fst) q (𝟙 _)
    (by
      change f ≫ q = (f ≫ biprod.fst) ≫ biprod.inl
      apply biprod.hom_ext
      · simp [q]
      · simp [q, hfd])
    (by
      change d ≫ 𝟙 Z = q ≫ biprod.snd
      simpa only [Category.comp_id] using hqSnd.symm)
    (by
      change δ ≫ (f ≫ biprod.fst)⟦(1 : ℤ)⟧' = 𝟙 Z ≫ 0
      simp [hz])
  exact Pretriangulated.isIso₁_of_isIso₂₃ φ hT
    (Pretriangulated.binaryBiproductTriangle_distinguished A Z) hq (by
      change IsIso (𝟙 Z)
      infer_instance)

private lemma isIso_triangle_snd_of_biprod_desc {C : Type u} [Category C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [HasShift C ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C] {F A B Z : C}
    (f : F ⟶ A ⊞ B) (d : A ⊞ B ⟶ Z) (δ : Z ⟶ F⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f d δ ∈ distTriang C) (a : A ⟶ Z) (b : B ⟶ Z) (ha : IsIso a)
    (hd : d = biprod.desc a (-b)) : IsIso (f ≫ biprod.snd) := by
  let T := Triangle.mk f d δ
  let s := biprod.braiding A B
  let T' := Triangle.mk (f ≫ s.hom) (s.inv ≫ d) δ
  have hs : T ≅ T' := Triangle.isoMk T T' (Iso.refl _) s (Iso.refl _) (by simp [T, T'])
    (by simp [T, T']) (by simp [T, T'])
  have hT' : T' ∈ distTriang C := isomorphic_distinguished T hT T' hs.symm
  have hd' : s.inv ≫ d = biprod.desc (-b) (-(-a)) := by
    rw [hd]
    ext <;> simp [s, biprod.braiding]
  have hneg : IsIso (-a) := by
    let e := asIso a
    refine ⟨⟨-e.inv, ?_, ?_⟩⟩ <;> simp [e]
  have hfront := isIso_triangle_front_of_biprod_desc T'.mor₁ T'.mor₂ T'.mor₃ hT' (-b) (-a) hneg
    (by simpa [T'] using hd')
  simpa [T', s, biprod.braiding] using (hfront : IsIso ((f ≫ s.hom) ≫ biprod.fst))

/-- On the other open of the cover, the map `Rj_{V*}B ⟶ Rj_{W*}(B|_W)` becomes invertible. -/
private lemma restrictedPushforwardRestrictionMap_isIso {X U V W : RingedSpace.{u, u}}
    (jU : U ⟶ X) (jV : V ⟶ X) (iU : W ⟶ U) (iV : W ⟶ V)
    [SheafedSpace.IsOpenImmersion jU] [SheafedSpace.IsOpenImmersion jV]
    [SheafedSpace.IsOpenImmersion iV] (h : IsPullback iU iV jU jV) (B : DerivedModules V) :
    IsIso ((derivedRestrict jU).map (pushforwardRestrictionMap jV iV B)) := by
  let RV := derivedPush jV
  let η := (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction iV).unit.app B
  let α := pushforwardRestrictIso jV iV jU iU h.flip
  have : IsIso (α.hom.app B) := NatIso.isIso_app_of_isIso α.hom B
  have : IsIso (α.hom.app ((derivedPush iV).obj ((derivedRestrict iV).obj B))) :=
    NatIso.isIso_app_of_isIso α.hom _
  have hη : IsIso ((derivedRestrict iV).map η) := by
    let adj := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction iV
    have : IsIso adj.counit := adj.isIso_counit_of_iso (derivedPushRestrictSelfIso iV)
    have : IsIso (adj.counit.app ((derivedRestrict iV).obj B)) :=
      NatIso.isIso_app_of_isIso adj.counit _
    have htriangle : (derivedRestrict iV).map η ≫
        adj.counit.app ((derivedRestrict iV).obj B) = 𝟙 _ := adj.left_triangle_components B
    have : IsIso ((derivedRestrict iV).map η ≫ adj.counit.app ((derivedRestrict iV).obj B)) := by
      rw [htriangle]
      infer_instance
    exact IsIso.of_isIso_comp_right ((derivedRestrict iV).map η)
      (adj.counit.app ((derivedRestrict iV).obj B))
  have hη' : IsIso ((derivedRestrict iV ⋙ derivedPush iU).map η) := by
    change IsIso ((derivedPush iU).map ((derivedRestrict iV).map η))
    infer_instance
  have hnat := α.hom.naturality η
  have hnat' : ((RV ⋙ derivedRestrict jU).map η) ≫
      α.hom.app ((derivedPush iV).obj ((derivedRestrict iV).obj B)) =
      α.hom.app B ≫ ((derivedRestrict iV ⋙ derivedPush iU).map η) := by
    simpa [RV] using hnat
  have hsource : IsIso ((RV ⋙ derivedRestrict jU).map η) := by
    have hcomp : IsIso (α.hom.app B ≫ ((derivedRestrict iV ⋙ derivedPush iU).map η)) := by
      infer_instance
    rw [← hnat'] at hcomp
    exact IsIso.of_isIso_comp_right ((RV ⋙ derivedRestrict jU).map η)
      (α.hom.app ((derivedPush iV).obj ((derivedRestrict iV).obj B)))
  change IsIso ((derivedRestrict jU).map (RV.map η ≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso iV jV).hom.app
      ((derivedRestrict iV).obj B)))
  rw [Functor.map_comp]
  have hsource' : IsIso ((derivedRestrict jU).map (RV.map η)) := hsource
  infer_instance

/-! ### The glued object -/

private lemma pushEqIso_counit {X W : RingedSpace.{u, u}} {f g : W ⟶ X} (h : f = g)
    (M : DerivedModules W) :
    (derivedRestrict g).map ((pushEqIso h).hom.app M) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction g).counit.app M =
      (restrictEqIso h).inv.app ((derivedPush f).obj M) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f).counit.app M := by
  cases h
  simp [pushEqIso, restrictEqIso]

/-- The component on `U` of the difference map: restrict `Rj_{U*}A` to the intersection and
compare with `Rj_{W*}(B|_W)` through `c`. -/
def glueingFirstComponent {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X)
    (iU : W ⟶ U) (iV : W ⟶ V) (h : iU ≫ jU = iV ≫ jV) {A : DerivedModules U}
    {B : DerivedModules V} (c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B) :
    (derivedPush jU).obj A ⟶ (derivedPush (iV ≫ jV)).obj ((derivedRestrict iV).obj B) :=
  pushforwardRestrictionMap jU iU A ≫ (pushEqIso h).hom.app ((derivedRestrict iU).obj A) ≫
    (derivedPush (iV ≫ jV)).map c.hom

/-- The difference map whose fibre is the glued object. -/
def glueingDifference {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X) (iU : W ⟶ U)
    (iV : W ⟶ V) (h : iU ≫ jU = iV ≫ jV) {A : DerivedModules U} {B : DerivedModules V}
    (c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B) :
    (derivedPush jU).obj A ⊞ (derivedPush jV).obj B ⟶
      (derivedPush (iV ≫ jV)).obj ((derivedRestrict iV).obj B) :=
  biprod.desc (glueingFirstComponent jU jV iU iV h c) (-(pushforwardRestrictionMap jV iV B))

/-- The counit of `L(i_V j_V)^* ⊣ R(i_V j_V)_*` undoes the comparison `Rj_{U*}A ⟶ Rj_{W*}(A|_W)`
after restriction to the intersection. -/
private lemma bridgeFirst {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X)
    (iU : W ⟶ U) (iV : W ⟶ V) (h : iU ≫ jU = iV ≫ jV) (A : DerivedModules U) :
    (derivedRestrict (iV ≫ jV)).map (pushforwardRestrictionMap jU iU A) ≫
        (derivedRestrict (iV ≫ jV)).map
          ((pushEqIso h).hom.app ((derivedRestrict iU).obj A)) ≫
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
            (iV ≫ jV)).counit.app ((derivedRestrict iU).obj A) =
      (restrictEqIso h).inv.app ((derivedPush jU).obj A) ≫
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iU jU).inv.app
            ((derivedPush jU).obj A) ≫
          (derivedRestrict iU).map
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
              jU).counit.app A) := by
  have hU0' : (derivedRestrict (iU ≫ jU)).map (pushforwardRestrictionMap jU iU A) ≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
        (iU ≫ jU)).counit.app ((derivedRestrict iU).obj A) =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iU jU).inv.app
          ((derivedPush jU).obj A) ≫
        (derivedRestrict iU).map
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
            jU).counit.app A) :=
    eq_inv_comp_of_hom_comp_eq
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iU jU).app
        ((derivedPush jU).obj A)) _ _ (pushforwardRestrictionMap_counit jU iU A)
  exact natIsoMapCounitBridge (derivedRestrict (iU ≫ jU)) (derivedRestrict (iV ≫ jV))
    (restrictEqIso h) (pushforwardRestrictionMap jU iU A)
    ((pushEqIso h).hom.app ((derivedRestrict iU).obj A)) _ _ _
    (pushEqIso_counit h ((derivedRestrict iU).obj A))
    ((restrictEqIso h).inv.naturality (pushforwardRestrictionMap jU iU A)) hU0'

/-- The same for the second open, where no transport along `h` intervenes. -/
private lemma bridgeSecond {X V W : RingedSpace.{u, u}} (jV : V ⟶ X) (iV : W ⟶ V)
    (B : DerivedModules V) :
    (derivedRestrict (iV ≫ jV)).map (pushforwardRestrictionMap jV iV B) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
          (iV ≫ jV)).counit.app ((derivedRestrict iV).obj B) =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iV jV).inv.app
          ((derivedPush jV).obj B) ≫
        (derivedRestrict iV).map
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
            jV).counit.app B) :=
  eq_inv_comp_of_hom_comp_eq
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iV jV).app
      ((derivedPush jV).obj B)) _ _ (pushforwardRestrictionMap_counit jV iV B)

/-- The first term of the transposed cone identity *is* the transpose, across the adjunction on
the intersection, of the composite with the first component of the difference map. -/
private lemma transposeFirst {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X)
    (iU : W ⟶ U) (iV : W ⟶ V) (h : iU ≫ jU = iV ≫ jV) {A : DerivedModules U}
    {B : DerivedModules V} (c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B)
    (F : DerivedModules X) (u : F ⟶ (derivedPush jU).obj A) :
    (derivedRestrict (iV ≫ jV)).map u ≫ (restrictEqIso h).inv.app ((derivedPush jU).obj A) ≫
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iU jU).inv.app
            ((derivedPush jU).obj A) ≫
          (derivedRestrict iU).map
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
              jU).counit.app A) ≫ c.hom =
      (derivedRestrict (iV ≫ jV)).map (u ≫ glueingFirstComponent jU jV iU iV h c) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
          (iV ≫ jV)).counit.app ((derivedRestrict iV).obj B) := by
  have hnatc : (derivedRestrict (iV ≫ jV)).map ((derivedPush (iV ≫ jV)).map c.hom) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
          (iV ≫ jV)).counit.app ((derivedRestrict iV).obj B) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
        (iV ≫ jV)).counit.app ((derivedRestrict iU).obj A) ≫ c.hom :=
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
      (iV ≫ jV)).counit.naturality c.hom
  calc
    _ = (derivedRestrict (iV ≫ jV)).map u ≫
          (derivedRestrict (iV ≫ jV)).map (pushforwardRestrictionMap jU iU A) ≫
            (derivedRestrict (iV ≫ jV)).map
              ((pushEqIso h).hom.app ((derivedRestrict iU).obj A)) ≫
                (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
                  (iV ≫ jV)).counit.app ((derivedRestrict iU).obj A) ≫ c.hom := by
          have hh := congrArg (fun q => (derivedRestrict (iV ≫ jV)).map u ≫ q ≫ c.hom)
            (bridgeFirst jU jV iU iV h A)
          simpa only [Category.assoc] using hh.symm
    _ = _ := by
          rw [← hnatc]
          simp only [glueingFirstComponent, Functor.map_comp, Category.assoc]

/-- The second term of the transposed cone identity is the transpose of the composite with the
second component of the difference map. -/
private lemma transposeSecond {X V W : RingedSpace.{u, u}} (jV : V ⟶ X) (iV : W ⟶ V)
    {B : DerivedModules V} (F : DerivedModules X) (v : F ⟶ (derivedPush jV).obj B) :
    (derivedRestrict (iV ≫ jV)).map v ≫
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iV jV).inv.app
            ((derivedPush jV).obj B) ≫
          (derivedRestrict iV).map
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
              jV).counit.app B) =
      (derivedRestrict (iV ≫ jV)).map (v ≫ pushforwardRestrictionMap jV iV B) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
          (iV ≫ jV)).counit.app ((derivedRestrict iV).obj B) := by
  rw [Functor.map_comp, Category.assoc, bridgeSecond jV iV B]

/-- Two maps into a derived direct image are equal as soon as their transposes are. -/
private lemma transpose_inj {X W : RingedSpace.{u, u}} (k : W ⟶ X) (F : DerivedModules X)
    (M : DerivedModules W) {p q : F ⟶ (derivedPush k).obj M}
    (hpq : (derivedRestrict k).map p ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction k).counit.app M =
      (derivedRestrict k).map q ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction k).counit.app M) :
    p = q := by
  apply ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction k).homEquiv F
    M).symm.injective
  rwa [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]

/-- The cone identity, transposed across the two adjunctions. -/
private lemma coneTransposed {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X)
    (iU : W ⟶ U) (iV : W ⟶ V) (h : iU ≫ jU = iV ≫ jV) {A : DerivedModules U}
    {B : DerivedModules V} (c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B)
    (F : DerivedModules X) (u : F ⟶ (derivedPush jU).obj A) (v : F ⟶ (derivedPush jV).obj B)
    (hcone : u ≫ glueingFirstComponent jU jV iU iV h c = v ≫ pushforwardRestrictionMap jV iV B) :
    (derivedRestrict (iV ≫ jV)).map u ≫ (restrictEqIso h).inv.app ((derivedPush jU).obj A) ≫
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iU jU).inv.app
            ((derivedPush jU).obj A) ≫
          (derivedRestrict iU).map
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
              jU).counit.app A) ≫ c.hom =
      (derivedRestrict (iV ≫ jV)).map v ≫
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iV jV).inv.app
            ((derivedPush jV).obj B) ≫
          (derivedRestrict iV).map
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
              jV).counit.app B) := by
  rw [transposeFirst jU jV iU iV h c F u, transposeSecond jV iV F v, hcone]

/-- Two natural transformations in succession, transported across a map of the source. -/
private lemma natTransport {C D : Type*} [Category C] [Category D] {G F₁ F₂ : C ⥤ D}
    (β : G ⟶ F₁) (α : F₁ ⟶ F₂) {X Y : C} (u : X ⟶ Y) {Z Z' : D} (k : F₂.obj Y ⟶ Z)
    (m : Z ⟶ Z') :
    β.app X ≫ α.app X ≫ (F₂.map u ≫ k) ≫ m = G.map u ≫ β.app Y ≫ α.app Y ≫ k ≫ m := by
  simp only [Category.assoc, ← α.naturality_assoc, ← β.naturality_assoc]

/-- A natural transformation transported across a map of the source. -/
private lemma natTransportSimple {C D : Type*} [Category C] [Category D] {G F : C ⥤ D}
    (β : G ⟶ F) {X Y : C} (v : X ⟶ Y) {Z : D} (k : F.obj Y ⟶ Z) :
    G.map v ≫ β.app Y ≫ k = β.app X ≫ F.map v ≫ k := by
  rw [← Category.assoc, β.naturality v, Category.assoc]

/-- **The forward half of `Stacks.Cohomology.GlueingComplexes.overlap_eq_iff_mid`.**  Split off
into its own declaration: `maxHeartbeats` is per declaration, and the two halves together no
longer fit in one budget. -/
private lemma overlap_eq_of_mid {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X)
    (iU : W ⟶ U) (iV : W ⟶ V) [SheafedSpace.IsOpenImmersion jU]
    [SheafedSpace.IsOpenImmersion jV] (h : iU ≫ jU = iV ≫ jV) {A : DerivedModules U}
    {B : DerivedModules V} (c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B)
    (F : DerivedModules X) (u : F ⟶ (derivedPush jU).obj A) (v : F ⟶ (derivedPush jV).obj B)
    (hmid : (restrictEqIso h).inv.app F ≫
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iU jU).inv.app F ≫
          ((derivedRestrict iU).map ((derivedRestrict jU).map u) ≫
            (derivedRestrict iU).map
              ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
                jU).counit.app A)) ≫ c.hom =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iV jV).inv.app F ≫
        ((derivedRestrict iV).map ((derivedRestrict jV).map v) ≫
          (derivedRestrict iV).map
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
              jV).counit.app B))) :
    (derivedRestrict iU).map ((derivedRestrict jU).map u ≫
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
            jU).counit.app A) ≫ c.hom =
      (overlapIso jU jV iU iV h).hom.app F ≫
        (derivedRestrict iV).map ((derivedRestrict jV).map v ≫
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
            jV).counit.app B) := by
  refine eq_natIso_hom_comp (overlapIso jU jV iU iV h) F _ _ ?_
  rw [congrArg (fun α => α.app F) (overlapIso_inv jU jV iU iV h), Functor.map_comp,
    Functor.map_comp]
  simp only [NatTrans.comp_app]
  have hh := congrArg (fun q =>
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iV jV).hom.app F ≫ q)
    hmid
  simpa only [Category.assoc,
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iV
      jV).hom_inv_id_app_assoc] using hh

/-- **The backward half of `Stacks.Cohomology.GlueingComplexes.overlap_eq_iff_mid`.**  Split off
into its own declaration for the same reason as the forward half; the chase itself is
`Stacks.Cohomology.GlueingComplexes.transportBack`, applied with every object and morphism
inferred from this goal rather than re-elaborated here. -/
private lemma mid_of_overlap_eq {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X)
    (iU : W ⟶ U) (iV : W ⟶ V) [SheafedSpace.IsOpenImmersion jU]
    [SheafedSpace.IsOpenImmersion jV] (h : iU ≫ jU = iV ≫ jV) {A : DerivedModules U}
    {B : DerivedModules V} (c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B)
    (F : DerivedModules X) (u : F ⟶ (derivedPush jU).obj A) (v : F ⟶ (derivedPush jV).obj B)
    (hoverlap : (derivedRestrict iU).map ((derivedRestrict jU).map u ≫
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
            jU).counit.app A) ≫ c.hom =
      (overlapIso jU jV iU iV h).hom.app F ≫
        (derivedRestrict iV).map ((derivedRestrict jV).map v ≫
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
            jV).counit.app B)) :
    (restrictEqIso h).inv.app F ≫
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iU jU).inv.app F ≫
          ((derivedRestrict iU).map ((derivedRestrict jU).map u) ≫
            (derivedRestrict iU).map
              ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
                jU).counit.app A)) ≫ c.hom =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iV jV).inv.app F ≫
        ((derivedRestrict iV).map ((derivedRestrict jV).map v) ≫
          (derivedRestrict iV).map
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
              jV).counit.app B)) := by
  have hpre : (overlapIso jU jV iU iV h).inv.app F ≫
      ((derivedRestrict iU).map ((derivedRestrict jU).map u ≫
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
            jU).counit.app A) ≫ c.hom) =
      (derivedRestrict iV).map ((derivedRestrict jV).map v ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
          jV).counit.app B) := by
    rw [hoverlap, Iso.inv_hom_id_app_assoc]
  rw [overlapIso_inv_app jU jV iU iV h F] at hpre
  refine transportBack ?_
    ((derivedRestrict iU).map_comp ((derivedRestrict jU).map u)
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction jU).counit.app A))
    ((derivedRestrict iV).map_comp ((derivedRestrict jV).map v)
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction jV).counit.app B))
    hpre
  exact Iso.inv_hom_id_app _ F

/-- The compatibility condition on the intersection, read through the two comparison
isomorphisms of the iterated restrictions: the form in which the transposed cone identity
presents it. -/
private lemma overlap_eq_iff_mid {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X)
    (iU : W ⟶ U) (iV : W ⟶ V) [SheafedSpace.IsOpenImmersion jU]
    [SheafedSpace.IsOpenImmersion jV] (h : iU ≫ jU = iV ≫ jV) {A : DerivedModules U}
    {B : DerivedModules V} (c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B)
    (F : DerivedModules X) (u : F ⟶ (derivedPush jU).obj A) (v : F ⟶ (derivedPush jV).obj B) :
    ((restrictEqIso h).inv.app F ≫
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iU jU).inv.app F ≫
          ((derivedRestrict iU).map ((derivedRestrict jU).map u) ≫
            (derivedRestrict iU).map
              ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
                jU).counit.app A)) ≫ c.hom =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iV jV).inv.app F ≫
        ((derivedRestrict iV).map ((derivedRestrict jV).map v) ≫
          (derivedRestrict iV).map
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
              jV).counit.app B))) ↔
    ((derivedRestrict iU).map ((derivedRestrict jU).map u ≫
          (derivedPushRestrictSelfIso jU).hom.app A) ≫ c.hom =
      (overlapIso jU jV iU iV h).hom.app F ≫
        (derivedRestrict iV).map ((derivedRestrict jV).map v ≫
          (derivedPushRestrictSelfIso jV).hom.app B)) := by
  rw [derivedPushRestrictSelfIso_hom_app jU A, derivedPushRestrictSelfIso_hom_app jV B]
  exact ⟨overlap_eq_of_mid jU jV iU iV h c F u v, mid_of_overlap_eq jU jV iU iV h c F u v⟩

/-- A pair of maps out of an object of `D(𝒪_X)` annihilated by the difference map transposes to
the compatibility condition on the intersection. -/
private lemma overlap_eq_of_cone {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X)
    (iU : W ⟶ U) (iV : W ⟶ V) [SheafedSpace.IsOpenImmersion jU]
    [SheafedSpace.IsOpenImmersion jV] (h : iU ≫ jU = iV ≫ jV) {A : DerivedModules U}
    {B : DerivedModules V} (c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B)
    (F : DerivedModules X) (u : F ⟶ (derivedPush jU).obj A) (v : F ⟶ (derivedPush jV).obj B)
    (hcone : u ≫ glueingFirstComponent jU jV iU iV h c = v ≫ pushforwardRestrictionMap jV iV B) :
    (derivedRestrict iU).map ((derivedRestrict jU).map u ≫
          (derivedPushRestrictSelfIso jU).hom.app A) ≫ c.hom =
      (overlapIso jU jV iU iV h).hom.app F ≫
        (derivedRestrict iV).map ((derivedRestrict jV).map v ≫
          (derivedPushRestrictSelfIso jV).hom.app B) :=
  (overlap_eq_iff_mid jU jV iU iV h c F u v).1
    ((natTransport (restrictEqIso h).inv
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iU jU).inv u
        ((derivedRestrict iU).map
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
            jU).counit.app A)) c.hom).trans
      ((coneTransposed jU jV iU iV h c F u v hcone).trans
        (natTransportSimple
          (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iV jV).inv v
          ((derivedRestrict iV).map
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
              jV).counit.app B)))))

/-- Conversely: a pair of maps whose restrictions to the intersection agree through `c` is
annihilated by the difference map. This is the converse of `overlap_eq_of_cone`, and it is what
makes a compatible pair of maps into a cone over the difference map. -/
private lemma cone_of_overlap_eq {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X)
    (iU : W ⟶ U) (iV : W ⟶ V) [SheafedSpace.IsOpenImmersion jU]
    [SheafedSpace.IsOpenImmersion jV] (h : iU ≫ jU = iV ≫ jV) {A : DerivedModules U}
    {B : DerivedModules V} (c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B)
    (F : DerivedModules X) (u : F ⟶ (derivedPush jU).obj A) (v : F ⟶ (derivedPush jV).obj B)
    (hoverlap : (derivedRestrict iU).map ((derivedRestrict jU).map u ≫
          (derivedPushRestrictSelfIso jU).hom.app A) ≫ c.hom =
      (overlapIso jU jV iU iV h).hom.app F ≫
        (derivedRestrict iV).map ((derivedRestrict jV).map v ≫
          (derivedPushRestrictSelfIso jV).hom.app B)) :
    u ≫ glueingFirstComponent jU jV iU iV h c = v ≫ pushforwardRestrictionMap jV iV B := by
  apply transpose_inj (iV ≫ jV) F ((derivedRestrict iV).obj B)
  rw [← transposeFirst jU jV iU iV h c F u, ← transposeSecond jV iV F v]
  exact (natTransport (restrictEqIso h).inv
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iU jU).inv u
      ((derivedRestrict iU).map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
          jU).counit.app A)) c.hom).symm.trans
    (((overlap_eq_iff_mid jU jV iU iV h c F u v).2 hoverlap).trans
      (natTransportSimple
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iV jV).inv v
        ((derivedRestrict iV).map
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
            jV).counit.app B))).symm)

/-- The glued object as the fibre of the difference map: a distinguished triangle whose first
vertex `F` maps to the biproduct of the two derived direct images so that the two restrictions
of the two components are invertible. This is the construction behind the existence of a
glueing, and it is what the second half of [Stacks, Tag 08DG] reuses. -/
private theorem exists_glueingFibre {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X)
    (iU : W ⟶ U) (iV : W ⟶ V) [SheafedSpace.IsOpenImmersion jU]
    [SheafedSpace.IsOpenImmersion jV] (h : IsPullback iU iV jU jV) (A : DerivedModules U)
    (B : DerivedModules V)
    (c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B) :
    ∃ (F : DerivedModules X) (f₀ : F ⟶ (derivedPush jU).obj A ⊞ (derivedPush jV).obj B)
      (δ : (derivedPush (iV ≫ jV)).obj ((derivedRestrict iV).obj B) ⟶ F⟦(1 : ℤ)⟧),
      Triangle.mk f₀ (glueingDifference jU jV iU iV h.w c) δ ∈ distTriang (DerivedModules X) ∧
        IsIso ((derivedRestrict jU).map (f₀ ≫ biprod.fst)) ∧
        IsIso ((derivedRestrict jV).map (f₀ ≫ biprod.snd)) := by
  let : SheafedSpace.IsOpenImmersion iU := by
    rw [← h.isoPullback_hom_fst]
    infer_instance
  let : SheafedSpace.IsOpenImmersion iV := by
    rw [← h.isoPullback_hom_snd]
    infer_instance
  let aU := glueingFirstComponent jU jV iU iV h.w c
  let aV := pushforwardRestrictionMap jV iV B
  let d := glueingDifference jU jV iU iV h.w c
  obtain ⟨F, f₀, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle₁ d
  let T := Triangle.mk f₀ d δ
  have hT' : T ∈ distTriang (DerivedModules X) := by simpa [T] using hT
  let LU := derivedRestrict jU
  let LV := derivedRestrict jV
  let : LU.IsTriangulated :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated jU
  let : LV.IsTriangulated :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated jV
  let : LU.Additive := Functor.additive_of_preserves_binary_products LU
  let : LV.Additive := Functor.additive_of_preserves_binary_products LV
  let : PreservesBinaryBiproduct ((derivedPush jU).obj A) ((derivedPush jV).obj B) LU :=
    preservesBinaryBiproduct_of_preservesBiproduct LU _ _
  let : PreservesBinaryBiproduct ((derivedPush jU).obj A) ((derivedPush jV).obj B) LV :=
    preservesBinaryBiproduct_of_preservesBiproduct LV _ _
  let mU := LU.mapBiprod ((derivedPush jU).obj A) ((derivedPush jV).obj B)
  let mV := LV.mapBiprod ((derivedPush jU).obj A) ((derivedPush jV).obj B)
  let TU := LU.mapTriangle.obj T
  let TV := LV.mapTriangle.obj T
  let TU' := Triangle.mk (TU.mor₁ ≫ mU.hom) (mU.inv ≫ TU.mor₂) TU.mor₃
  let TV' := Triangle.mk (TV.mor₁ ≫ mV.hom) (mV.inv ≫ TV.mor₂) TV.mor₃
  have hTU' : TU' ∈ distTriang (DerivedModules U) :=
    isomorphic_distinguished TU (LU.map_distinguished T hT') TU' <|
      Triangle.isoMk TU' TU (Iso.refl _) mU.symm (Iso.refl _)
        (by dsimp [TU']; exact isoCancelRight TU.mor₁ mU)
        (by dsimp [TU']; exact Category.comp_id _)
        (by unfold TU'; simp)
  have hTV' : TV' ∈ distTriang (DerivedModules V) :=
    isomorphic_distinguished TV (LV.map_distinguished T hT') TV' <|
      Triangle.isoMk TV' TV (Iso.refl _) mV.symm (Iso.refl _)
        (by dsimp [TV']; exact isoCancelRight TV.mor₁ mV)
        (by dsimp [TV']; exact Category.comp_id _)
        (by unfold TV'; simp)
  have hdU : mU.inv ≫ TU.mor₂ = biprod.desc (LU.map aU) (-(LU.map aV)) := by
    change mU.inv ≫ LU.map d = _
    simpa [mU, d, glueingDifference, aU, aV] using
      biprod.mapBiprod_inv_map_desc (F := LU) ((derivedPush jU).obj A)
        ((derivedPush jV).obj B) aU (-aV)
  have hdV : mV.inv ≫ TV.mor₂ = biprod.desc (LV.map aU) (-(LV.map aV)) := by
    change mV.inv ≫ LV.map d = _
    simpa [mV, d, glueingDifference, aU, aV] using
      biprod.mapBiprod_inv_map_desc (F := LV) ((derivedPush jU).obj A)
        ((derivedPush jV).obj B) aU (-aV)
  have hIsoAV : IsIso (LU.map aV) :=
    restrictedPushforwardRestrictionMap_isIso jU jV iU iV h B
  have hIsoAU : IsIso (LV.map aU) := by
    have hbase := restrictedPushforwardRestrictionMap_isIso jV jU iV iU h.flip A
    dsimp only [aU, glueingFirstComponent]
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  have hpU : IsIso ((LU.map f₀ ≫ mU.hom) ≫ biprod.fst) :=
    isIso_triangle_front_of_biprod_desc TU'.mor₁ TU'.mor₂ TU'.mor₃ hTU' (LU.map aU)
      (LU.map aV) hIsoAV hdU
  have hpV : IsIso ((LV.map f₀ ≫ mV.hom) ≫ biprod.snd) :=
    isIso_triangle_snd_of_biprod_desc TV'.mor₁ TV'.mor₂ TV'.mor₃ hTV' (LV.map aU)
      (LV.map aV) hIsoAU hdV
  let u : F ⟶ (derivedPush jU).obj A := f₀ ≫ biprod.fst
  let v : F ⟶ (derivedPush jV).obj B := f₀ ≫ biprod.snd
  have hfst : mU.hom ≫ biprod.fst = LU.map biprod.fst := mapBiprodFst LU
  have hsnd : mV.hom ≫ biprod.snd = LV.map biprod.snd := mapBiprodSnd LV
  have hfhom : (LU.map f₀ ≫ mU.hom) ≫ biprod.fst = LU.map u := by
    simp only [u, Category.assoc, hfst, ← Functor.map_comp]
  have hghom : (LV.map f₀ ≫ mV.hom) ≫ biprod.snd = LV.map v := by
    simp only [v, Category.assoc, hsnd, ← Functor.map_comp]
  rw [hfhom] at hpU
  rw [hghom] at hpV
  exact ⟨F, f₀, δ, hT', hpU, hpV⟩

/-- **Stacks Project, Tag 08DG.** Let `X` be a ringed space, let `jU : U ⟶ X` and `jV : V ⟶ X`
be open immersions and let `W` be their intersection. An object `A` of `D(𝒪_U)`, an object `B`
of `D(𝒪_V)` and an isomorphism `c : A|_W ≅ B|_W` come from an object of `D(𝒪_X)`.

No hypothesis that `U` and `V` cover `X` is needed for the glued object to exist; a cover is
what makes it unique. -/
@[stacks 08DG "existence of a glueing"]
theorem exists_glueing {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X) (iU : W ⟶ U)
    (iV : W ⟶ V) [SheafedSpace.IsOpenImmersion jU] [SheafedSpace.IsOpenImmersion jV]
    (h : IsPullback iU iV jU jV) (A : DerivedModules U) (B : DerivedModules V)
    (c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B) :
    Nonempty (Glueing jU jV iU iV h.w A B c) := by
  obtain ⟨F, f₀, δ, hT, hpU, hpV⟩ := exists_glueingFibre jU jV iU iV h A B c
  have hzero : f₀ ≫ glueingDifference jU jV iU iV h.w c = 0 :=
    Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT
  have hcone : (f₀ ≫ biprod.fst) ≫ glueingFirstComponent jU jV iU iV h.w c =
      (f₀ ≫ biprod.snd) ≫ pushforwardRestrictionMap jV iV B :=
    biprodDescNegZero f₀ _ _ hzero
  exact ⟨⟨F, asIso ((derivedRestrict jU).map (f₀ ≫ biprod.fst)) ≪≫
      (derivedPushRestrictSelfIso jU).app A,
    asIso ((derivedRestrict jV).map (f₀ ≫ biprod.snd)) ≪≫
      (derivedPushRestrictSelfIso jV).app B,
    overlap_eq_of_cone jU jV iU iV h.w c F _ _ hcone⟩⟩

/-! ### Restriction to a cover by two opens is conservative -/

section Conservativity

open TopologicalSpace Stacks.Cohomology.RelativeMayerVietoris

/-- A functor preserving zero morphisms carries a zero object to a zero object. -/
private lemma isZero_obj {C D : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [Category D] [Preadditive D] [HasZeroObject D] (F : C ⥤ D) (hF : F.Additive) {A : C}
    (h : IsZero A) : IsZero (F.obj A) :=
  let := hF
  (isZero_zero D).of_iso (F.mapIso h.isoZero ≪≫ F.mapZeroObject)

/-- A biproduct of two zero objects is zero. -/
private lemma isZero_biprod {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasBinaryBiproducts C] {A B : C} (hA : IsZero A) (hB : IsZero B) : IsZero (A ⊞ B) := by
  rw [IsZero.iff_id_eq_zero]
  exact Limits.biprod.hom_ext _ _ (hA.eq_of_tgt _ _) (hB.eq_of_tgt _ _)

/-- The identity functor of `D(𝒪_X)` compares with the degreewise direct image along `𝟙 X`. -/
private def pushforwardIdDerivedIso (X : RingedSpace.{u, u}) :
    DerivedCategory.Qh ⋙ 𝟭 (DerivedModules X) ≅
      homotopyToDerived (modulePushforward (𝟙 X)) :=
  Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      (mapHomotopyCategoryIdIso (modulePushforward (𝟙 X))
        (RingedSpaceModuleAdjunction.modulePushforwardId X)).symm
      DerivedCategory.Qh

/-- The comparison exhibiting the identity functor as a right derived functor of the degreewise
direct image along `𝟙 X`. -/
private def pushforwardIdComparison (X : RingedSpace.{u, u}) :
    homotopyToDerived (modulePushforward (𝟙 X)) ⟶
      DerivedCategory.Qh ⋙ 𝟭 (DerivedModules X) :=
  (pushforwardIdDerivedIso X).inv

/-- The identity functor is a right derived functor of the degreewise direct image along
`𝟙 X`: the latter already inverts the quasi-isomorphisms. -/
private instance identity_isRightDerivedFunctor (X : RingedSpace.{u, u}) :
    (𝟭 (DerivedModules X)).IsRightDerivedFunctor (pushforwardIdComparison X)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (𝟭 (DerivedModules X)) (pushforwardIdDerivedIso X)

/-! ### The restricted direct images along the identity -/

/-- The inclusion of an open subspace is an open immersion. -/
private instance openSubspaceInclusion_isOpenImmersion (X : RingedSpace.{u, u})
    (O : Opens X) : SheafedSpace.IsOpenImmersion (openSubspaceInclusion X O) :=
  SheafedSpace.IsOpenImmersion.ofRestrict X O.isOpenEmbedding

/-- Restriction to an open subspace followed by the derived direct image back to `X`. This is
the vertex of the relative Mayer--Vietoris triangle of `𝟙 X` attached to an open subset. -/
private abbrev restrictedPush (X : RingedSpace.{u, u}) (O : Opens X) :
    DerivedModules X ⥤ DerivedModules X :=
  derivedRestrict (openSubspaceInclusion X O) ⋙
    derivedPush (openSubspaceInclusion X O ≫ 𝟙 X)

/-- The comparison from the degreewise restricted direct image to `restrictedPush`: the
composition isomorphism on homotopy categories, the unit of the derived direct image, and the
identification of the derived pullback along an open immersion with the degreewise one. -/
private def restrictedPushComparison (X : RingedSpace.{u, u}) (O : Opens X) :
    homotopyToDerived (restrictedPushforward (𝟙 X) O) ⟶
      DerivedCategory.Qh ⋙ restrictedPush X O :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (modulePullback (openSubspaceInclusion X O) ⋙
        modulePushforward (openSubspaceInclusion X O ≫ 𝟙 X)))
      (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    (Functor.associator
      ((modulePullback (openSubspaceInclusion X O)).mapHomotopyCategory (ComplexShape.up ℤ))
      ((modulePushforward (openSubspaceInclusion X O ≫ 𝟙 X)).mapHomotopyCategory
        (ComplexShape.up ℤ)) DerivedCategory.Qh).hom ≫
    Functor.whiskerLeft
      ((modulePullback (openSubspaceInclusion X O)).mapHomotopyCategory (ComplexShape.up ℤ))
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit
        (openSubspaceInclusion X O ≫ 𝟙 X)) ≫
    (Functor.associator
      ((modulePullback (openSubspaceInclusion X O)).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh (derivedPush (openSubspaceInclusion X O ≫ 𝟙 X))).inv ≫
    Functor.whiskerRight (openImmersionDerivedPullbackUnitIso (openSubspaceInclusion X O)).hom
      (derivedPush (openSubspaceInclusion X O ≫ 𝟙 X)) ≫
    (Functor.associator DerivedCategory.Qh (derivedRestrict (openSubspaceInclusion X O))
      (derivedPush (openSubspaceInclusion X O ≫ 𝟙 X))).hom

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- `restrictedPush` is a right derived functor of the degreewise restricted direct image: on a
K-injective complex each of the three factors of `restrictedPushComparison` is invertible,
pullback along an open immersion preserving K-injectivity. -/
private instance restrictedPush_isRightDerivedFunctor (X : RingedSpace.{u, u}) (O : Opens X) :
    (restrictedPush X O).IsRightDerivedFunctor (restrictedPushComparison X O)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) := by
  apply Stacks.Cohomology.isRightDerivedFunctor_of_isIso_on_kInjectives
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective X)
  intro I hI
  let k := openSubspaceInclusion X O
  let := hI
  let hKi := Stacks.Cohomology.openImmersionModulePullback_preservesKInjective k I
  let hunit : IsIso ((derivedPushforwardUnit (k ≫ 𝟙 X)).app
      (((modulePullback k).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)).obj I))) :=
    isIso_derivedPushforwardUnit_app_of_isKInjective (k ≫ 𝟙 X)
      (((modulePullback k).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) hKi
  dsimp only [restrictedPushComparison]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

/-! ### Vanishing of the restrictions -/

/-- The universal property of an open immersion, at the level of ringed spaces: a morphism whose
topological image is contained in that of an open immersion factors through it. -/
private def openImmersionLift {X U W : RingedSpace.{u, u}} (j : U ⟶ X) (k : W ⟶ X)
    [hj : SheafedSpace.IsOpenImmersion j]
    (hr : Set.range k.hom.base ⊆ Set.range j.hom.base) : W ⟶ U :=
  SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimage
    (PresheafedSpace.IsOpenImmersion.lift (hf := hj) j.hom k.hom hr)

/-- The factorisation produced by `openImmersionLift`. -/
private lemma openImmersionLift_fac {X U W : RingedSpace.{u, u}} (j : U ⟶ X) (k : W ⟶ X)
    [hj : SheafedSpace.IsOpenImmersion j]
    (hr : Set.range k.hom.base ⊆ Set.range j.hom.base) :
    openImmersionLift j k hr ≫ j = k :=
  InducedCategory.hom_ext
    (PresheafedSpace.IsOpenImmersion.lift_fac (hf := hj) j.hom k.hom hr)

/-- The restriction of `K` along a morphism whose image sits inside the image of an open
immersion `j` is a further restriction of `K|_U`, so it vanishes with the latter. -/
private lemma isZero_derivedRestrict_of_range_subset {X U W : RingedSpace.{u, u}} (j : U ⟶ X)
    (k : W ⟶ X) [SheafedSpace.IsOpenImmersion j]
    (hr : Set.range k.hom.base ⊆ Set.range j.hom.base) (K : DerivedModules X)
    (hj : IsZero ((derivedRestrict j).obj K)) : IsZero ((derivedRestrict k).obj K) := by
  let t := openImmersionLift j k hr
  let e : (derivedRestrict k).obj K ≅ (derivedRestrict t).obj ((derivedRestrict j).obj K) :=
    (restrictEqIso (openImmersionLift_fac j k hr)).symm.app K ≪≫
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical t j).symm.app K
  exact (isZero_obj (derivedRestrict t)
    (Functor.additive_of_preserves_binary_products _) hj).of_iso e

/-- The range of the inclusion of an open subspace is that open subset. -/
private lemma range_openSubspaceInclusion (X : RingedSpace.{u, u}) (O : Opens X) :
    Set.range (openSubspaceInclusion X O).hom.base = (O : Set X) := by
  ext x
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

/-- Each vertex of the relative Mayer--Vietoris triangle of `𝟙 X` attached to an open subset of
the image of `j` vanishes on an object whose restriction along `j` vanishes. -/
private lemma isZero_restrictedPush {X U : RingedSpace.{u, u}} (j : U ⟶ X)
    [SheafedSpace.IsOpenImmersion j] (O : Opens X)
    (hO : (O : Set X) ⊆ Set.range j.hom.base) (K : DerivedModules X)
    (hj : IsZero ((derivedRestrict j).obj K)) : IsZero ((restrictedPush X O).obj K) := by
  let k := openSubspaceInclusion X O
  have hr : Set.range k.hom.base ⊆ Set.range j.hom.base := by
    rwa [range_openSubspaceInclusion]
  let : (derivedPush (k ≫ 𝟙 X)).IsRightAdjoint :=
    { exists_leftAdjoint := ⟨_,
        ⟨Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction (k ≫ 𝟙 X)⟩⟩ }
  let : PreservesLimitsOfShape (Discrete WalkingPair) (derivedPush (k ≫ 𝟙 X)) :=
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
      (k ≫ 𝟙 X)).rightAdjoint_preservesLimits.preservesLimitsOfShape
  exact isZero_obj (derivedPush (k ≫ 𝟙 X))
    (Functor.additive_of_preserves_binary_products _)
    (isZero_derivedRestrict_of_range_subset j k hr K hj)

/-! ### Conservativity -/

/-- Restriction to the two members of a cover of a ringed space by the images of two open
immersions detects vanishing in the unbounded derived category of modules. -/
theorem isZero_of_restrict_isZero {X U V : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X)
    [SheafedSpace.IsOpenImmersion jU] [SheafedSpace.IsOpenImmersion jV]
    (cover : Set.range jU.hom.base ∪ Set.range jV.hom.base = Set.univ)
    (K : DerivedModules X)
    (hU : IsZero ((derivedRestrict jU).obj K)) (hV : IsZero ((derivedRestrict jV).obj K)) :
    IsZero K := by
  have hUV : immImage jU ⊔ immImage jV = ⊤ := by
    ext x
    change x ∈ Set.range jU.hom.base ∪ Set.range jV.hom.base ↔ x ∈ Set.univ
    simpa using congrArg (fun s : Set X.carrier => x ∈ s) cover
  obtain ⟨rU, rV, dU, dV, δ, hTri⟩ :=
    unboundedRelativeMayerVietoris (𝟙 X) (immImage jU) (immImage jV) hUV
      (𝟭 (DerivedModules X)) (restrictedPush X (immImage jU)) (restrictedPush X (immImage jV))
      (restrictedPush X (immImage jU ⊓ immImage jV)) (pushforwardIdComparison X)
      (restrictedPushComparison X (immImage jU)) (restrictedPushComparison X (immImage jV))
      (restrictedPushComparison X (immImage jU ⊓ immImage jV))
  have hsubW : ((immImage jU ⊓ immImage jV : Opens X) : Set X) ⊆
      Set.range jU.hom.base :=
    fun _ hx => hx.1
  have h₂ : IsZero ((restrictedPush X (immImage jU)).obj K ⊞
      (restrictedPush X (immImage jV)).obj K) :=
    isZero_biprod (isZero_restrictedPush jU _ (fun _ hx => hx) K hU)
      (isZero_restrictedPush jV _ (fun _ hx => hx) K hV)
  have h₃ : IsZero ((restrictedPush X (immImage jU ⊓ immImage jV)).obj K) :=
    isZero_restrictedPush jU _ hsubW K hU
  exact Triangle.isZero₁_of_isZero₂₃ _ (hTri K) h₂ h₃

/-- Restriction to the two members of a cover of a ringed space by the images of two open
immersions detects invertibility in the unbounded derived category of modules. -/
theorem isIso_of_restrict_isIso {X U V : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X)
    [SheafedSpace.IsOpenImmersion jU] [SheafedSpace.IsOpenImmersion jV]
    (cover : Set.range jU.hom.base ∪ Set.range jV.hom.base = Set.univ)
    {K L : DerivedModules X} (φ : K ⟶ L)
    (hU : IsIso ((derivedRestrict jU).map φ)) (hV : IsIso ((derivedRestrict jV).map φ)) :
    IsIso φ := by
  obtain ⟨C, g, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle φ
  let T := Triangle.mk φ g δ
  have hT' : T ∈ distTriang (DerivedModules X) := hT
  let : (derivedRestrict jU).IsTriangulated :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated jU
  let : (derivedRestrict jV).IsTriangulated :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated jV
  have hCU : IsZero ((derivedRestrict jU).obj C) :=
    Triangle.isZero₃_of_isIso₁ ((derivedRestrict jU).mapTriangle.obj T)
      ((derivedRestrict jU).map_distinguished T hT') hU
  have hCV : IsZero ((derivedRestrict jV).obj C) :=
    Triangle.isZero₃_of_isIso₁ ((derivedRestrict jV).mapTriangle.obj T)
      ((derivedRestrict jV).map_distinguished T hT') hV
  exact (Triangle.isZero₃_iff_isIso₁ T hT').1
    (isZero_of_restrict_isZero jU jV cover C hCU hCV)

end Conservativity

/-! ### Maps out of the glued object -/

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- A cone over the difference map factors through the fibre of that difference map. -/
private theorem exists_factorisation_of_cone {X U V W : RingedSpace.{u, u}}
    {jU : U ⟶ X} {jV : V ⟶ X} {iU : W ⟶ U} {iV : W ⟶ V}
    {h : iU ≫ jU = iV ≫ jV} {A : DerivedModules U} {B : DerivedModules V}
    {c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B} {FE K : DerivedModules X}
    {f₀ : FE ⟶ (derivedPush jU).obj A ⊞ (derivedPush jV).obj B}
    {δ : (derivedPush (iV ≫ jV)).obj ((derivedRestrict iV).obj B) ⟶ FE⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₀ (glueingDifference jU jV iU iV h c) δ ∈ distTriang (DerivedModules X))
    (u : K ⟶ (derivedPush jU).obj A) (v : K ⟶ (derivedPush jV).obj B)
    (hcone : u ≫ glueingFirstComponent jU jV iU iV h c =
      v ≫ pushforwardRestrictionMap jV iV B) :
    ∃ χ : K ⟶ FE, χ ≫ f₀ ≫ biprod.fst = u ∧ χ ≫ f₀ ≫ biprod.snd = v := by
  obtain ⟨χ, hχ⟩ := Pretriangulated.Triangle.coyoneda_exact₂ _ hT (biprod.lift u v)
    (biprodLiftDescNegZero u v (glueingFirstComponent jU jV iU iV h c)
      (pushforwardRestrictionMap jV iV B) hcone)
  exact ⟨χ, (comp_biprodLift_components χ f₀ u v hχ).1,
    (comp_biprodLift_components χ f₀ u v hχ).2⟩

/-- If `Lj^* p` is invertible, a factorisation `ι ≫ p` of the unit of `Lj^* ⊣ Rj_*` restricts to
a retraction of `Lj^* ι`, so `Lj^* ι` is invertible too. -/
private lemma restrict_factorisation_unit {X U : RingedSpace.{u, u}} (j : U ⟶ X)
    [SheafedSpace.IsOpenImmersion j] {E FE : DerivedModules X} (ι : E ⟶ FE)
    (p : FE ⟶ (derivedPush j).obj ((derivedRestrict j).obj E))
    [IsIso ((derivedRestrict j).map p)] (hp : ι ≫ p =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction j).unit.app E) :
    (derivedRestrict j).map ι ≫ (derivedRestrict j).map p ≫
        (derivedPushRestrictSelfIso j).hom.app ((derivedRestrict j).obj E) = 𝟙 _ ∧
      IsIso ((derivedRestrict j).map ι) := by
  have hι : (derivedRestrict j).map ι ≫ (derivedRestrict j).map p ≫
      (derivedPushRestrictSelfIso j).hom.app ((derivedRestrict j).obj E) = 𝟙 _ := by
    rw [derivedPushRestrictSelfIso_hom_app j ((derivedRestrict j).obj E), ← Category.assoc,
      ← Functor.map_comp, hp]
    exact (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
      j).left_triangle_components E
  refine ⟨hι, ?_⟩
  have : IsIso ((derivedPushRestrictSelfIso j).hom.app ((derivedRestrict j).obj E)) :=
    NatIso.isIso_app_of_isIso (derivedPushRestrictSelfIso j).hom _
  have : IsIso ((derivedRestrict j).map ι ≫ (derivedRestrict j).map p ≫
      (derivedPushRestrictSelfIso j).hom.app ((derivedRestrict j).obj E)) := by
    rw [hι]
    infer_instance
  exact IsIso.of_isIso_comp_right ((derivedRestrict j).map ι)
    ((derivedRestrict j).map p ≫
      (derivedPushRestrictSelfIso j).hom.app ((derivedRestrict j).obj E))

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- Every object of `D(𝒪_X)` is the glueing of its own two restrictions: the two units of the
adjunctions form a cone over the difference map of that glueing datum, so they factor through
its fibre, and the factorisation is inverse to the two identifications of clause (i). -/
private theorem exists_selfGlueingFactorisation {X U V W : RingedSpace.{u, u}}
    (jU : U ⟶ X) (jV : V ⟶ X) (iU : W ⟶ U) (iV : W ⟶ V)
    [SheafedSpace.IsOpenImmersion jU] [SheafedSpace.IsOpenImmersion jV]
    (h : IsPullback iU iV jU jV) (E : DerivedModules X) :
    ∃ (FE : DerivedModules X)
      (f₀ : FE ⟶ (derivedPush jU).obj ((derivedRestrict jU).obj E) ⊞
        (derivedPush jV).obj ((derivedRestrict jV).obj E))
      (δ : (derivedPush (iV ≫ jV)).obj
          ((derivedRestrict iV).obj ((derivedRestrict jV).obj E)) ⟶ FE⟦(1 : ℤ)⟧)
      (ι : E ⟶ FE),
      Triangle.mk f₀ (glueingDifference jU jV iU iV h.w ((overlapIso jU jV iU iV h.w).app E)) δ
          ∈ distTriang (DerivedModules X) ∧
        (derivedRestrict jU).map ι ≫ (derivedRestrict jU).map (f₀ ≫ biprod.fst) ≫
          (derivedPushRestrictSelfIso jU).hom.app ((derivedRestrict jU).obj E) = 𝟙 _ ∧
        (derivedRestrict jV).map ι ≫ (derivedRestrict jV).map (f₀ ≫ biprod.snd) ≫
          (derivedPushRestrictSelfIso jV).hom.app ((derivedRestrict jV).obj E) = 𝟙 _ ∧
        IsIso ((derivedRestrict jU).map ι) ∧ IsIso ((derivedRestrict jV).map ι) ∧
        ι ≫ f₀ ≫ biprod.fst = (derivedAdjunction jU).unit.app E ∧
        ι ≫ f₀ ≫ biprod.snd = (derivedAdjunction jV).unit.app E := by
  obtain ⟨FE, f₀, δ, hT, hpU, hpV⟩ := exists_glueingFibre jU jV iU iV h
    ((derivedRestrict jU).obj E) ((derivedRestrict jV).obj E)
    ((overlapIso jU jV iU iV h.w).app E)
  obtain ⟨ι, hιfst, hιsnd⟩ := exists_factorisation_of_cone hT
    ((derivedAdjunction jU).unit.app E) ((derivedAdjunction jV).unit.app E)
    (cone_of_overlap_eq jU jV iU iV h.w ((overlapIso jU jV iU iV h.w).app E) E _ _ (by
      rw [derivedPushRestrictSelfIso_hom_app jU ((derivedRestrict jU).obj E),
        derivedPushRestrictSelfIso_hom_app jV ((derivedRestrict jV).obj E),
        (derivedAdjunction jU).left_triangle_components E,
        (derivedAdjunction jV).left_triangle_components E]
      simp))
  obtain ⟨hιU, hisoU⟩ := restrict_factorisation_unit jU ι (f₀ ≫ biprod.fst) hιfst
  obtain ⟨hιV, hisoV⟩ := restrict_factorisation_unit jV ι (f₀ ≫ biprod.snd) hιsnd
  exact ⟨FE, f₀, δ, ι, hT, hιU, hιV, hisoU, hisoV, hιfst, hιsnd⟩

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- The second half of [Stacks, Tag 08DG], with the only consequence of the covering hypothesis
isolated as the assumption `hcons`: restriction to the two opens detects isomorphisms.

`E` is the glueing of its own two restrictions, by `exists_selfGlueingFactorisation`, and a
compatible pair `(a, b)` transposes to a cone over the difference map of that glueing datum,
hence factors through its fibre; composing with the inverse of `E ≅ F_E` is the required
map. -/
private theorem exists_hom_of_compatible_of_conservative {X U V W : RingedSpace.{u, u}}
    (jU : U ⟶ X) (jV : V ⟶ X) (iU : W ⟶ U) (iV : W ⟶ V)
    [SheafedSpace.IsOpenImmersion jU] [SheafedSpace.IsOpenImmersion jV]
    (h : IsPullback iU iV jU jV)
    (hcons : ∀ {K L : DerivedModules X} (ψ : K ⟶ L), IsIso ((derivedRestrict jU).map ψ) →
      IsIso ((derivedRestrict jV).map ψ) → IsIso ψ)
    {A : DerivedModules U} {B : DerivedModules V}
    {c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B}
    (G : Glueing jU jV iU iV h.w A B c) (E : DerivedModules X)
    (a : A ⟶ (derivedRestrict jU).obj E) (b : B ⟶ (derivedRestrict jV).obj E)
    (hab : (derivedRestrict iU).map a ≫ (overlapIso jU jV iU iV h.w).hom.app E =
      c.hom ≫ (derivedRestrict iV).map b) :
    ∃ φ : G.F ⟶ E, (derivedRestrict jU).map φ = G.f.hom ≫ a ∧
      (derivedRestrict jV).map φ = G.g.hom ≫ b := by
  obtain ⟨FE, f₀, δ, ι, hT, hιU, hιV, hisoU, hisoV, -, -⟩ :=
    exists_selfGlueingFactorisation jU jV iU iV h E
  let : IsIso ι := hcons ι hisoU hisoV
  have hu : (derivedRestrict jU).map
        ((derivedAdjunction jU).homEquiv G.F ((derivedRestrict jU).obj E) (G.f.hom ≫ a)) ≫
      (derivedAdjunction jU).counit.app ((derivedRestrict jU).obj E) = G.f.hom ≫ a :=
    ((derivedAdjunction jU).homEquiv G.F ((derivedRestrict jU).obj E)).symm_apply_apply _
  have hv : (derivedRestrict jV).map
        ((derivedAdjunction jV).homEquiv G.F ((derivedRestrict jV).obj E) (G.g.hom ≫ b)) ≫
      (derivedAdjunction jV).counit.app ((derivedRestrict jV).obj E) = G.g.hom ≫ b :=
    ((derivedAdjunction jV).homEquiv G.F ((derivedRestrict jV).obj E)).symm_apply_apply _
  have hcompat : (derivedRestrict iU).map G.f.hom ≫ c.hom =
      (overlapIso jU jV iU iV h.w).hom.app G.F ≫ (derivedRestrict iV).map G.g.hom :=
    G.compatible
  obtain ⟨χ, hχU, hχV⟩ := exists_factorisation_of_cone hT
    ((derivedAdjunction jU).homEquiv G.F ((derivedRestrict jU).obj E) (G.f.hom ≫ a))
    ((derivedAdjunction jV).homEquiv G.F ((derivedRestrict jV).obj E) (G.g.hom ≫ b))
    (cone_of_overlap_eq jU jV iU iV h.w ((overlapIso jU jV iU iV h.w).app E) G.F _ _ (by
      rw [derivedPushRestrictSelfIso_hom_app jU ((derivedRestrict jU).obj E),
        derivedPushRestrictSelfIso_hom_app jV ((derivedRestrict jV).obj E), hu, hv,
        Functor.map_comp, Functor.map_comp, Category.assoc,
        show ((overlapIso jU jV iU iV h.w).app E).hom =
          (overlapIso jU jV iU iV h.w).hom.app E from rfl, hab, ← Category.assoc, hcompat,
        Category.assoc]))
  refine ⟨χ ≫ inv ι, ?_, ?_⟩
  · rw [Functor.map_comp, Functor.map_inv, IsIso.inv_eq_of_hom_inv_id hιU, ← Category.assoc,
      ← Functor.map_comp, hχU]
    exact hu
  · rw [Functor.map_comp, Functor.map_inv, IsIso.inv_eq_of_hom_inv_id hιV, ← Category.assoc,
      ← Functor.map_comp, hχV]
    exact hv

/-- **Stacks Project, Tag 08DG.** Let `X` be a ringed space covered by the images of two open
immersions `jU : U ⟶ X` and `jV : V ⟶ X`, let `W` be their intersection, and let `F` be a
glueing of the glueing data `(A, B, c)`, with identifications `f : F|_U ≅ A` and
`g : F|_V ≅ B`. Let `E` be an object of `D(𝒪_X)` and let `a : A ⟶ E|_U` and `b : B ⟶ E|_V`
agree on `W` through `c`. Then there is a morphism `F ⟶ E` restricting to `a ∘ f` on `U` and
to `b ∘ g` on `V`.

Unlike the existence of the glued object, this needs `U` and `V` to cover `X`: it is
Mayer--Vietoris for `Hom`, and the covering hypothesis enters only through
`isIso_of_restrict_isIso`. -/
@[stacks 08DG "a compatible pair of maps comes from the glued object"]
theorem exists_hom_of_compatible {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X)
    (iU : W ⟶ U) (iV : W ⟶ V) [SheafedSpace.IsOpenImmersion jU]
    [SheafedSpace.IsOpenImmersion jV] (h : IsPullback iU iV jU jV)
    (cover : Set.range jU.hom.base ∪ Set.range jV.hom.base = Set.univ)
    {A : DerivedModules U} {B : DerivedModules V}
    {c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B}
    (G : Glueing jU jV iU iV h.w A B c) (E : DerivedModules X)
    (a : A ⟶ (derivedRestrict jU).obj E) (b : B ⟶ (derivedRestrict jV).obj E)
    (hab : (derivedRestrict iU).map a ≫ (overlapIso jU jV iU iV h.w).hom.app E =
      c.hom ≫ (derivedRestrict iV).map b) :
    ∃ φ : G.F ⟶ E, (derivedRestrict jU).map φ = G.f.hom ≫ a ∧
      (derivedRestrict jV).map φ = G.g.hom ≫ b :=
  exists_hom_of_compatible_of_conservative jU jV iU iV h
    (fun ψ hψU hψV => isIso_of_restrict_isIso jU jV cover ψ hψU hψV) G E a b hab

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- A map killed by restriction along `j` is killed by any factorisation of the unit of
`Lj^* ⊣ Rj_*` at its target. -/
private lemma comp_factorisation_unit_eq_zero {X U : RingedSpace.{u, u}} (j : U ⟶ X)
    {K E FE : DerivedModules X} (φ : K ⟶ E) (ι : E ⟶ FE)
    (p : FE ⟶ (derivedPush j).obj ((derivedRestrict j).obj E))
    (hp : ι ≫ p = (derivedAdjunction j).unit.app E) (hφ : (derivedRestrict j).map φ = 0) :
    φ ≫ ι ≫ p = 0 := by
  have := (derivedAdjunction j).isRightAdjoint
  rw [hp, ← (derivedAdjunction j).unit_naturality, hφ, Functor.map_zero, comp_zero]

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- **Stacks Project, Tag 08DG, uniqueness of the map out of a glueing.** Let `X` be covered by
the images of two open immersions `jU`, `jV` with intersection `W`, and let `φ : K ⟶ E` restrict to
zero on `U` and on `V`. If every map from the restriction of `K⟦1⟧` to `W` to the restriction of
`E` to `W` vanishes — the vanishing of `Ext^{-1}(K|_W, E|_W)` — then `φ = 0`. This is the
injectivity half of Mayer--Vietoris for `Hom`. -/
theorem eq_zero_of_restrict_eq_zero {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X)
    (iU : W ⟶ U) (iV : W ⟶ V) [SheafedSpace.IsOpenImmersion jU]
    [SheafedSpace.IsOpenImmersion jV] (h : IsPullback iU iV jU jV)
    (cover : Set.range jU.hom.base ∪ Set.range jV.hom.base = Set.univ)
    {K E : DerivedModules X} (φ : K ⟶ E) (hU : (derivedRestrict jU).map φ = 0)
    (hV : (derivedRestrict jV).map φ = 0)
    (hW : ∀ g : (derivedRestrict (iV ≫ jV)).obj (K⟦(1 : ℤ)⟧) ⟶
      (derivedRestrict iV).obj ((derivedRestrict jV).obj E), g = 0) :
    φ = 0 := by
  obtain ⟨FE, f₀, δ, ι, hT, -, -, hisoU, hisoV, hfst, hsnd⟩ :=
    exists_selfGlueingFactorisation jU jV iU iV h E
  have := (derivedAdjunction (iV ≫ jV)).isRightAdjoint
  let : IsIso ι := isIso_of_restrict_isIso jU jV cover ι hisoU hisoV
  have h0 : (φ ≫ ι) ≫ f₀ = 0 := by
    apply biprod.hom_ext
    · rw [zero_comp, Category.assoc, Category.assoc]
      exact comp_factorisation_unit_eq_zero jU φ ι _ hfst hU
    · rw [zero_comp, Category.assoc, Category.assoc]
      exact comp_factorisation_unit_eq_zero jV φ ι _ hsnd hV
  obtain ⟨g, hg⟩ := Pretriangulated.Triangle.coyoneda_exact₁ _ hT ((φ ≫ ι)⟦(1 : ℤ)⟧')
    (by
      change (φ ≫ ι)⟦(1 : ℤ)⟧' ≫ f₀⟦(1 : ℤ)⟧' = 0
      rw [← Functor.map_comp, h0, Functor.map_zero])
  have hg0 : g = 0 := by
    rw [← ((derivedAdjunction (iV ≫ jV)).homEquiv _ _).apply_symm_apply g,
      hW (((derivedAdjunction (iV ≫ jV)).homEquiv _ _).symm g),
      Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  have hψ : (φ ≫ ι)⟦(1 : ℤ)⟧' = 0 := by
    rw [hg]
    change g ≫ δ = 0
    rw [hg0, zero_comp]
  have hψ' : φ ≫ ι = 0 :=
    (shiftFunctor (DerivedModules X) (1 : ℤ)).map_injective (by rw [hψ, Functor.map_zero])
  rw [← Category.comp_id φ, ← IsIso.hom_inv_id ι, ← Category.assoc, hψ', zero_comp]

end Stacks.Cohomology.GlueingComplexes

end
