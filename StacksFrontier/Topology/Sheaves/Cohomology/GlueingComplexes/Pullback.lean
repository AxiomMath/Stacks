module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom
public import StacksFrontier.Topology.Sheaves.Cohomology.GlueingComplexes.TwoOpens

/-!
# Pulling a glued object back along a morphism of covers

Let `X` be a ringed space with opens `U`, `V` and intersection `W`, and let `X'` be a ringed
space covered by opens `U'`, `V'` with intersection `W'`, with a morphism `p : X' ⟶ X` restricting
to `pU : U' ⟶ U`, `pV : V' ⟶ V` and `pW : W' ⟶ W`. Let `F` be an object of `D(𝒪_X)` glued from
`A ∈ D(𝒪_U)` and `B ∈ D(𝒪_V)` along `c : A|_W ≅ B|_W`. If an object `E` of `D(𝒪_{X'})` has
restrictions to `U'` and `V'` identified with `Lp_U^*A` and `Lp_V^*B`, compatibly on `W'` with
the derived pullback of `c`, then `Lp^*F ≅ E`, through an isomorphism restricting on `U'` and on
`V'` to the given identifications.

## Main definitions

* `Stacks.Cohomology.GlueingComplexes.derivedRestrictSquareIso`: the comparison
  `Lg^* ⋙ Lf^* ≅ Lg'^* ⋙ Lf'^*` attached to a commutative square `f ≫ g = f' ≫ g'`.
* `Stacks.Cohomology.GlueingComplexes.glueingPullback`: the glueing on `X'` of the two
  restrictions of `E`, carried by `Lp^*F`.

## Main results

* `Stacks.Cohomology.GlueingComplexes.overlapIso_eq_derivedRestrictSquareIso`: the canonical
  comparison on an intersection is the square comparison of its square.
* `Stacks.Cohomology.GlueingComplexes.cube_coherence`: the coherence of the square comparisons
  around a cube of morphisms of ringed spaces.
* `Stacks.Cohomology.GlueingComplexes.exists_iso_derivedRestrict_glueing`: `Lp^*F ≅ E`.

## References

* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Lemma 36.35.9 (Tag 0DI8)](https://stacks.math.columbia.edu/tag/0DI8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.DerivedPullback (factorIso factorIso_assoc)

namespace Stacks.Cohomology.GlueingComplexes

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Square comparisons -/

section Square

variable {A B B' C : RingedSpace.{u, u}}

/-- The comparison `Lg^* ⋙ Lf^* ≅ Lg'^* ⋙ Lf'^*` attached to a commutative square
`f ≫ g = f' ≫ g'` of morphisms of ringed spaces. -/
def derivedRestrictSquareIso (f : A ⟶ B) (g : B ⟶ C) (f' : A ⟶ B') (g' : B' ⟶ C)
    (w : f ≫ g = f' ≫ g') :
    derivedRestrict g ⋙ derivedRestrict f ≅ derivedRestrict g' ⋙ derivedRestrict f' :=
  factorIso f g (f ≫ g) rfl ≪≫ (factorIso f' g' (f ≫ g) w.symm).symm

/-- The comparison of a factorisation along a morphism equal to the composite is the composition
isomorphism of Tag 0D5S followed by the transport along that equality. -/
theorem factorIso_eq_trans_eqToIso (f : A ⟶ B) (g : B ⟶ C) {k : A ⟶ C} (h : f ≫ g = k) :
    factorIso f g k h = Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g ≪≫
      eqToIso (congrArg (fun m : A ⟶ C => derivedRestrict m) h) := by
  subst h
  rw [eqToIso_refl, Iso.trans_refl]
  rfl

end Square

/-- **The canonical comparison on an intersection is the square comparison of its square.** -/
theorem overlapIso_eq_derivedRestrictSquareIso {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X)
    (jV : V ⟶ X) (iU : W ⟶ U) (iV : W ⟶ V) (h : iU ≫ jU = iV ≫ jV) :
    overlapIso jU jV iU iV h = derivedRestrictSquareIso iU jU iV jV h := by
  unfold overlapIso derivedRestrictSquareIso
  rw [factorIso_eq_trans_eqToIso iV jV h.symm]
  rfl

/-! ### Paths of three morphisms -/

section Path

variable {P Q R T : RingedSpace.{u, u}}

/-- The comparison of `La^* Lb^* Lc^*` with `Lκ^*` for `κ = a ≫ b ≫ c`, composing `b` and `c`
first. -/
def pathIsoInner (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ T) (m : Q ⟶ T) (hm : b ≫ c = m)
    (κ : P ⟶ T) (hκ : a ≫ m = κ) (M : DerivedModules T) :
    (derivedRestrict a).obj ((derivedRestrict b).obj ((derivedRestrict c).obj M)) ≅
      (derivedRestrict κ).obj M :=
  (derivedRestrict a).mapIso ((factorIso b c m hm).app M) ≪≫ (factorIso a m κ hκ).app M

/-- The comparison of `La^* Lb^* Lc^*` with `Lκ^*` for `κ = a ≫ b ≫ c`, composing `a` and `b`
first. -/
def pathIsoOuter (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ T) (q : P ⟶ R) (hq : a ≫ b = q)
    (κ : P ⟶ T) (hκ : q ≫ c = κ) (M : DerivedModules T) :
    (derivedRestrict a).obj ((derivedRestrict b).obj ((derivedRestrict c).obj M)) ≅
      (derivedRestrict κ).obj M :=
  (factorIso a b q hq).app ((derivedRestrict c).obj M) ≪≫ (factorIso q c κ hκ).app M

/-- The two bracketings of a path of three morphisms give the same comparison: the associativity
of Tag 0D5S. -/
theorem pathIsoInner_eq_pathIsoOuter (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ T) (m : Q ⟶ T)
    (hm : b ≫ c = m) (q : P ⟶ R) (hq : a ≫ b = q) (κ : P ⟶ T) (hκ : a ≫ m = κ)
    (hκ' : q ≫ c = κ) (M : DerivedModules T) :
    pathIsoInner a b c m hm κ hκ M = pathIsoOuter a b c q hq κ hκ' M :=
  (factorIso_assoc a b c m q κ hm hq hκ' hκ M).symm

/-- A square comparison on the inner pair of a path is absorbed by the inner comparisons. -/
theorem derivedRestrict_map_squareIso_comp_pathIsoInner (a : P ⟶ Q) {R' : RingedSpace.{u, u}}
    (b : Q ⟶ R) (c : R ⟶ T) (b' : Q ⟶ R') (c' : R' ⟶ T) (w : b ≫ c = b' ≫ c')
    (m : Q ⟶ T) (hm : b ≫ c = m) (hm' : b' ≫ c' = m) (κ : P ⟶ T) (hκ : a ≫ m = κ)
    (M : DerivedModules T) :
    (derivedRestrict a).map ((derivedRestrictSquareIso b c b' c' w).hom.app M) ≫
        (pathIsoInner a b' c' m hm' κ hκ M).hom =
      (pathIsoInner a b c m hm κ hκ M).hom := by
  subst hm
  simp only [pathIsoInner, derivedRestrictSquareIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← Functor.map_comp_assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- A square comparison on the outer pair of a path is absorbed by the outer comparisons. -/
theorem squareIso_app_comp_pathIsoOuter {Q' : RingedSpace.{u, u}} (a : P ⟶ Q) (b : Q ⟶ R)
    (a' : P ⟶ Q') (b' : Q' ⟶ R) (c : R ⟶ T) (w : a ≫ b = a' ≫ b') (q : P ⟶ R)
    (hq : a ≫ b = q) (hq' : a' ≫ b' = q) (κ : P ⟶ T) (hκ : q ≫ c = κ)
    (M : DerivedModules T) :
    (derivedRestrictSquareIso a b a' b' w).hom.app ((derivedRestrict c).obj M) ≫
        (pathIsoOuter a' b' c q hq' κ hκ M).hom =
      (pathIsoOuter a b c q hq κ hκ M).hom := by
  subst hq
  simp only [pathIsoOuter, derivedRestrictSquareIso, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc]

/-- The inverse of a square comparison on the outer pair of a path, absorbed by the outer
comparisons. -/
theorem squareIso_inv_app_comp_pathIsoOuter {Q' : RingedSpace.{u, u}} (a : P ⟶ Q) (b : Q ⟶ R)
    (a' : P ⟶ Q') (b' : Q' ⟶ R) (c : R ⟶ T) (w : a ≫ b = a' ≫ b') (q : P ⟶ R)
    (hq : a ≫ b = q) (hq' : a' ≫ b' = q) (κ : P ⟶ T) (hκ : q ≫ c = κ)
    (M : DerivedModules T) :
    (derivedRestrictSquareIso a b a' b' w).inv.app ((derivedRestrict c).obj M) ≫
        (pathIsoOuter a b c q hq κ hκ M).hom =
      (pathIsoOuter a' b' c q hq' κ hκ M).hom := by
  rw [← squareIso_app_comp_pathIsoOuter a b a' b' c w q hq hq' κ hκ M,
    Iso.inv_hom_id_app_assoc]

end Path

/-! ### The cube -/

section Cube

variable {X U V W X' U' V' W' : RingedSpace.{u, u}}
  {jU : U ⟶ X} {jV : V ⟶ X} {iU : W ⟶ U} {iV : W ⟶ V}
  {jU' : U' ⟶ X'} {jV' : V' ⟶ X'} {iU' : W' ⟶ U'} {iV' : W' ⟶ V'}
  {p : X' ⟶ X} {pU : U' ⟶ U} {pV : V' ⟶ V} {pW : W' ⟶ W}

/-- **The coherence of the square comparisons around a cube.** Going from `Li_U'^* Lj_U'^* Lp^*`
to `Li_V'^* Lp_V^* Lj_V^*` through the face over `U`, the face over `W`, the bottom face and the
face over `W` again agrees with going through the top face and the face over `V`. -/
theorem cube_coherence (h : iU ≫ jU = iV ≫ jV) (h' : iU' ≫ jU' = iV' ≫ jV')
    (hU : jU' ≫ p = pU ≫ jU) (hV : jV' ≫ p = pV ≫ jV) (hWU : pW ≫ iU = iU' ≫ pU)
    (hWV : pW ≫ iV = iV' ≫ pV) (M : DerivedModules X) :
    (derivedRestrict iU').map ((derivedRestrictSquareIso jU' p pU jU hU).hom.app M) ≫
        (derivedRestrictSquareIso pW iU iU' pU hWU).inv.app ((derivedRestrict jU).obj M) ≫
        (derivedRestrict pW).map ((derivedRestrictSquareIso iU jU iV jV h).hom.app M) ≫
        (derivedRestrictSquareIso pW iV iV' pV hWV).hom.app ((derivedRestrict jV).obj M) =
      (derivedRestrictSquareIso iU' jU' iV' jV' h').hom.app ((derivedRestrict p).obj M) ≫
        (derivedRestrict iV').map ((derivedRestrictSquareIso jV' p pV jV hV).hom.app M) := by
  have hc : (iU' ≫ pU) ≫ jU = iU' ≫ jU' ≫ p := by rw [Category.assoc, hU]
  have he : pW ≫ (iU ≫ jU) = iU' ≫ jU' ≫ p := by rwa [← Category.assoc, hWU]
  have hg : (pW ≫ iV) ≫ jV = iU' ≫ jU' ≫ p := by rwa [Category.assoc, ← h]
  have hj : iV' ≫ (jV' ≫ p) = iU' ≫ jU' ≫ p := by
    rwa [hV, ← Category.assoc, ← hWV]
  have hl : (iU' ≫ jU') ≫ p = iU' ≫ jU' ≫ p := Category.assoc _ _ _
  rw [← cancel_mono (pathIsoOuter iV' pV jV (pW ≫ iV) hWV.symm _ hg M).hom]
  simp only [Category.assoc]
  rw [squareIso_app_comp_pathIsoOuter pW iV iV' pV jV hWV (pW ≫ iV) rfl hWV.symm _ hg M,
    ← pathIsoInner_eq_pathIsoOuter pW iV jV (iU ≫ jU) h.symm (pW ≫ iV) rfl _ he hg M,
    derivedRestrict_map_squareIso_comp_pathIsoInner pW iU jU iV jV h (iU ≫ jU) rfl h.symm _
      he M,
    pathIsoInner_eq_pathIsoOuter pW iU jU (iU ≫ jU) rfl (iU' ≫ pU) hWU _ he hc M,
    squareIso_inv_app_comp_pathIsoOuter pW iU iU' pU jU hWU (iU' ≫ pU) hWU rfl _ hc M,
    ← pathIsoInner_eq_pathIsoOuter iU' pU jU (jU' ≫ p) hU.symm (iU' ≫ pU) rfl _ rfl hc M,
    derivedRestrict_map_squareIso_comp_pathIsoInner iU' jU' p pU jU hU (jU' ≫ p) rfl hU.symm _
      rfl M,
    ← pathIsoInner_eq_pathIsoOuter iV' pV jV (jV' ≫ p) hV.symm (pW ≫ iV) hWV.symm _ hj hg M,
    derivedRestrict_map_squareIso_comp_pathIsoInner iV' jV' p pV jV hV (jV' ≫ p) rfl hV.symm _
      hj M,
    pathIsoInner_eq_pathIsoOuter iV' jV' p (jV' ≫ p) rfl (iU' ≫ jU') h'.symm _ hj hl M,
    squareIso_app_comp_pathIsoOuter iU' jU' iV' jV' p h' (iU' ≫ jU') rfl h'.symm _ hl M,
    pathIsoInner_eq_pathIsoOuter iU' jU' p (jU' ≫ p) rfl (iU' ≫ jU') rfl _ rfl hl M]

end Cube

/-! ### The glued object pulled back -/

section Glueing

variable {X U V W X' U' V' W' : RingedSpace.{u, u}}
  {jU : U ⟶ X} {jV : V ⟶ X} {iU : W ⟶ U} {iV : W ⟶ V}
  {jU' : U' ⟶ X'} {jV' : V' ⟶ X'} {iU' : W' ⟶ U'} {iV' : W' ⟶ V'}
  {p : X' ⟶ X} {pU : U' ⟶ U} {pV : V' ⟶ V} {pW : W' ⟶ W}
  {h : iU ≫ jU = iV ≫ jV} (h' : iU' ≫ jU' = iV' ≫ jV')
  (hU : jU' ≫ p = pU ≫ jU) (hV : jV' ≫ p = pV ≫ jV) (hWU : pW ≫ iU = iU' ≫ pU)
  (hWV : pW ≫ iV = iV' ≫ pV)
  {A : DerivedModules U} {B : DerivedModules V}
  {c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B}
  (G : Glueing jU jV iU iV h A B c) (E : DerivedModules X')
  (a : (derivedRestrict pU).obj A ≅ (derivedRestrict jU').obj E)
  (b : (derivedRestrict pV).obj B ≅ (derivedRestrict jV').obj E)

/-- The identification of the restriction to `U'` of the pullback of the glued object with the
restriction of `E`. -/
def glueingPullbackLeft : (derivedRestrict jU').obj ((derivedRestrict p).obj G.F) ≅
    (derivedRestrict jU').obj E :=
  (derivedRestrictSquareIso jU' p pU jU hU).app G.F ≪≫ (derivedRestrict pU).mapIso G.f ≪≫ a

/-- The identification of the restriction to `V'` of the pullback of the glued object with the
restriction of `E`. -/
def glueingPullbackRight : (derivedRestrict jV').obj ((derivedRestrict p).obj G.F) ≅
    (derivedRestrict jV').obj E :=
  (derivedRestrictSquareIso jV' p pV jV hV).app G.F ≪≫ (derivedRestrict pV).mapIso G.g ≪≫ b

include h' hWU hWV in
/-- **The compatibility of the two identifications on `W'`.** -/
theorem glueingPullback_compatible
    (hc : (derivedRestrictSquareIso pW iU iU' pU hWU).inv.app A ≫
        (derivedRestrict pW).map c.hom ≫ (derivedRestrictSquareIso pW iV iV' pV hWV).hom.app B =
      (derivedRestrict iU').map a.hom ≫ (overlapIso jU' jV' iU' iV' h').hom.app E ≫
        (derivedRestrict iV').map b.inv) :
    CompatibleOnOverlap jU' jV' iU' iV' h' ((overlapIso jU' jV' iU' iV' h').app E)
      ((derivedRestrict p).obj G.F) (glueingPullbackLeft hU G E a)
      (glueingPullbackRight hV G E b) := by
  have hc' : (derivedRestrict iU').map a.hom ≫ (overlapIso jU' jV' iU' iV' h').hom.app E =
      (derivedRestrictSquareIso pW iU iU' pU hWU).inv.app A ≫
        (derivedRestrict pW).map c.hom ≫
          (derivedRestrictSquareIso pW iV iV' pV hWV).hom.app B ≫
            (derivedRestrict iV').map b.hom := by
    rw [reassoc_of% hc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  have hG : (derivedRestrict iU).map G.f.hom ≫ c.hom =
      (derivedRestrictSquareIso iU jU iV jV h).hom.app G.F ≫ (derivedRestrict iV).map G.g.hom := by
    rw [← overlapIso_eq_derivedRestrictSquareIso]
    exact G.compatible
  unfold CompatibleOnOverlap
  simp only [glueingPullbackLeft, glueingPullbackRight, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [hc', reassoc_of% ((derivedRestrictSquareIso pW iU iU' pU hWU).inv.naturality G.f.hom),
    ← Functor.map_comp_assoc, hG, Functor.map_comp_assoc,
    reassoc_of% ((derivedRestrictSquareIso pW iV iV' pV hWV).hom.naturality G.g.hom),
    overlapIso_eq_derivedRestrictSquareIso, reassoc_of% (cube_coherence h h' hU hV hWU hWV G.F)]

/-- **The glueing on `X'` of the two restrictions of `E`**, carried by the derived pullback of
the glued object `F`. -/
def glueingPullback
    (hc : (derivedRestrictSquareIso pW iU iU' pU hWU).inv.app A ≫
        (derivedRestrict pW).map c.hom ≫ (derivedRestrictSquareIso pW iV iV' pV hWV).hom.app B =
      (derivedRestrict iU').map a.hom ≫ (overlapIso jU' jV' iU' iV' h').hom.app E ≫
        (derivedRestrict iV').map b.inv) :
    Glueing jU' jV' iU' iV' h' ((derivedRestrict jU').obj E) ((derivedRestrict jV').obj E)
      ((overlapIso jU' jV' iU' iV' h').app E) where
  F := (derivedRestrict p).obj G.F
  f := glueingPullbackLeft hU G E a
  g := glueingPullbackRight hV G E b
  compatible := glueingPullback_compatible h' hU hV hWU hWV G E a b hc

end Glueing

/-- **Pulling a glued object back along a morphism of covers.** Let `F` be glued on `X` from
`A` and `B` along `c`, and let `p : X' ⟶ X` restrict to `pU`, `pV`, `pW` on the members of a
cover of `X'` by two opens `U'`, `V'` with intersection `W'`. If `E ∈ D(𝒪_{X'})` has its
restrictions to `U'` and `V'` identified with `Lp_U^*A` and `Lp_V^*B` by `a` and `b`, and the
derived pullback of `c` is, through the square comparisons of the faces over `W'`, the
comparison of these identifications on `W'`, then `Lp^*F ≅ E`, by an isomorphism whose
restrictions to `U'` and `V'` are the square comparisons followed by the pullbacks of the
identifications of `F` and by `a` and `b`. -/
theorem exists_iso_derivedRestrict_glueing {X U V W X' U' V' W' : RingedSpace.{u, u}}
    {jU : U ⟶ X} {jV : V ⟶ X} {iU : W ⟶ U} {iV : W ⟶ V}
    {jU' : U' ⟶ X'} {jV' : V' ⟶ X'} {iU' : W' ⟶ U'} {iV' : W' ⟶ V'}
    [SheafedSpace.IsOpenImmersion jU'] [SheafedSpace.IsOpenImmersion jV']
    {p : X' ⟶ X} {pU : U' ⟶ U} {pV : V' ⟶ V} {pW : W' ⟶ W}
    {h : iU ≫ jU = iV ≫ jV} (h' : IsPullback iU' iV' jU' jV')
    (cover : Set.range jU'.hom.base ∪ Set.range jV'.hom.base = Set.univ)
    (hU : jU' ≫ p = pU ≫ jU) (hV : jV' ≫ p = pV ≫ jV) (hWU : pW ≫ iU = iU' ≫ pU)
    (hWV : pW ≫ iV = iV' ≫ pV)
    {A : DerivedModules U} {B : DerivedModules V}
    {c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B}
    (G : Glueing jU jV iU iV h A B c) (E : DerivedModules X')
    (a : (derivedRestrict pU).obj A ≅ (derivedRestrict jU').obj E)
    (b : (derivedRestrict pV).obj B ≅ (derivedRestrict jV').obj E)
    (hc : (derivedRestrictSquareIso pW iU iU' pU hWU).inv.app A ≫
        (derivedRestrict pW).map c.hom ≫ (derivedRestrictSquareIso pW iV iV' pV hWV).hom.app B =
      (derivedRestrict iU').map a.hom ≫ (overlapIso jU' jV' iU' iV' h'.w).hom.app E ≫
        (derivedRestrict iV').map b.inv) :
    ∃ φ : (derivedRestrict p).obj G.F ≅ E,
      (derivedRestrict jU').map φ.hom =
          (derivedRestrictSquareIso jU' p pU jU hU).hom.app G.F ≫
            (derivedRestrict pU).map G.f.hom ≫ a.hom ∧
        (derivedRestrict jV').map φ.hom =
          (derivedRestrictSquareIso jV' p pV jV hV).hom.app G.F ≫
            (derivedRestrict pV).map G.g.hom ≫ b.hom := by
  let G' := glueingPullback h'.w hU hV hWU hWV G E a b hc
  obtain ⟨φ, hφU, hφV⟩ := exists_hom_of_compatible jU' jV' iU' iV' h' cover G' E (𝟙 _) (𝟙 _)
    (by simp)
  have hφU' : (derivedRestrict jU').map φ =
      (derivedRestrictSquareIso jU' p pU jU hU).hom.app G.F ≫
        (derivedRestrict pU).map G.f.hom ≫ a.hom := by
    rw [hφU, Category.comp_id]
    simp [G', glueingPullback, glueingPullbackLeft]
  have hφV' : (derivedRestrict jV').map φ =
      (derivedRestrictSquareIso jV' p pV jV hV).hom.app G.F ≫
        (derivedRestrict pV).map G.g.hom ≫ b.hom := by
    rw [hφV, Category.comp_id]
    simp [G', glueingPullback, glueingPullbackRight]
  have hφ : IsIso φ := isIso_of_restrict_isIso jU' jV' cover φ
    (by rw [hφU']; exact (glueingPullbackLeft hU G E a).isIso_hom)
    (by rw [hφV']; exact (glueingPullbackRight hV G E b).isIso_hom)
  exact ⟨@asIso _ _ _ _ φ hφ, hφU', hφV'⟩

end Stacks.Cohomology.GlueingComplexes

end
