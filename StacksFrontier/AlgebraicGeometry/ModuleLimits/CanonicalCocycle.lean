module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalAffine
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackCanonical

/-!
# The canonical identification of iterated pullbacks, and its cocycle

For morphisms of schemes `q : W ⟶ Z` and `g : Z ⟶ X` with `q ≫ g = pi` the canonical
identification `Stacks.AlgebraicGeometry.ModuleLimits.canHom` of `q^*(g^*F)` with `pi^*F` is the
morphism through which [Stacks Project, Tag 01ZR] (2) states the base change of a descended
morphism.  This file records its *cocycle*: for a chain `L ⟶ W ⟶ Z ⟶ X` the two ways of
identifying the triply iterated pullback with the pullback along the total composite agree.

The cocycle is then used to prove that the relation "`φ` is the base change of `χ` through the
canonical identifications" — `Stacks.AlgebraicGeometry.ModuleLimits.IsCanonicalBaseChange` — is
invariant under the three moves a local-to-global argument for Tag 01ZR (2) performs: pushing
the stage further along the diagram, factoring the morphism that the modules are pulled back
along, and restricting the base to an open subscheme.  Each of the three is an *equivalence*, not
just an implication, which is what makes the gluing argument reversible.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.canConj`: a morphism of iterated pullbacks read, through
  the canonical identification, as a morphism of pullbacks along the composite.
* `Stacks.AlgebraicGeometry.ModuleLimits.rcanIso` and `...rcanConj`: the same for an open
  immersion, with `AlgebraicGeometry.Scheme.Modules.restrictFunctor` in place of the pullback.
* `Stacks.AlgebraicGeometry.ModuleLimits.IsCanonicalBaseChange`: the conclusion of
  [Stacks Project, Tag 01ZR] (2) as a relation between a morphism at a stage and a morphism at
  the base.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp_canHom`: **the cocycle.**
* `Stacks.AlgebraicGeometry.ModuleLimits.pullback_map_eq_of_isCanonicalBaseChange`: two
  morphisms at a stage with the same canonical base change have equal pullbacks to the base.
* `Stacks.AlgebraicGeometry.ModuleLimits.isCanonicalBaseChange_stage_iff`: the relation is
  unchanged when the stage is pushed one step further along the diagram.
* `Stacks.AlgebraicGeometry.ModuleLimits.isCanonicalBaseChange_stage_restrictFunctor_iff`: the
  same, with the pullback along an open immersion replaced by
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, which is the spelling a morphism glued from
  local data over an open covering comes in.
* `Stacks.AlgebraicGeometry.ModuleLimits.isCanonicalBaseChange_factor_iff`: the relation is
  unchanged when the morphism the modules are pulled back along is factored.
* `Stacks.AlgebraicGeometry.ModuleLimits.isCanonicalBaseChange_restrict_iff`: the pullback of the
  canonical equation along a morphism of the base is the canonical equation over that base.

## Implementation notes

The cocycle is `AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity` read at a single
module, with the two `pullbackCongr` factors attached to equations that are definitionally
reflexivity once the intermediate composites have been substituted.  Every equation between
composites of morphisms of schemes is carried as an explicit hypothesis rather than written out,
so that consumers never have to transport along `Scheme.Modules.pullbackCongr` by hand: a
diagram whose transition morphism is `D.map (e₁ ≫ e₂)` can be fed to these lemmas with
`D.map_comp` as the hypothesis.

The three invariance statements are each proved by exhibiting both sides of the equation in the
shape `n ≫ _ ≫ m` with `n` and `m` isomorphisms and appealing to
`Stacks.AlgebraicGeometry.ModuleLimits.eq_iff_eq_of_isIso_comp_comp`; no step of the argument
needs the morphisms involved to be isomorphisms.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-! ### Cancelling isomorphisms on both sides of an equation -/

/-- Two morphisms presented as `n ≫ u ≫ m` and `n ≫ v ≫ m` with `n` and `m` isomorphisms are
equal exactly when `u` and `v` are. -/
theorem eq_iff_eq_of_isIso_comp_comp {C : Type*} [Category C] {A A' B B' : C} (n : A ⟶ A')
    [IsIso n] (m : B' ⟶ B) [IsIso m] {u v : A' ⟶ B'} {u' v' : A ⟶ B}
    (hu : u' = n ≫ u ≫ m) (hv : v' = n ≫ v ≫ m) : u' = v' ↔ u = v := by
  rw [hu, hv]
  exact ⟨fun h => (cancel_mono m).mp ((cancel_epi n).mp h), fun h => by rw [h]⟩

/-! ### Reading a morphism of iterated pullbacks through the canonical identification -/

section Can

variable {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X) (hpi : q ≫ g = pi)

/-- A morphism of iterated pullbacks read, through the canonical identification, as a morphism of
pullbacks along the composite. -/
noncomputable def canConj {F G : X.Modules}
    (χ : (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F) ⟶
      (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj G)) :
    (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G :=
  (canIso q g pi hpi F).inv ≫ χ ≫ canHom q g pi hpi G

/-- The defining property of `canConj`, in the form in which it is used. -/
theorem canHom_comp_canConj {F G : X.Modules}
    (χ : (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F) ⟶
      (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj G)) :
    canHom q g pi hpi F ≫ canConj q g pi hpi χ = χ ≫ canHom q g pi hpi G := by
  rw [canConj, ← Category.assoc, ← canIso_hom q g pi hpi, (canIso q g pi hpi F).hom_inv_id,
    Category.id_comp]

end Can

/-! ### The cocycle -/

/-- **The cocycle for the canonical identification.**  For a chain `L ⟶ W ⟶ Z ⟶ X` the
identification of the triply iterated pullback with the pullback along the total composite does
not depend on the order in which the two intermediate objects are cancelled.  Every composite is
supplied as a hypothesis, so a diagram whose transition morphism is `D.map (e₁ ≫ e₂)` can be fed
to this lemma with `D.map_comp`. -/
theorem canHom_comp_canHom {L W Z X : Scheme.{u}} (p : L ⟶ W) (t : W ⟶ Z) (s : Z ⟶ X)
    (pw : L ⟶ Z) (h1 : p ≫ t = pw) (ts : W ⟶ X) (h3 : t ≫ s = ts)
    (pz : L ⟶ X) (h2 : pw ≫ s = pz) (h4 : p ≫ ts = pz) (F : X.Modules) :
    canHom p t pw h1 ((Scheme.Modules.pullback s).obj F) ≫ canHom pw s pz h2 F
      = (Scheme.Modules.pullback p).map (canHom t s ts h3 F) ≫ canHom p ts pz h4 F := by
  subst h1
  subst h3
  subst h2
  have key := Scheme.Modules.pseudofunctor_associativity (f := p) (g := t) (h := s)
  replace key := NatTrans.congr_app key F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_app] at key
  simp only [canHom, Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id, eqToIso.hom, eqToHom_app]
  rw [← key]
  simp

/-! ### The canonical base change relation -/

/-- **The conclusion of [Stacks Project, Tag 01ZR] (2)** as a relation: the morphism `φ` of
pullbacks along `pi` is the base change of the morphism `χ` of pullbacks along `g`, the base
change being taken along `q` through the canonical identification attached to `q ≫ g = pi`. -/
def IsCanonicalBaseChange {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X)
    (hpi : q ≫ g = pi) {F G : X.Modules}
    (χ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G)
    (φ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G) : Prop :=
  (Scheme.Modules.pullback q).map χ ≫ canHom q g pi hpi G = canHom q g pi hpi F ≫ φ

section Rel

variable {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X) (hpi : q ≫ g = pi)

/-- The canonical base change relation says that `φ` is obtained from the pullback of `χ` by
conjugating with the canonical identifications. -/
theorem isCanonicalBaseChange_iff {F G : X.Modules}
    (χ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G)
    (φ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G) :
    IsCanonicalBaseChange q g pi hpi χ φ
      ↔ canConj q g pi hpi ((Scheme.Modules.pullback q).map χ) = φ := by
  rw [IsCanonicalBaseChange, canConj, Iso.inv_comp_eq, canIso_hom]

/-- `canConj` carries a composite to the composite. -/
theorem canConj_comp {F G H : X.Modules}
    (χ : (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F) ⟶
      (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj G))
    (χ' : (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj G) ⟶
      (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj H)) :
    canConj q g pi hpi (χ ≫ χ') = canConj q g pi hpi χ ≫ canConj q g pi hpi χ' := by
  simp only [canConj, Category.assoc]
  rw [← canIso_hom q g pi hpi G, (canIso q g pi hpi G).hom_inv_id_assoc]

/-- `canConj` carries the identity to the identity. -/
@[simp]
theorem canConj_id (F : X.Modules) :
    canConj q g pi hpi (𝟙 ((Scheme.Modules.pullback q).obj
      ((Scheme.Modules.pullback g).obj F))) = 𝟙 _ := by
  rw [canConj, Category.id_comp, ← canIso_hom q g pi hpi F,
    (canIso q g pi hpi F).inv_hom_id]

/-- Two morphisms at a stage with the same canonical base change have equal pullbacks to the
base.  This is the half of faithfulness that costs nothing: the canonical identification is an
isomorphism. -/
theorem pullback_map_eq_of_isCanonicalBaseChange {F G : X.Modules}
    {χ₁ χ₂ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G}
    {φ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G}
    (h₁ : IsCanonicalBaseChange q g pi hpi χ₁ φ)
    (h₂ : IsCanonicalBaseChange q g pi hpi χ₂ φ) :
    (Scheme.Modules.pullback q).map χ₁ = (Scheme.Modules.pullback q).map χ₂ :=
  (cancel_mono (canHom q g pi hpi G)).mp (h₁.trans h₂.symm)

end Rel

/-! ### Pushing the stage one step further along the diagram -/

/-- Cancelling the canonical identification of `t^*(s^*F)` against the two-step cocycle. -/
private theorem map_canIso_inv_comp_canHom_comp_canHom {L W Z X : Scheme.{u}} (p : L ⟶ W)
    (t : W ⟶ Z) (s : Z ⟶ X) (pw : L ⟶ Z) (h1 : p ≫ t = pw) (ts : W ⟶ X) (h3 : t ≫ s = ts)
    (pz : L ⟶ X) (h2 : pw ≫ s = pz) (h4 : p ≫ ts = pz) (F : X.Modules) :
    (Scheme.Modules.pullback p).map (canIso t s ts h3 F).inv ≫
      canHom p t pw h1 ((Scheme.Modules.pullback s).obj F) ≫ canHom pw s pz h2 F
      = canHom p ts pz h4 F := by
  rw [canHom_comp_canHom p t s pw h1 ts h3 pz h2 h4 F, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← canIso_hom t s ts h3, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The canonical base change relation is unchanged when the stage is pushed further along the
diagram.**  Let `L ⟶ W ⟶ Z ⟶ X` be a chain with `p ≫ t = pw`, `t ≫ s = ts` and
`pw ≫ s = pz`.  A morphism `χ` of pullbacks along `s` has the morphism `φ` of pullbacks along
`pz` as its base change along `pw` exactly when its pullback along `t`, read as a morphism of
pullbacks along `ts`, has `φ` as its base change along `p`.

This is what lets the stage produced for one member of an affine covering be refined to a stage
that works for every member. -/
theorem isCanonicalBaseChange_stage_iff {L W Z X : Scheme.{u}} (p : L ⟶ W) (t : W ⟶ Z) (s : Z ⟶ X)
    (pw : L ⟶ Z) (h1 : p ≫ t = pw) (ts : W ⟶ X) (h3 : t ≫ s = ts)
    (pz : L ⟶ X) (h2 : pw ≫ s = pz) (h4 : p ≫ ts = pz) {F G : X.Modules}
    (χ : (Scheme.Modules.pullback s).obj F ⟶ (Scheme.Modules.pullback s).obj G)
    (φ : (Scheme.Modules.pullback pz).obj F ⟶ (Scheme.Modules.pullback pz).obj G) :
    IsCanonicalBaseChange p ts pz h4
        (canConj t s ts h3 ((Scheme.Modules.pullback t).map χ)) φ
      ↔ IsCanonicalBaseChange pw s pz h2 χ φ := by
  have hCG := canHom_comp_canHom p t s pw h1 ts h3 pz h2 h4 G
  refine eq_iff_eq_of_isIso_comp_comp
    ((Scheme.Modules.pullback p).map (canIso t s ts h3 F).inv ≫
      canHom p t pw h1 ((Scheme.Modules.pullback s).obj F)) (𝟙 _) ?_ ?_
  · simp only [Category.comp_id, canConj, CategoryTheory.Functor.map_comp, Category.assoc]
    rw [← hCG, reassoc_of% (canHom_naturality p t pw h1 χ)]
  · simp only [Category.comp_id, Category.assoc]
    rw [reassoc_of% (map_canIso_inv_comp_canHom_comp_canHom p t s pw h1 ts h3 pz h2 h4 F)]

/-! ### The stage move for an open immersion, in the restriction-functor spelling -/

section OpenImmersion

variable {L W Z X : Scheme.{u}} (p : L ⟶ W) (t : W ⟶ Z) [IsOpenImmersion t] (s : Z ⟶ X)

/-- The canonical identification `t^*(s^*F) ≅ ts^*F` with
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` in place of the pullback along the open
immersion `t`.  The restriction functor is the spelling of the pullback along an open immersion
whose action on sections is available, and it is therefore the spelling in which a morphism
assembled from local data over an open covering is produced. -/
noncomputable def rcanIso (ts : W ⟶ X) (h : t ≫ s = ts) (F : X.Modules) :
    (Scheme.Modules.restrictFunctor t).obj ((Scheme.Modules.pullback s).obj F) ≅
      (Scheme.Modules.pullback ts).obj F :=
  (Scheme.Modules.restrictFunctorIsoPullback t).app _ ≪≫ canIso t s ts h F

/-- A morphism of the restrictions to the source of an open immersion read, through `rcanIso`, as
a morphism of pullbacks along the composite. -/
noncomputable def rcanConj (ts : W ⟶ X) (h : t ≫ s = ts) {F G : X.Modules}
    (ρ : (Scheme.Modules.restrictFunctor t).obj ((Scheme.Modules.pullback s).obj F) ⟶
      (Scheme.Modules.restrictFunctor t).obj ((Scheme.Modules.pullback s).obj G)) :
    (Scheme.Modules.pullback ts).obj F ⟶ (Scheme.Modules.pullback ts).obj G :=
  (rcanIso t s ts h F).inv ≫ ρ ≫ (rcanIso t s ts h G).hom

omit [IsOpenImmersion t] in
/-- `canConj` and `rcanConj` agree on a morphism coming from the base, because
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` is natural. -/
theorem canConj_eq_rcanConj (ts : W ⟶ X) (h : t ≫ s = ts) [IsOpenImmersion t] {F G : X.Modules}
    (χ : (Scheme.Modules.pullback s).obj F ⟶ (Scheme.Modules.pullback s).obj G) :
    canConj t s ts h ((Scheme.Modules.pullback t).map χ)
      = rcanConj t s ts h ((Scheme.Modules.restrictFunctor t).map χ) := by
  have hnat := (Scheme.Modules.restrictFunctorIsoPullback t).hom.naturality χ
  simp only [rcanConj, rcanIso, canConj, Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom,
    Category.assoc, canIso_hom]
  rw [reassoc_of% hnat, Iso.inv_hom_id_app_assoc]

/-- **The stage move for an open immersion, in the restriction-functor spelling.**  This is
`isCanonicalBaseChange_stage_iff` with the pullback along the open immersion `t` replaced by
`AlgebraicGeometry.Scheme.Modules.restrictFunctor t`, so that a morphism glued from local data
over an open covering can be fed to it directly. -/
theorem isCanonicalBaseChange_stage_restrictFunctor_iff
    (pw : L ⟶ Z) (h1 : p ≫ t = pw) (ts : W ⟶ X) (h3 : t ≫ s = ts)
    (pz : L ⟶ X) (h2 : pw ≫ s = pz) (h4 : p ≫ ts = pz) {F G : X.Modules}
    (χ : (Scheme.Modules.pullback s).obj F ⟶ (Scheme.Modules.pullback s).obj G)
    (φ : (Scheme.Modules.pullback pz).obj F ⟶ (Scheme.Modules.pullback pz).obj G) :
    IsCanonicalBaseChange p ts pz h4
        (rcanConj t s ts h3 ((Scheme.Modules.restrictFunctor t).map χ)) φ
      ↔ IsCanonicalBaseChange pw s pz h2 χ φ := by
  rw [← canConj_eq_rcanConj]
  exact isCanonicalBaseChange_stage_iff p t s pw h1 ts h3 pz h2 h4 χ φ

end OpenImmersion

/-! ### Factoring the morphism the modules are pulled back along -/

/-- **The canonical base change relation is unchanged when the morphism the modules are pulled
back along is factored.**  Let `W ⟶ Z ⟶ Y ⟶ X` be a chain with `g₁ ≫ g₂ = g`, `q ≫ g₁ = pY`
and `pY ≫ g₂ = pi`.  A morphism `χ` of pullbacks along `g₁` of the pullbacks along `g₂` has
`ψ` as its base change along `q` exactly when the two, read through the canonical
identifications as morphisms of pullbacks along `g` and along `pi`, stand in the same relation.

This is what lets the affine case, applied on the diagram of preimages of an affine open of a
stage, be read as a statement about the modules on that stage. -/
theorem isCanonicalBaseChange_factor_iff {W Z Y X : Scheme.{u}} (q : W ⟶ Z) (g₁ : Z ⟶ Y)
    (g₂ : Y ⟶ X) (g : Z ⟶ X) (hg : g₁ ≫ g₂ = g) (pY : W ⟶ Y) (hpY : q ≫ g₁ = pY)
    (pi : W ⟶ X) (hpi : pY ≫ g₂ = pi) (hq : q ≫ g = pi) {F G : X.Modules}
    (χ : (Scheme.Modules.pullback g₁).obj ((Scheme.Modules.pullback g₂).obj F) ⟶
      (Scheme.Modules.pullback g₁).obj ((Scheme.Modules.pullback g₂).obj G))
    (ψ : (Scheme.Modules.pullback pY).obj ((Scheme.Modules.pullback g₂).obj F) ⟶
      (Scheme.Modules.pullback pY).obj ((Scheme.Modules.pullback g₂).obj G)) :
    IsCanonicalBaseChange q g pi hq (canConj g₁ g₂ g hg χ) (canConj pY g₂ pi hpi ψ)
      ↔ IsCanonicalBaseChange q g₁ pY hpY χ ψ := by
  have hCG := canHom_comp_canHom q g₁ g₂ pY hpY g hg pi hpi hq G
  refine eq_iff_eq_of_isIso_comp_comp
    ((Scheme.Modules.pullback q).map (canIso g₁ g₂ g hg F).inv)
    (canHom pY g₂ pi hpi G) ?_ ?_
  · simp only [canConj, CategoryTheory.Functor.map_comp, Category.assoc]
    rw [← hCG]
  · simp only [Category.assoc]
    rw [← canHom_comp_canConj pY g₂ pi hpi ψ,
      reassoc_of% (map_canIso_inv_comp_canHom_comp_canHom q g₁ g₂ pY hpY g hg pi hpi hq F)]

/-! ### Restricting the base -/

/-- **The pullback of the canonical equation along a morphism of the base is the canonical
equation over that base.**  For `j : W' ⟶ W` the two sides of the canonical equation for
`q ≫ g = pi` have equal pullbacks along `j` exactly when `χ` has the restriction of `φ` as its
base change along `q' = j ≫ q`.

Together with the locality of an equality of morphisms of sheaves of modules
(`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover`) this is what reduces the
canonical equation on the limit to the canonical equation over the members of an open
covering. -/
theorem isCanonicalBaseChange_restrict_iff {W' W Z X : Scheme.{u}} (j : W' ⟶ W) (q : W ⟶ Z)
    (g : Z ⟶ X) (pi : W ⟶ X) (hpi : q ≫ g = pi) (q' : W' ⟶ Z) (hq' : j ≫ q = q')
    (pi' : W' ⟶ X) (hpi' : j ≫ pi = pi') (hq'' : q' ≫ g = pi') {F G : X.Modules}
    (χ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G)
    (φ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G) :
    (Scheme.Modules.pullback j).map ((Scheme.Modules.pullback q).map χ ≫ canHom q g pi hpi G)
        = (Scheme.Modules.pullback j).map (canHom q g pi hpi F ≫ φ)
      ↔ IsCanonicalBaseChange q' g pi' hq'' χ
          (canConj j pi pi' hpi' ((Scheme.Modules.pullback j).map φ)) := by
  have hCF := canHom_comp_canHom j q g q' hq' pi hpi pi' hq'' hpi' F
  have hCG := canHom_comp_canHom j q g q' hq' pi hpi pi' hq'' hpi' G
  refine eq_iff_eq_of_isIso_comp_comp
    (canHom j q q' hq' ((Scheme.Modules.pullback g).obj F))
    (inv (canHom j pi pi' hpi' G)) ?_ ?_
  · simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [← reassoc_of% (canHom_naturality j q q' hq' χ), reassoc_of% hCG, IsIso.hom_inv_id,
      Category.comp_id]
  · simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [reassoc_of% hCF, reassoc_of% (canHom_comp_canConj j pi pi' hpi'
      ((Scheme.Modules.pullback j).map φ)), IsIso.hom_inv_id, Category.comp_id]

end Stacks.AlgebraicGeometry.ModuleLimits

end
