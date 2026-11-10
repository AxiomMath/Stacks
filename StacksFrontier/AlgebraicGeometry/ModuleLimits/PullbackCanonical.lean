module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalAffine

/-!
# Formal properties of the canonical identification of an iterated pullback

For a composite `q ≫ g = pi` of morphisms of schemes and a sheaf of modules `F` on the target,
`Stacks.AlgebraicGeometry.ModuleLimits.canHom` is the canonical comparison
`q^*(g^*F) ⟶ pi^*F` with which the conclusion of [Stacks Project, Tag 01ZR] (2) is stated.  This
file packages it as an isomorphism and proves the cocycle condition for a chain of three
morphisms.  The latter is the pseudofunctoriality of `F ↦ F.Modules` read at an object, and it is
what lets a statement about a module pulled back from one stage of a diagram be transported to
any later stage.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.canIso`: the canonical comparison of an iterated
  pullback with the pullback of the composite, as an isomorphism.
* `Stacks.AlgebraicGeometry.ModuleLimits.canStep`: an endomorphism-shaped morphism between
  pullbacks along `g`, carried along a further morphism `m` with `m ≫ g = mg` to a morphism
  between pullbacks along `mg`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.canHom_rfl`: for the composite written out, the
  congruence factor of `canHom` is an identity.
* `Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp`: **the cocycle condition** for a chain
  `r`, `q`, `g` of three morphisms.
* `Stacks.AlgebraicGeometry.ModuleLimits.canonical_eq_of_further_step`: an equation between a
  morphism of pullbacks along `g` and a morphism of pullbacks along `πi`, mediated by the
  canonical comparison, is inherited by the morphism obtained by pulling back one stage further.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.pullbackCongr` is literally `eqToIso`, so a composite
presented as a variable together with an equation can be eliminated by `subst`, after which the
congruence factor of `canHom` becomes an identity (`canHom_rfl`) and the cocycle condition is
exactly `AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity` read at the module.  The
remaining `eqToHom` in that reading is the associativity of composition of morphisms of schemes,
which is not a definitional equality; it is matched against the congruence factor of the
left-hand side rather than removed.

`canonical_eq_of_further_step` is then a formal consequence of the cocycle condition, the
naturality and the fact that `canIso` is an isomorphism; no geometry enters.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-! ### The canonical comparison as an isomorphism -/

section Iso

variable {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X) (hpi : q ≫ g = pi)
  (F : X.Modules)

/-- The canonical identification of an iterated pullback with the pullback of the composite, as
an isomorphism: `AlgebraicGeometry.Scheme.Modules.pullbackComp` followed by
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`, read at the module `F`. -/
noncomputable def canIso :
    (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F) ≅
      (Scheme.Modules.pullback pi).obj F :=
  (Scheme.Modules.pullbackComp q g).app F ≪≫ (Scheme.Modules.pullbackCongr hpi).app F

/-- The underlying morphism of `canIso` is `canHom`. -/
@[simp] theorem canIso_hom : (canIso q g pi hpi F).hom = canHom q g pi hpi F := rfl

/-- For the composite written out, the congruence factor of `canHom` is an identity. -/
theorem canHom_rfl : canHom q g (q ≫ g) rfl F = (Scheme.Modules.pullbackComp q g).hom.app F := by
  simp [canHom, Scheme.Modules.pullbackCongr]

end Iso

/-! ### The cocycle condition -/

/-- **The cocycle condition.** For a chain `V ⟶ W ⟶ Z ⟶ X` of three morphisms, the two ways of
comparing the thrice iterated pullback of `F` with the pullback of `F` along the total composite
agree.  This is `AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity` read at `F`.  The
hypothesis `hrt` is a consequence of `hs`, `hpi` and `ht`; it is taken as a hypothesis so that
both sides can be stated with the named composites. -/
@[reassoc]
theorem canHom_comp {V W Z X : Scheme.{u}} (r : V ⟶ W) (q : W ⟶ Z) (g : Z ⟶ X) (s : V ⟶ Z)
    (pi : W ⟶ X) (t : V ⟶ X) (hs : r ≫ q = s) (hpi : q ≫ g = pi) (ht : s ≫ g = t)
    (hrt : r ≫ pi = t) (F : X.Modules) :
    (Scheme.Modules.pullback r).map (canHom q g pi hpi F) ≫ canHom r pi t hrt F
      = canHom r q s hs ((Scheme.Modules.pullback g).obj F) ≫ canHom s g t ht F := by
  subst hpi
  subst hs
  subst ht
  have key := CategoryTheory.NatTrans.congr_app
    (Scheme.Modules.pseudofunctor_associativity (f := r) (g := q) (h := g)) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToHom_app, Category.id_comp] at key
  have hE : (Scheme.Modules.pullback (r ≫ q ≫ g)).obj F
      = (Scheme.Modules.pullback ((r ≫ q) ≫ g)).obj F := by rw [hrt]
  have e1 : canHom r (q ≫ g) ((r ≫ q) ≫ g) hrt F
      = (Scheme.Modules.pullbackComp r (q ≫ g)).hom.app F ≫ eqToHom hE := by
    simp [canHom, Scheme.Modules.pullbackCongr]
  rw [canHom_rfl, canHom_rfl, canHom_rfl, e1, ← key]
  simp

/-! ### Transporting along a further morphism -/

/-- A morphism between pullbacks along `g`, carried along a further morphism `m` with
`m ≫ g = mg` to a morphism between pullbacks along `mg`, by conjugating the pullback of the
morphism along `m` with the canonical comparison. -/
noncomputable def canStep {Zk Zj Zi : Scheme.{u}} (m : Zk ⟶ Zj) (g : Zj ⟶ Zi) (mg : Zk ⟶ Zi)
    (hmg : m ≫ g = mg) {F G : Zi.Modules}
    (ψ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G) :
    (Scheme.Modules.pullback mg).obj F ⟶ (Scheme.Modules.pullback mg).obj G :=
  (canIso m g mg hmg F).inv ≫ (Scheme.Modules.pullback m).map ψ ≫ (canIso m g mg hmg G).hom

/-- If a morphism `ψ` between pullbacks along `g` is carried by the canonical comparison to a
morphism `φ` between pullbacks along `πi`, then so is the morphism obtained from `ψ` by pulling
back one stage further, along `m`. -/
theorem canonical_eq_of_further_step {L Zk Zj Zi : Scheme.{u}} (πk : L ⟶ Zk) (m : Zk ⟶ Zj)
    (πj : L ⟶ Zj) (hm : πk ≫ m = πj) (g : Zj ⟶ Zi) (πi : L ⟶ Zi) (hg : πj ≫ g = πi)
    (mg : Zk ⟶ Zi) (hmg : m ≫ g = mg) (hki : πk ≫ mg = πi) {F G : Zi.Modules}
    (ψ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G)
    (φ : (Scheme.Modules.pullback πi).obj F ⟶ (Scheme.Modules.pullback πi).obj G)
    (h : (Scheme.Modules.pullback πj).map ψ ≫ canHom πj g πi hg G
      = canHom πj g πi hg F ≫ φ) :
    (Scheme.Modules.pullback πk).map (canStep m g mg hmg ψ) ≫ canHom πk mg πi hki G
      = canHom πk mg πi hki F ≫ φ := by
  have coc := canHom_comp πk m g πj mg πi hm hmg hg hki
  simp only [canStep, Functor.map_comp, Category.assoc, canIso_hom]
  rw [coc, canHom_naturality_assoc, h, ← reassoc_of% (coc F), ← canIso_hom m g mg hmg F,
    Iso.inv_hom_id_map_assoc]

end Stacks.AlgebraicGeometry.ModuleLimits

end
