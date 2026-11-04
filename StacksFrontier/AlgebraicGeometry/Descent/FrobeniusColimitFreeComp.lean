module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackFreeComp

/-!
# The comparison of the transition functors around a square, at a free module

Let `p` be a prime. The transition functors of Stacks Tag 0EXE are extension of scalars along the
canonical morphisms of Frobenius-colimit structure sheaves, and each of them carries a free
module to a free module by Mathlib's
`CategoryTheory.SheafOfModules.pullbackObjFreeIso`. For a commutative square of schemes in
characteristic `p` the two composite transition functors around the square are compared by
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso`, and this file proves that **that
comparison agrees with the two free identifications**: going around the square one way and
identifying the free module at each stage is the same as going the other way and identifying
there.

This is the compatibility that lets the cartesian square of Hom-sets of free modules
(`AlgebraicGeometry.isPullback_frobeniusColimitFreeHom_twoGenerator`) be read on the canonical
cospan `g ↦ e^*g ≫ α`, `k ↦ α ≫ d^*k` which full faithfulness of the comparison functor asks
for, by
`CategoryTheory.Limits.CategoricalPullback.fullyFaithful_squareComparison_iff_isPullback`.

## Main results

* `AlgebraicGeometry.frobeniusColimitPullbackCompOfEq_unit` and
  `AlgebraicGeometry.frobeniusColimitPullbackCompOfEq_free`: **the composition comparison of the
  transition functors is compatible with the unit, respectively the free, identifications.** The
  morphisms of Frobenius-colimit sheaves are parameters and the equations presenting the
  composites are hypotheses, exactly as in
  `AlgebraicGeometry.frobeniusColimitPullbackCompOfEq` itself.
* `AlgebraicGeometry.frobeniusColimitPullbackComp_free`: the instance of the previous result at
  the canonical morphisms.
* `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_hom_app_hom_free`: **the comparison of
  the two composite transition functors around a commutative square agrees with the free
  identifications at a free module.**

## Implementation notes

Every transport is substituted away rather than computed with. The composition comparison of the
transition functors is `AlgebraicGeometry.frobeniusColimitPullbackCompOfEq`, which carries an
`CategoryTheory.eqToIso` along the equation presenting the composite morphism of
Frobenius-colimit sheaves; and the square comparison carries a second one, along the square's own
commutativity. Each is removed by a lemma stating the transport with *both* morphisms as
parameters and the equality as a hypothesis — so that `subst` applies — and the untransported
statement is then Mathlib-level, namely
`Stacks.SheafOfModules.pullbackComp_hom_app_free_comp_pullbackObjFreeIso_hom`.

The two transport lemmas are stated here and not at an arbitrary site because a bound morphism of
sheaves of rings has to admit extension of scalars for the transported expression to elaborate at
all: `CategoryTheory.SheafOfModules.pullback` takes the right-adjointness of the pushforward as an
instance, and on the site of opens of a scheme that instance is available for *every* morphism,
which is what makes `congrArg (fun m => pullback m) h` typecheck. At an arbitrary site it is a
hypothesis on one fixed morphism and the same expression does not elaborate.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-- **Transporting the unit identification along an equality of morphisms of Frobenius-colimit
sheaves.** Both morphisms are parameters and the equality is a hypothesis, so that the transport
can be substituted away. -/
theorem eqToHom_comp_pullbackObjUnitToUnit_frobeniusColimit {X Z : Scheme.{u}} (g : X ⟶ Z)
    (hX : IsInCharacteristic X p) (hZ : IsInCharacteristic Z p)
    {χ χ' : frobeniusColimitRingSheaf Z p hZ ⟶
      (g.ringSheafPushforward).obj (frobeniusColimitRingSheaf X p hX)} (h : χ = χ') :
    (eqToIso (congrArg (fun m => _root_.SheafOfModules.pullback.{u} m) h)).hom.app
        (_root_.SheafOfModules.unit (frobeniusColimitRingSheaf Z p hZ)) ≫
      _root_.SheafOfModules.pullbackObjUnitToUnit χ' =
    _root_.SheafOfModules.pullbackObjUnitToUnit χ := by
  subst h
  simp

/-- **The composition comparison of the transition functors is compatible with the unit
identifications.** -/
theorem frobeniusColimitPullbackCompOfEq_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (hZ : IsInCharacteristic Z p)
    (a : frobeniusColimitRingSheaf Z p hZ ⟶
      (g.ringSheafPushforward).obj (frobeniusColimitRingSheaf Y p hY))
    (b : frobeniusColimitRingSheaf Y p hY ⟶
      (f.ringSheafPushforward).obj (frobeniusColimitRingSheaf X p hX))
    (c : frobeniusColimitRingSheaf Z p hZ ⟶
      ((f ≫ g).ringSheafPushforward).obj (frobeniusColimitRingSheaf X p hX))
    (hc : c = a ≫ (g.ringSheafPushforward).map b) :
    (frobeniusColimitPullbackCompOfEq p f g hX hY hZ a b c hc).hom.app
          (_root_.SheafOfModules.unit (frobeniusColimitRingSheaf Z p hZ)) ≫
        _root_.SheafOfModules.pullbackObjUnitToUnit c =
      (_root_.SheafOfModules.pullback.{u} b).map
          (_root_.SheafOfModules.pullbackObjUnitToUnit a) ≫
        _root_.SheafOfModules.pullbackObjUnitToUnit b := by
  simp only [frobeniusColimitPullbackCompOfEq, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  erw [eqToHom_comp_pullbackObjUnitToUnit_frobeniusColimit p (f ≫ g) hX hZ hc.symm]
  exact Stacks.SheafOfModules.pullbackComp_hom_app_unit_comp_pullbackObjUnitToUnit a b

/-- **The composition comparison of the transition functors at the canonical morphisms is
compatible with the free identifications.** The free statement is deduced from the unit statement
by `Stacks.SheafOfModules.free_comp_pullbackObjFreeIso_hom_of_unit` rather than proved again. -/
theorem frobeniusColimitPullbackComp_free {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (hZ : IsInCharacteristic Z p) (I : Type u) :
    (frobeniusColimitPullbackComp p f g hX hY hZ).hom.app
          (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf Z p hZ) I) ≫
        (_root_.SheafOfModules.pullbackObjFreeIso
          (frobeniusColimitStructureSheafHom p (f ≫ g) hX hZ) I).hom =
      (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p f hX hY)).map
          (_root_.SheafOfModules.pullbackObjFreeIso
            (frobeniusColimitStructureSheafHom p g hY hZ) I).hom ≫
        (_root_.SheafOfModules.pullbackObjFreeIso
          (frobeniusColimitStructureSheafHom p f hX hY) I).hom :=
  Stacks.SheafOfModules.free_comp_pullbackObjFreeIso_hom_of_unit
    (frobeniusColimitStructureSheafHom p g hY hZ)
    (frobeniusColimitStructureSheafHom p f hX hY)
    (frobeniusColimitStructureSheafHom p (f ≫ g) hX hZ)
    (frobeniusColimitPullbackComp p f g hX hY hZ).hom
    (frobeniusColimitPullbackCompOfEq_unit p f g hX hY hZ _ _ _
      (frobeniusColimitStructureSheafHom_comp p f g hX hY hZ)) I

/-- **Transporting the free identification along an equality of morphisms of schemes.** Both
morphisms are parameters and the equality is a hypothesis, so that the transport the square
comparison carries along the square's commutativity can be substituted away. -/
theorem eqToHom_comp_pullbackObjFreeIso_hom_frobeniusColimit {E X : Scheme.{u}}
    {w w' : E ⟶ X} (hE : IsInCharacteristic E p) (hX : IsInCharacteristic X p)
    (h : w = w') (I : Type u) :
    (eqToIso (congrArg (fun m : E ⟶ X => _root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p m hE hX)) h)).hom.app
        (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) I) ≫
      (_root_.SheafOfModules.pullbackObjFreeIso
        (frobeniusColimitStructureSheafHom p w' hE hX) I).hom =
    (_root_.SheafOfModules.pullbackObjFreeIso
      (frobeniusColimitStructureSheafHom p w hE hX) I).hom := by
  subst h
  simp

/-- The transport of the transition functors along an equality of morphisms of schemes, read on
the underlying sheaves of modules. -/
theorem eqToIso_frobeniusColimitVectorBundlesPullback_hom_app_hom {E X : Scheme.{u}}
    {w w' : E ⟶ X} (hE : IsInCharacteristic E p) (hX : IsInCharacteristic X p)
    (h : w = w') (M : frobeniusColimitVectorBundles X p hX) :
    ((eqToIso (congrArg (fun m : E ⟶ X =>
          frobeniusColimitVectorBundlesPullback p m hE hX) h)).hom.app M).hom =
      (eqToIso (congrArg (fun m : E ⟶ X => _root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p m hE hX)) h)).hom.app M.obj := by
  subst h
  rfl

/-- The composition comparison of the transition functors on finite locally free modules, read on
the underlying sheaves of modules. -/
theorem frobeniusColimitVectorBundlesPullbackComp_hom_app_hom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (hZ : IsInCharacteristic Z p) (M : frobeniusColimitVectorBundles Z p hZ) :
    ((frobeniusColimitVectorBundlesPullbackComp p f g hX hY hZ).hom.app M).hom =
      (frobeniusColimitPullbackComp p f g hX hY hZ).hom.app M.obj := rfl

/-- The inverse of the composition comparison, read on the underlying sheaves of modules. -/
theorem frobeniusColimitVectorBundlesPullbackComp_inv_app_hom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (hZ : IsInCharacteristic Z p) (M : frobeniusColimitVectorBundles Z p hZ) :
    ((frobeniusColimitVectorBundlesPullbackComp p f g hX hY hZ).inv.app M).hom =
      (frobeniusColimitPullbackComp p f g hX hY hZ).inv.app M.obj := rfl

section Square

variable {X X' Z E : Scheme.{u}} (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
  (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
  (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)

/-- **The comparison of the two composite extensions of scalars around a commutative square**, on
all sheaves of modules over the Frobenius colimits. This is the construction underlying
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso`, which is its restriction to the
finite locally free modules. -/
noncomputable def frobeniusColimitPullbackSquareIso (hw : q ≫ b = e ≫ z) :
    _root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p z hZ hX) ⋙
        _root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p e hE hZ) ≅
      _root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p b hX' hX) ⋙
        _root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p q hE hX') :=
  frobeniusColimitPullbackComp p e z hE hZ hX ≪≫
    eqToIso (congrArg (fun m : E ⟶ X => _root_.SheafOfModules.pullback.{u}
      (frobeniusColimitStructureSheafHom p m hE hX)) hw.symm) ≪≫
    (frobeniusColimitPullbackComp p q b hE hX' hX).symm

/-- **The comparison of the two composite extensions of scalars around a commutative square
agrees with the free identifications at a free module.** Composing it with the free
identification along the route through the modification gives the free identification along the
route through the centre. -/
theorem frobeniusColimitPullbackSquareIso_free (hw : q ≫ b = e ≫ z) (I : Type u) :
    (frobeniusColimitPullbackSquareIso p b z q e hX hX' hZ hE hw).hom.app
          (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) I) ≫
        ((_root_.SheafOfModules.pullback.{u}
              (frobeniusColimitStructureSheafHom p q hE hX')).map
            (_root_.SheafOfModules.pullbackObjFreeIso
              (frobeniusColimitStructureSheafHom p b hX' hX) I).hom ≫
          (_root_.SheafOfModules.pullbackObjFreeIso
            (frobeniusColimitStructureSheafHom p q hE hX') I).hom) =
      (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p e hE hZ)).map
          (_root_.SheafOfModules.pullbackObjFreeIso
            (frobeniusColimitStructureSheafHom p z hZ hX) I).hom ≫
        (_root_.SheafOfModules.pullbackObjFreeIso
          (frobeniusColimitStructureSheafHom p e hE hZ) I).hom := by
  rw [← frobeniusColimitPullbackComp_free p q b hE hX' hX I]
  simp only [frobeniusColimitPullbackSquareIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [eqToHom_comp_pullbackObjFreeIso_hom_frobeniusColimit p hE hX hw.symm I]
  exact frobeniusColimitPullbackComp_free p e z hE hZ hX I

/-- The comparison of the two composite transition functors around a commutative square, read on
the underlying sheaves of modules, is the comparison of the two composite extensions of scalars.
The two are built from the same data; only the transport along the square's commutativity has to
be matched, and that is substituted away. -/
theorem frobeniusColimitVectorBundlesSquareIso_hom_app_hom (hw : q ≫ b = e ≫ z)
    (M : frobeniusColimitVectorBundles X p hX) :
    ((frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app M).hom =
      (frobeniusColimitPullbackSquareIso p b z q e hX hX' hZ hE hw).hom.app M.obj := by
  have h1 : ((frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app M).hom =
      ((frobeniusColimitVectorBundlesPullbackComp p e z hE hZ hX).hom.app M).hom ≫
        ((eqToIso (congrArg (fun m : E ⟶ X =>
          frobeniusColimitVectorBundlesPullback p m hE hX) hw.symm)).hom.app M).hom ≫
        ((frobeniusColimitVectorBundlesPullbackComp p q b hE hX' hX).inv.app M).hom := rfl
  have h2 : (frobeniusColimitPullbackSquareIso p b z q e hX hX' hZ hE hw).hom.app M.obj =
      (frobeniusColimitPullbackComp p e z hE hZ hX).hom.app M.obj ≫
        (eqToIso (congrArg (fun m : E ⟶ X => _root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p m hE hX)) hw.symm)).hom.app M.obj ≫
        (frobeniusColimitPullbackComp p q b hE hX' hX).inv.app M.obj := rfl
  rw [h1, h2, frobeniusColimitVectorBundlesPullbackComp_hom_app_hom,
    frobeniusColimitVectorBundlesPullbackComp_inv_app_hom,
    eqToIso_frobeniusColimitVectorBundlesPullback_hom_app_hom p hE hX hw.symm M]
  rfl

/-- `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_hom_app_hom` at a free module, with
the index type written out rather than read off the object. The two statements differ only by an
iota reduction, but the reduced form is the one a rewrite can leave in a shape that
`AlgebraicGeometry.frobeniusColimitPullbackSquareIso_free` matches without a search. -/
theorem frobeniusColimitVectorBundlesSquareIso_hom_app_free_hom (hw : q ≫ b = e ≫ z)
    (I : Type u)
    (hI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) I)) :
    ((frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app
        ⟨_root_.SheafOfModules.free I, hI⟩).hom =
      (frobeniusColimitPullbackSquareIso p b z q e hX hX' hZ hE hw).hom.app
        (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) I) :=
  frobeniusColimitVectorBundlesSquareIso_hom_app_hom p b z q e hX hX' hZ hE hw
    ⟨_root_.SheafOfModules.free I, hI⟩

/-- **The comparison of the two composite transition functors around a commutative square agrees
with the free identifications at a free module.** Composing it with the free identification along
the route through the modification gives the free identification along the route through the
centre.

This is the compatibility that
`CategoryTheory.Limits.CategoricalPullback.fullyFaithful_squareComparison_iff_isPullback` needs in
order to consume a cartesian square of Hom-sets of free modules. -/
theorem frobeniusColimitVectorBundlesSquareIso_hom_app_hom_free (hw : q ≫ b = e ≫ z)
    (I : Type u)
    (hI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) I)) :
    ((frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app
          ⟨_root_.SheafOfModules.free I, hI⟩).hom ≫
        ((_root_.SheafOfModules.pullback.{u}
              (frobeniusColimitStructureSheafHom p q hE hX')).map
            (_root_.SheafOfModules.pullbackObjFreeIso
              (frobeniusColimitStructureSheafHom p b hX' hX) I).hom ≫
          (_root_.SheafOfModules.pullbackObjFreeIso
            (frobeniusColimitStructureSheafHom p q hE hX') I).hom) =
      (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p e hE hZ)).map
          (_root_.SheafOfModules.pullbackObjFreeIso
            (frobeniusColimitStructureSheafHom p z hZ hX) I).hom ≫
        (_root_.SheafOfModules.pullbackObjFreeIso
          (frobeniusColimitStructureSheafHom p e hE hZ) I).hom := by
  conv_lhs => rw [frobeniusColimitVectorBundlesSquareIso_hom_app_free_hom
    p b z q e hX hX' hZ hE hw I hI]
  exact frobeniusColimitPullbackSquareIso_free p b z q e hX hX' hZ hE hw I

end Square

end AlgebraicGeometry

end
