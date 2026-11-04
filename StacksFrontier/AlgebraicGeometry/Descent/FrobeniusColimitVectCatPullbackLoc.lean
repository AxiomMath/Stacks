module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundlesCube

/-!
# Base change of the square at the level of the categorical fibre product

Let `p` be a prime and let

```
E ⟶ X'          D ⟶ V'
↓    ↓    and    ↓    ↓
Z ⟶ X           W ⟶ V
```

be two commutative squares of schemes in characteristic `p`, with four vertical morphisms
`ιV, ιV', ιW, ιD` making the four side faces of the resulting cube commute. The comparison
functor of [Stacks, Tag 0EXD] is attached to each of the two squares, and the trivialising-cover
step of that tag needs the two to be compared: an object of the categorical fibre product over
the bottom square has to be *restricted* to the top square, compatibly with the comparison
functor.

This file supplies both. The restriction is a functor

`𝒮_Z ×_{𝒮_E} 𝒮_{X'} ⟶ 𝒮_W ×_{𝒮_D} 𝒮_{V'}`

built from the two side faces at the exceptional corner, and the compatibility is
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_cube_app` — it is exactly the cube
coherence, and nothing else.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitVectorBundlesCatPullbackLoc`: **the restriction functor on
  the categorical fibre products**, for two commutative squares related by four side faces. Its
  two components are the transition functors of the vertical morphisms at the centre and at the
  modification; the structural isomorphism is conjugated by the two square comparisons at the
  exceptional corner.

## Main results

* `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_flip_hom_app`: **the square
  comparison of the transposed square is the inverse of the square comparison.** The cube
  coherence is stated with the transposed spelling at the top and bottom faces and the comparison
  functor with the untransposed one, so the two have to be matched.
* `AlgebraicGeometry.frobeniusColimitVectorBundlesCatPullbackLocIso`: **the comparison functor
  commutes with base change of the square**, as an isomorphism
  `Loc (G M) ≅ G' (ι^* M)` natural in `M`.

## Implementation notes

Everything here is stated with the eight corners, the eight transition functors and the six
commutativities as *variables*: nothing of [Stacks, Example 0EVH] enters, and against variables
the comparison of a component of a morphism of the categorical fibre product with the corner of
the square is immediate, whereas with the concrete corners substituted the unifier unfolds
`CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback` and the
Frobenius colimit at once and exhausts the `isDefEq` budget.

The four side commutativities are supplied as ordinary equations between morphisms of schemes,
exactly as in `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_cube_app`: at the square
of [Stacks, Example 0EVH] over a basic open of the base the fourth corner of the top face is
`e ⁻¹ᵁ (z ⁻¹ᵁ D(g))` read one way and `q ⁻¹ᵁ (b ⁻¹ᵁ D(g))` read the other, and a statement that
computed the top square from the bottom one would carry a transport inside its type.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

section Flip

variable {X X' Z E : Scheme.{u}} (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
  (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
  (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)

/-- **The square comparison of the transposed square is the inverse of the square comparison.**
Both are built from the two composition isomorphisms of the transition functors and the
`CategoryTheory.eqToIso` of the square's commutativity, in opposite orders. -/
theorem frobeniusColimitVectorBundlesSquareIso_flip_hom_app (hw : q ≫ b = e ≫ z)
    (M : frobeniusColimitVectorBundles X p hX) :
    (frobeniusColimitVectorBundlesSquareIso p z b e q hX hZ hX' hE hw.symm).hom.app M =
      (frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).inv.app M := by
  simp [frobeniusColimitVectorBundlesSquareIso]

end Flip

section Loc

variable {X X' Z E V V' W D : Scheme.{u}}
  (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
  (bV : V' ⟶ V) (zV : W ⟶ V) (qV : D ⟶ V') (eV : D ⟶ W)
  (ιV : V ⟶ X) (ιV' : V' ⟶ X') (ιW : W ⟶ Z) (ιD : D ⟶ E)
  (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
  (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)
  (hV : IsInCharacteristic V p) (hV' : IsInCharacteristic V' p)
  (hW : IsInCharacteristic W p) (hD : IsInCharacteristic D p)
  (sq : qV ≫ ιV' = ιD ≫ q) (se : eV ≫ ιW = ιD ≫ e)

/-- **The restriction functor on the categorical fibre products attached to two commutative
squares related by four side faces.**

On objects it restricts the module over the centre along `ιW`, the module over the modification
along `ιV'`, and conjugates the structural isomorphism by the two square comparisons at the
exceptional corner; on morphisms it restricts both components, the compatibility following from
the naturality of those two comparisons. -/
noncomputable def frobeniusColimitVectorBundlesCatPullbackLoc :
    CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
        (frobeniusColimitVectorBundlesPullback p q hE hX') ⥤
      CategoricalPullback (frobeniusColimitVectorBundlesPullback p eV hD hW)
        (frobeniusColimitVectorBundlesPullback p qV hD hV') where
  obj T :=
    { fst := (frobeniusColimitVectorBundlesPullback p ιW hW hZ).obj T.fst
      snd := (frobeniusColimitVectorBundlesPullback p ιV' hV' hX').obj T.snd
      iso :=
        ((frobeniusColimitVectorBundlesSquareIso p ιW e eV ιD hZ hW hE hD se).app T.fst).symm ≪≫
          (frobeniusColimitVectorBundlesPullback p ιD hD hE).mapIso T.iso ≪≫
            (frobeniusColimitVectorBundlesSquareIso p ιV' q qV ιD hX' hV' hE hD sq).app T.snd }
  map {T T'} f :=
    { fst := (frobeniusColimitVectorBundlesPullback p ιW hW hZ).map f.fst
      snd := (frobeniusColimitVectorBundlesPullback p ιV' hV' hX').map f.snd
      w := by
        have hfst := (frobeniusColimitVectorBundlesSquareIso p ιW e eV ιD
          hZ hW hE hD se).inv.naturality f.fst
        have hsnd := (frobeniusColimitVectorBundlesSquareIso p ιV' q qV ιD
          hX' hV' hE hD sq).hom.naturality f.snd
        have hw := f.w
        simp only [Functor.comp_obj, Functor.comp_map] at hfst hsnd
        simp only [Iso.app_hom, Iso.app_inv, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
          Category.assoc]
        rw [reassoc_of% hfst, ← Functor.map_comp_assoc, hw, Functor.map_comp_assoc, hsnd] }
  map_id T := CategoricalPullback.hom_ext (by simp) (by simp)
  map_comp f g := CategoricalPullback.hom_ext (by simp) (by simp)

/-- **The comparison functor commutes with base change of the square.** The restriction of the
image of `M` under the comparison functor of the bottom square is the image of the restriction of
`M` under the comparison functor of the top square. This is exactly the cube coherence
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_cube_app`, read through
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_flip_hom_app` to match the transposed
spelling the cube uses at the top and bottom faces. -/
noncomputable def frobeniusColimitVectorBundlesCatPullbackLocIso (hw : q ≫ b = e ≫ z)
    (hwV : qV ≫ bV = eV ≫ zV) (sb : bV ≫ ιV = ιV' ≫ b) (sz : zV ≫ ιV = ιW ≫ z)
    (M : frobeniusColimitVectorBundles X p hX) :
    (frobeniusColimitVectorBundlesCatPullbackLoc p q e qV eV ιV' ιW ιD
          hX' hZ hE hV' hW hD sq se).obj
        ((frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).obj M) ≅
      (frobeniusColimitVectorBundlesComparison p bV zV qV eV hV hV' hW hD hwV).obj
        ((frobeniusColimitVectorBundlesPullback p ιV hV hX).obj M) :=
  CategoricalPullback.mkIso
    ((frobeniusColimitVectorBundlesSquareIso p ιV z zV ιW hX hV hZ hW sz).app M)
    ((frobeniusColimitVectorBundlesSquareIso p ιV b bV ιV' hX hV hX' hV' sb).app M)
    (by
      have hcube := frobeniusColimitVectorBundlesSquareIso_cube_app p b z q e bV zV qV eV
        ιV ιV' ιW ιD hX hX' hZ hE hV hV' hW hD hw hwV sb sz sq se M
      rw [frobeniusColimitVectorBundlesSquareIso_flip_hom_app p bV zV qV eV hV hV' hW hD hwV,
        frobeniusColimitVectorBundlesSquareIso_flip_hom_app p b z q e hX hX' hZ hE hw] at hcube
      have hid : (frobeniusColimitVectorBundlesPullback p ιD hD hE).map
            ((frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app M) ≫
          (frobeniusColimitVectorBundlesPullback p ιD hD hE).map
            ((frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).inv.app M) =
            𝟙 _ := by
        rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
          CategoryTheory.Functor.map_id]
      have key := congrArg (fun t =>
        (frobeniusColimitVectorBundlesPullback p ιD hD hE).map
            ((frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app M) ≫
          t ≫ (frobeniusColimitVectorBundlesSquareIso p bV zV qV eV hV hV' hW hD hwV).hom.app
            ((frobeniusColimitVectorBundlesPullback p ιV hV hX).obj M)) hcube
      simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
        reassoc_of% hid] at key
      have key2 : (frobeniusColimitVectorBundlesPullback p eV hD hW).map
              ((frobeniusColimitVectorBundlesSquareIso p ιV z zV ιW hX hV hZ hW sz).hom.app M) ≫
            (frobeniusColimitVectorBundlesSquareIso p bV zV qV eV hV hV' hW hD hwV).hom.app
              ((frobeniusColimitVectorBundlesPullback p ιV hV hX).obj M) =
          (frobeniusColimitVectorBundlesSquareIso p ιW e eV ιD hZ hW hE hD se).inv.app
              ((frobeniusColimitVectorBundlesPullback p z hZ hX).obj M) ≫
            (frobeniusColimitVectorBundlesPullback p ιD hD hE).map
                ((frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app M) ≫
              (frobeniusColimitVectorBundlesSquareIso p ιV' q qV ιD hX' hV' hE hD sq).hom.app
                  ((frobeniusColimitVectorBundlesPullback p b hX' hX).obj M) ≫
                (frobeniusColimitVectorBundlesPullback p qV hD hV').map
                  ((frobeniusColimitVectorBundlesSquareIso p ιV b bV ιV'
                    hX hV hX' hV' sb).hom.app M) := by
        rw [key]
        simp
      simp only [frobeniusColimitVectorBundlesCatPullbackLoc, Iso.app_hom, Iso.app_inv,
        Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
      exact key2)

end Loc

end AlgebraicGeometry

end
