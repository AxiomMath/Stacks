module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectCatPullbackLoc

/-!
# The restriction functor on the categorical fibre products is pseudofunctorial

Let `p` be a prime. `StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectCatPullbackLoc`
attaches to two commutative squares of schemes in characteristic `p`, related by side faces, a
restriction functor

`𝒮_Z ×_{𝒮_E} 𝒮_{X'} ⟶ 𝒮_W ×_{𝒮_D} 𝒮_{V'}`

between the categorical fibre products of the categories of finite locally free modules over the
Frobenius colimits of the structure sheaves. This file shows that restricting along a cube and then
along a second cube stacked on it is restricting along the composite cube, which is what the
trivialising-cover step of [Stacks, Tag 0EXD] needs to compare restrictions to opens of opens.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitVectorBundlesCatPullbackLocComp`: **the composite of two
  restriction functors is the restriction functor of the composite cube**. Its components at the
  centre and at the modification are the triangle comparisons of the side maps.

## Main results

* `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_vpaste_app`: **the vertical pasting
  law** for the square comparisons, in the shape the restriction functor uses.
* `AlgebraicGeometry.frobeniusColimitVectorBundlesPullbackTriangleIso_pentagon_app`: the
  associativity pentagon of the triangle comparisons on the finite locally free modules.
* `AlgebraicGeometry.frobeniusColimitVectorBundlesCatPullbackLocIso_naturality`: the base-change
  comparison of the comparison functor is natural.
* `AlgebraicGeometry.frobeniusColimitVectorBundlesCatPullbackLocComp_locIso`: the composition
  comparison is compatible with the base-change comparisons.
* `AlgebraicGeometry.frobeniusColimitVectorBundlesCatPullbackLocComp_pentagon`: the pentagon of
  the composition comparisons.

## Implementation notes

As in `StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectCatPullbackLoc`, every corner,
transition functor and commutativity is a variable, and the composite side maps `cV'`, `cW`, `cD`
are variables subject to equations, so that the vertical pasting law is an instance of
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_paste_app` and no transport occurs.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-! ### The associativity pentagon of the triangle comparisons -/

section Triangle

variable {Q R S T : Scheme.{u}}

/-- **The associativity pentagon of the triangle comparisons, on the finite locally free
modules.** For composable `f`, `g`, `h` and morphisms `fg`, `gh`, `fgh` filling the four
triangles they span, the two ways of comparing the three-fold restriction with the restriction
along `fgh` agree. It is the module-level
`AlgebraicGeometry.frobeniusColimitPullbackTriangleIso_pentagon_app`, read on the underlying
sheaves of modules. -/
@[reassoc]
theorem frobeniusColimitVectorBundlesPullbackTriangleIso_pentagon_app (f : Q ⟶ R) (g : R ⟶ S)
    (h : S ⟶ T) (fg : Q ⟶ S) (gh : R ⟶ T) (fgh : Q ⟶ T)
    (hQ : IsInCharacteristic Q p) (hR : IsInCharacteristic R p) (hS : IsInCharacteristic S p)
    (hT : IsInCharacteristic T p)
    (wfg : f ≫ g = fg) (wgh : g ≫ h = gh) (w₁ : f ≫ gh = fgh) (w₂ : fg ≫ h = fgh)
    (M : frobeniusColimitVectorBundles T p hT) :
    (frobeniusColimitVectorBundlesPullbackTriangleIso p f g fg hQ hR hS wfg).hom.app
          ((frobeniusColimitVectorBundlesPullback p h hS hT).obj M) ≫
        (frobeniusColimitVectorBundlesPullbackTriangleIso p fg h fgh hQ hS hT w₂).hom.app M =
      (frobeniusColimitVectorBundlesPullback p f hQ hR).map
          ((frobeniusColimitVectorBundlesPullbackTriangleIso p g h gh hR hS hT wgh).hom.app M) ≫
        (frobeniusColimitVectorBundlesPullbackTriangleIso p f gh fgh hQ hR hT w₁).hom.app M := by
  refine ObjectProperty.hom_ext _ ?_
  simpa [frobeniusColimitVectorBundlesPullbackTriangleIso_hom_app_hom] using
    frobeniusColimitPullbackTriangleIso_pentagon_app p f g h fg gh fgh hQ hR hS hT
      wfg wgh w₁ w₂ M.obj

end Triangle

section Loc
variable {X' Z E V' W D V₂' W₂ D₂ : Scheme.{u}}
  (q : E ⟶ X') (e : E ⟶ Z) (qV : D ⟶ V') (eV : D ⟶ W) (q₂ : D₂ ⟶ V₂') (e₂ : D₂ ⟶ W₂)
  (ιV' : V' ⟶ X') (ιW : W ⟶ Z) (ιD : D ⟶ E)
  (κV' : V₂' ⟶ V') (κW : W₂ ⟶ W) (κD : D₂ ⟶ D)
  (cV' : V₂' ⟶ X') (cW : W₂ ⟶ Z) (cD : D₂ ⟶ E)
  (hX' : IsInCharacteristic X' p) (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)
  (hV' : IsInCharacteristic V' p) (hW : IsInCharacteristic W p) (hD : IsInCharacteristic D p)
  (hV₂' : IsInCharacteristic V₂' p) (hW₂ : IsInCharacteristic W₂ p)
  (hD₂ : IsInCharacteristic D₂ p)
  (sq : qV ≫ ιV' = ιD ≫ q) (se : eV ≫ ιW = ιD ≫ e)
  (sq₂ : q₂ ≫ κV' = κD ≫ qV) (se₂ : e₂ ≫ κW = κD ≫ eV)
  (sqc : q₂ ≫ cV' = cD ≫ q) (sec : e₂ ≫ cW = cD ≫ e)

/-- **The vertical pasting law for the square comparisons of the restriction functor.** For two
commutative squares `qV ≫ ιV' = ιD ≫ q` and `q₂ ≫ κV' = κD ≫ qV` stacked on each other, the
comparison of the outer square `q₂ ≫ cV' = cD ≫ q` is the pasting of the two inner comparisons
with the triangle comparisons of the composite side maps. -/
theorem frobeniusColimitVectorBundlesSquareIso_vpaste_app
    (hcV' : κV' ≫ ιV' = cV') (hcD : κD ≫ ιD = cD) (M : frobeniusColimitVectorBundles X' p hX') :
    (frobeniusColimitVectorBundlesSquareIso p cV' q q₂ cD hX' hV₂' hE hD₂ sqc).hom.app M =
      (frobeniusColimitVectorBundlesPullbackTriangleIso p κD ιD cD hD₂ hD hE hcD).inv.app
          ((frobeniusColimitVectorBundlesPullback p q hE hX').obj M) ≫
        (frobeniusColimitVectorBundlesPullback p κD hD₂ hD).map
          ((frobeniusColimitVectorBundlesSquareIso p ιV' q qV ιD hX' hV' hE hD sq).hom.app M) ≫
        (frobeniusColimitVectorBundlesSquareIso p κV' qV q₂ κD hV' hV₂' hD hD₂ sq₂).hom.app
            ((frobeniusColimitVectorBundlesPullback p ιV' hV' hX').obj M) ≫
          (frobeniusColimitVectorBundlesPullback p q₂ hD₂ hV₂').map
            ((frobeniusColimitVectorBundlesPullbackTriangleIso p κV' ιV' cV'
              hV₂' hV' hX' hcV').hom.app M) := by
  rw [← frobeniusColimitVectorBundlesSquareIso_paste_app p κD ιD q₂ qV q κV' ιV'
    hD₂ hD hE hV₂' hV' hX' sq₂.symm sq.symm cD hcD cV' hcV' sqc.symm M, Iso.inv_hom_id_app_assoc]

/-- The vertical pasting law with the triangle comparison of `κD`, `ιD`, `cD` moved to the left. -/
private theorem frobeniusColimitVectorBundlesSquareIso_vpaste_app'
    (hcV' : κV' ≫ ιV' = cV') (hcD : κD ≫ ιD = cD) (M : frobeniusColimitVectorBundles X' p hX') :
    (frobeniusColimitVectorBundlesPullbackTriangleIso p κD ιD cD hD₂ hD hE hcD).hom.app
          ((frobeniusColimitVectorBundlesPullback p q hE hX').obj M) ≫
        (frobeniusColimitVectorBundlesSquareIso p cV' q q₂ cD hX' hV₂' hE hD₂ sqc).hom.app M =
      (frobeniusColimitVectorBundlesPullback p κD hD₂ hD).map
          ((frobeniusColimitVectorBundlesSquareIso p ιV' q qV ιD hX' hV' hE hD sq).hom.app M) ≫
        (frobeniusColimitVectorBundlesSquareIso p κV' qV q₂ κD hV' hV₂' hD hD₂ sq₂).hom.app
            ((frobeniusColimitVectorBundlesPullback p ιV' hV' hX').obj M) ≫
          (frobeniusColimitVectorBundlesPullback p q₂ hD₂ hV₂').map
            ((frobeniusColimitVectorBundlesPullbackTriangleIso p κV' ιV' cV'
              hV₂' hV' hX' hcV').hom.app M) := by
  rw [frobeniusColimitVectorBundlesSquareIso_vpaste_app p q qV q₂ ιV' ιD κV' κD cV' cD
    hX' hE hV' hD hV₂' hD₂ sq sq₂ sqc hcV' hcD M, Iso.hom_inv_id_app_assoc]

/-- **The vertical pasting law for the inverse square comparisons.** The inverse comparison of
the outer square, conjugated by the triangle comparisons of the composite side maps, is the
pasting of the two inverse inner comparisons. -/
private theorem frobeniusColimitVectorBundlesSquareIso_vpaste_inv_app
    (hcV' : κV' ≫ ιV' = cV') (hcD : κD ≫ ιD = cD) (M : frobeniusColimitVectorBundles X' p hX') :
    (frobeniusColimitVectorBundlesPullback p q₂ hD₂ hV₂').map
        ((frobeniusColimitVectorBundlesPullbackTriangleIso p κV' ιV' cV'
          hV₂' hV' hX' hcV').hom.app M) ≫
      (frobeniusColimitVectorBundlesSquareIso p cV' q q₂ cD hX' hV₂' hE hD₂ sqc).inv.app M ≫
      (frobeniusColimitVectorBundlesPullbackTriangleIso p κD ιD cD hD₂ hD hE hcD).inv.app
        ((frobeniusColimitVectorBundlesPullback p q hE hX').obj M) =
    (frobeniusColimitVectorBundlesSquareIso p κV' qV q₂ κD hV' hV₂' hD hD₂ sq₂).inv.app
        ((frobeniusColimitVectorBundlesPullback p ιV' hV' hX').obj M) ≫
      (frobeniusColimitVectorBundlesPullback p κD hD₂ hD).map
        ((frobeniusColimitVectorBundlesSquareIso p ιV' q qV ιD hX' hV' hE hD sq).inv.app M) := by
  have h := frobeniusColimitVectorBundlesSquareIso_vpaste_app' p q qV q₂ ιV' ιD κV' κD cV' cD
    hX' hE hV' hD hV₂' hD₂ sq sq₂ sqc hcV' hcD M
  apply (cancel_epi ((frobeniusColimitVectorBundlesSquareIso p κV' qV q₂ κD
    hV' hV₂' hD hD₂ sq₂).hom.app ((frobeniusColimitVectorBundlesPullback p ιV' hV' hX').obj M))).mp
  apply (cancel_epi ((frobeniusColimitVectorBundlesPullback p κD hD₂ hD).map
    ((frobeniusColimitVectorBundlesSquareIso p ιV' q qV ιD hX' hV' hE hD sq).hom.app M))).mp
  rw [reassoc_of% h.symm, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app, ← Functor.map_comp, Iso.hom_inv_id_app]
  exact ((frobeniusColimitVectorBundlesPullback p κD hD₂ hD).map_id _).symm

/-- **The composite of two restriction functors on the categorical fibre products is the
restriction functor of the composite cube.** Restricting along the cube with side maps
`ιV'`, `ιW`, `ιD` and then along the cube with side maps `κV'`, `κW`, `κD` is restricting along
the cube with the composite side maps `cV' = κV' ≫ ιV'`, `cW = κW ≫ ιW`, `cD = κD ≫ ιD`; the
components at the centre and at the modification are the triangle comparisons. -/
noncomputable def frobeniusColimitVectorBundlesCatPullbackLocComp
    (hcV' : κV' ≫ ιV' = cV') (hcW : κW ≫ ιW = cW) (hcD : κD ≫ ιD = cD) :
    frobeniusColimitVectorBundlesCatPullbackLoc p q e qV eV ιV' ιW ιD
        hX' hZ hE hV' hW hD sq se ⋙
      frobeniusColimitVectorBundlesCatPullbackLoc p qV eV q₂ e₂ κV' κW κD
        hV' hW hD hV₂' hW₂ hD₂ sq₂ se₂ ≅
      frobeniusColimitVectorBundlesCatPullbackLoc p q e q₂ e₂ cV' cW cD
        hX' hZ hE hV₂' hW₂ hD₂ sqc sec :=
  NatIso.ofComponents
    (fun T => CategoricalPullback.mkIso
      ((frobeniusColimitVectorBundlesPullbackTriangleIso p κW ιW cW hW₂ hW hZ hcW).app T.fst)
      ((frobeniusColimitVectorBundlesPullbackTriangleIso p κV' ιV' cV'
        hV₂' hV' hX' hcV').app T.snd)
      (by
        have hV := frobeniusColimitVectorBundlesSquareIso_vpaste_app p q qV q₂ ιV' ιD κV' κD
          cV' cD hX' hE hV' hD hV₂' hD₂ sq sq₂ sqc hcV' hcD T.snd
        have hnat := (frobeniusColimitVectorBundlesPullbackTriangleIso p κD ιD cD
          hD₂ hD hE hcD).inv.naturality T.iso.hom
        simp only [Functor.comp_obj, Functor.comp_map] at hnat
        simp only [frobeniusColimitVectorBundlesCatPullbackLoc, Functor.comp_obj, Iso.app_hom,
          Iso.app_inv, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
        rw [hV, reassoc_of% hnat, reassoc_of%
          (frobeniusColimitVectorBundlesSquareIso_vpaste_inv_app p e eV e₂ ιW ιD κW κD cW cD
            hZ hE hW hD hW₂ hD₂ se se₂ sec hcW hcD T.fst)]
        simp only [Functor.map_comp, Category.assoc]))
    (fun {T T'} f => CategoricalPullback.hom_ext
      ((frobeniusColimitVectorBundlesPullbackTriangleIso p κW ιW cW hW₂ hW hZ hcW).hom.naturality
        f.fst)
      ((frobeniusColimitVectorBundlesPullbackTriangleIso p κV' ιV' cV'
        hV₂' hV' hX' hcV').hom.naturality f.snd))

/-- The first component of the composition comparison at `T` is the triangle comparison of
the side maps `κW`, `ιW`, `cW` at the first component of `T`. -/
@[simp]
lemma frobeniusColimitVectorBundlesCatPullbackLocComp_hom_app_fst
    (hcV' : κV' ≫ ιV' = cV') (hcW : κW ≫ ιW = cW) (hcD : κD ≫ ιD = cD)
    (T : CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p q hE hX')) :
    ((frobeniusColimitVectorBundlesCatPullbackLocComp p q e qV eV q₂ e₂ ιV' ιW ιD κV' κW κD
      cV' cW cD hX' hZ hE hV' hW hD hV₂' hW₂ hD₂ sq se sq₂ se₂ sqc sec hcV' hcW hcD).hom.app
        T).fst =
      (frobeniusColimitVectorBundlesPullbackTriangleIso p κW ιW cW hW₂ hW hZ hcW).hom.app
        T.fst :=
  rfl

/-- The second component of the composition comparison at `T` is the triangle comparison of
the side maps `κV'`, `ιV'`, `cV'` at the second component of `T`. -/
@[simp]
lemma frobeniusColimitVectorBundlesCatPullbackLocComp_hom_app_snd
    (hcV' : κV' ≫ ιV' = cV') (hcW : κW ≫ ιW = cW) (hcD : κD ≫ ιD = cD)
    (T : CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p q hE hX')) :
    ((frobeniusColimitVectorBundlesCatPullbackLocComp p q e qV eV q₂ e₂ ιV' ιW ιD κV' κW κD
      cV' cW cD hX' hZ hE hV' hW hD hV₂' hW₂ hD₂ sq se sq₂ se₂ sqc sec hcV' hcW hcD).hom.app
        T).snd =
      (frobeniusColimitVectorBundlesPullbackTriangleIso p κV' ιV' cV' hV₂' hV' hX' hcV').hom.app
        T.snd :=
  rfl

/-- The first component of the inverse composition comparison at `T` is the inverse triangle
comparison of the side maps `κW`, `ιW`, `cW` at the first component of `T`. -/
@[simp]
lemma frobeniusColimitVectorBundlesCatPullbackLocComp_inv_app_fst
    (hcV' : κV' ≫ ιV' = cV') (hcW : κW ≫ ιW = cW) (hcD : κD ≫ ιD = cD)
    (T : CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p q hE hX')) :
    ((frobeniusColimitVectorBundlesCatPullbackLocComp p q e qV eV q₂ e₂ ιV' ιW ιD κV' κW κD
      cV' cW cD hX' hZ hE hV' hW hD hV₂' hW₂ hD₂ sq se sq₂ se₂ sqc sec hcV' hcW hcD).inv.app
        T).fst =
      (frobeniusColimitVectorBundlesPullbackTriangleIso p κW ιW cW hW₂ hW hZ hcW).inv.app
        T.fst :=
  rfl

/-- The second component of the inverse composition comparison at `T` is the inverse triangle
comparison of the side maps `κV'`, `ιV'`, `cV'` at the second component of `T`. -/
@[simp]
lemma frobeniusColimitVectorBundlesCatPullbackLocComp_inv_app_snd
    (hcV' : κV' ≫ ιV' = cV') (hcW : κW ≫ ιW = cW) (hcD : κD ≫ ιD = cD)
    (T : CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p q hE hX')) :
    ((frobeniusColimitVectorBundlesCatPullbackLocComp p q e qV eV q₂ e₂ ιV' ιW ιD κV' κW κD
      cV' cW cD hX' hZ hE hV' hW hD hV₂' hW₂ hD₂ sq se sq₂ se₂ sqc sec hcV' hcW hcD).inv.app
        T).snd =
      (frobeniusColimitVectorBundlesPullbackTriangleIso p κV' ιV' cV' hV₂' hV' hX' hcV').inv.app
        T.snd :=
  rfl

end Loc

/-! ### Compatibility with the comparison functors -/

section LocMore
variable {X X' Z E V V' W D V₂ V₂' W₂ D₂ : Scheme.{u}}
  (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
  (bV : V' ⟶ V) (zV : W ⟶ V) (qV : D ⟶ V') (eV : D ⟶ W)
  (b₂ : V₂' ⟶ V₂) (z₂ : W₂ ⟶ V₂) (q₂ : D₂ ⟶ V₂') (e₂ : D₂ ⟶ W₂)
  (ιV : V ⟶ X) (ιV' : V' ⟶ X') (ιW : W ⟶ Z) (ιD : D ⟶ E)
  (κV : V₂ ⟶ V) (κV' : V₂' ⟶ V') (κW : W₂ ⟶ W) (κD : D₂ ⟶ D)
  (cV : V₂ ⟶ X) (cV' : V₂' ⟶ X') (cW : W₂ ⟶ Z) (cD : D₂ ⟶ E)
  (hX : IsInCharacteristic X p)
  (hX' : IsInCharacteristic X' p) (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)
  (hV : IsInCharacteristic V p)
  (hV' : IsInCharacteristic V' p) (hW : IsInCharacteristic W p) (hD : IsInCharacteristic D p)
  (hV₂ : IsInCharacteristic V₂ p)
  (hV₂' : IsInCharacteristic V₂' p) (hW₂ : IsInCharacteristic W₂ p)
  (hD₂ : IsInCharacteristic D₂ p)
  (hw : q ≫ b = e ≫ z) (hwV : qV ≫ bV = eV ≫ zV) (hw₂ : q₂ ≫ b₂ = e₂ ≫ z₂)
  (sb : bV ≫ ιV = ιV' ≫ b) (sz : zV ≫ ιV = ιW ≫ z)
  (sq : qV ≫ ιV' = ιD ≫ q) (se : eV ≫ ιW = ιD ≫ e)
  (sb₂ : b₂ ≫ κV = κV' ≫ bV) (sz₂ : z₂ ≫ κV = κW ≫ zV)
  (sq₂ : q₂ ≫ κV' = κD ≫ qV) (se₂ : e₂ ≫ κW = κD ≫ eV)
  (sbc : b₂ ≫ cV = cV' ≫ b) (szc : z₂ ≫ cV = cW ≫ z)
  (sqc : q₂ ≫ cV' = cD ≫ q) (sec : e₂ ≫ cW = cD ≫ e)
  (hcV : κV ≫ ιV = cV) (hcV' : κV' ≫ ιV' = cV') (hcW : κW ≫ ιW = cW) (hcD : κD ≫ ιD = cD)

/-- **The base-change comparison of the comparison functor is natural in the module.** Both
components are naturality squares of square comparisons. -/
theorem frobeniusColimitVectorBundlesCatPullbackLocIso_naturality
    {M N : frobeniusColimitVectorBundles X p hX} (f : M ⟶ N) :
    (frobeniusColimitVectorBundlesCatPullbackLoc p q e qV eV ιV' ιW ιD
          hX' hZ hE hV' hW hD sq se).map
        ((frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).map f) ≫
      (frobeniusColimitVectorBundlesCatPullbackLocIso p b z q e bV zV qV eV ιV ιV' ιW ιD
        hX hX' hZ hE hV hV' hW hD sq se hw hwV sb sz N).hom =
    (frobeniusColimitVectorBundlesCatPullbackLocIso p b z q e bV zV qV eV ιV ιV' ιW ιD
        hX hX' hZ hE hV hV' hW hD sq se hw hwV sb sz M).hom ≫
      (frobeniusColimitVectorBundlesComparison p bV zV qV eV hV hV' hW hD hwV).map
        ((frobeniusColimitVectorBundlesPullback p ιV hV hX).map f) :=
  CategoricalPullback.hom_ext
    ((frobeniusColimitVectorBundlesSquareIso p ιV z zV ιW hX hV hZ hW sz).hom.naturality f)
    ((frobeniusColimitVectorBundlesSquareIso p ιV b bV ιV' hX hV hX' hV' sb).hom.naturality f)

/-- **The composition comparison of the restriction functors is compatible with the base-change
comparisons of the comparison functor.** Componentwise this is the vertical pasting law
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_vpaste_app` for the two side faces of
the stacked cubes over the centre and over the modification. -/
theorem frobeniusColimitVectorBundlesCatPullbackLocComp_locIso
    (M : frobeniusColimitVectorBundles X p hX) :
    (frobeniusColimitVectorBundlesCatPullbackLocComp p q e qV eV q₂ e₂ ιV' ιW ιD κV' κW κD
        cV' cW cD hX' hZ hE hV' hW hD hV₂' hW₂ hD₂ sq se sq₂ se₂ sqc sec hcV' hcW hcD).hom.app
        ((frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).obj M) ≫
      (frobeniusColimitVectorBundlesCatPullbackLocIso p b z q e b₂ z₂ q₂ e₂ cV cV' cW cD
        hX hX' hZ hE hV₂ hV₂' hW₂ hD₂ sqc sec hw hw₂ sbc szc M).hom =
    (frobeniusColimitVectorBundlesCatPullbackLoc p qV eV q₂ e₂ κV' κW κD
          hV' hW hD hV₂' hW₂ hD₂ sq₂ se₂).map
        (frobeniusColimitVectorBundlesCatPullbackLocIso p b z q e bV zV qV eV ιV ιV' ιW ιD
          hX hX' hZ hE hV hV' hW hD sq se hw hwV sb sz M).hom ≫
      (frobeniusColimitVectorBundlesCatPullbackLocIso p bV zV qV eV b₂ z₂ q₂ e₂ κV κV' κW κD
          hV hV' hW hD hV₂ hV₂' hW₂ hD₂ sq₂ se₂ hwV hw₂ sb₂ sz₂
          ((frobeniusColimitVectorBundlesPullback p ιV hV hX).obj M)).hom ≫
      (frobeniusColimitVectorBundlesComparison p b₂ z₂ q₂ e₂ hV₂ hV₂' hW₂ hD₂ hw₂).map
        ((frobeniusColimitVectorBundlesPullbackTriangleIso p κV ιV cV hV₂ hV hX hcV).hom.app
          M) := by
  refine CategoricalPullback.hom_ext ?_ ?_
  · exact frobeniusColimitVectorBundlesSquareIso_vpaste_app' p z zV z₂ ιV ιW κV κW cV cW hX hZ
      hV hW hV₂ hW₂ sz sz₂ szc hcV hcW M
  · exact frobeniusColimitVectorBundlesSquareIso_vpaste_app' p b bV b₂ ιV ιV' κV κV' cV cV' hX
      hX' hV hV' hV₂ hV₂' sb sb₂ sbc hcV hcV' M

end LocMore

/-! ### The pentagon of the composition comparisons -/

section LocPentagon
variable {X' Z E V' W D V₂' W₂ D₂ V₃' W₃ D₃ : Scheme.{u}}
  (q : E ⟶ X') (e : E ⟶ Z) (qV : D ⟶ V') (eV : D ⟶ W) (q₂ : D₂ ⟶ V₂') (e₂ : D₂ ⟶ W₂)
  (q₃ : D₃ ⟶ V₃') (e₃ : D₃ ⟶ W₃)
  (ιV' : V' ⟶ X') (ιW : W ⟶ Z) (ιD : D ⟶ E)
  (κV' : V₂' ⟶ V') (κW : W₂ ⟶ W) (κD : D₂ ⟶ D)
  (μV' : V₃' ⟶ V₂') (μW : W₃ ⟶ W₂) (μD : D₃ ⟶ D₂)
  (cV' : V₂' ⟶ X') (cW : W₂ ⟶ Z) (cD : D₂ ⟶ E)
  (dV' : V₃' ⟶ V') (dW : W₃ ⟶ W) (dD : D₃ ⟶ D)
  (tV' : V₃' ⟶ X') (tW : W₃ ⟶ Z) (tD : D₃ ⟶ E)
  (hX' : IsInCharacteristic X' p) (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)
  (hV' : IsInCharacteristic V' p) (hW : IsInCharacteristic W p) (hD : IsInCharacteristic D p)
  (hV₂' : IsInCharacteristic V₂' p) (hW₂ : IsInCharacteristic W₂ p)
  (hD₂ : IsInCharacteristic D₂ p)
  (hV₃' : IsInCharacteristic V₃' p) (hW₃ : IsInCharacteristic W₃ p)
  (hD₃ : IsInCharacteristic D₃ p)
  (sq : qV ≫ ιV' = ιD ≫ q) (se : eV ≫ ιW = ιD ≫ e)
  (sq₂ : q₂ ≫ κV' = κD ≫ qV) (se₂ : e₂ ≫ κW = κD ≫ eV)
  (sq₃ : q₃ ≫ μV' = μD ≫ q₂) (se₃ : e₃ ≫ μW = μD ≫ e₂)
  (sqc : q₂ ≫ cV' = cD ≫ q) (sec : e₂ ≫ cW = cD ≫ e)
  (sqd : q₃ ≫ dV' = dD ≫ qV) (sed : e₃ ≫ dW = dD ≫ eV)
  (sqt : q₃ ≫ tV' = tD ≫ q) (set : e₃ ≫ tW = tD ≫ e)
  (hcV' : κV' ≫ ιV' = cV') (hcW : κW ≫ ιW = cW) (hcD : κD ≫ ιD = cD)
  (hdV' : μV' ≫ κV' = dV') (hdW : μW ≫ κW = dW) (hdD : μD ≫ κD = dD)
  (htV' : μV' ≫ cV' = tV') (htW : μW ≫ cW = tW) (htD : μD ≫ cD = tD)
  (htV'' : dV' ≫ ιV' = tV') (htW' : dW ≫ ιW = tW) (htD' : dD ≫ ιD = tD)

/-- **The pentagon of the composition comparisons of the restriction functors.** For three
stacked cubes, the two ways of comparing the three-fold restriction with the restriction along
the composite cube agree. Componentwise this is the pentagon
`AlgebraicGeometry.frobeniusColimitVectorBundlesPullbackTriangleIso_pentagon_app` at the centre
and at the modification. -/
theorem frobeniusColimitVectorBundlesCatPullbackLocComp_pentagon
    (T : CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p q hE hX')) :
    (frobeniusColimitVectorBundlesCatPullbackLoc p q₂ e₂ q₃ e₃ μV' μW μD
          hV₂' hW₂ hD₂ hV₃' hW₃ hD₃ sq₃ se₃).map
        ((frobeniusColimitVectorBundlesCatPullbackLocComp p q e qV eV q₂ e₂ ιV' ιW ιD κV' κW κD
          cV' cW cD hX' hZ hE hV' hW hD hV₂' hW₂ hD₂ sq se sq₂ se₂ sqc sec
          hcV' hcW hcD).hom.app T) ≫
      (frobeniusColimitVectorBundlesCatPullbackLocComp p q e q₂ e₂ q₃ e₃ cV' cW cD μV' μW μD
          tV' tW tD hX' hZ hE hV₂' hW₂ hD₂ hV₃' hW₃ hD₃ sqc sec sq₃ se₃ sqt set
          htV' htW htD).hom.app T =
    (frobeniusColimitVectorBundlesCatPullbackLocComp p qV eV q₂ e₂ q₃ e₃ κV' κW κD μV' μW μD
          dV' dW dD hV' hW hD hV₂' hW₂ hD₂ hV₃' hW₃ hD₃ sq₂ se₂ sq₃ se₃ sqd sed
          hdV' hdW hdD).hom.app
        ((frobeniusColimitVectorBundlesCatPullbackLoc p q e qV eV ιV' ιW ιD
          hX' hZ hE hV' hW hD sq se).obj T) ≫
      (frobeniusColimitVectorBundlesCatPullbackLocComp p q e qV eV q₃ e₃ ιV' ιW ιD dV' dW dD
          tV' tW tD hX' hZ hE hV' hW hD hV₃' hW₃ hD₃ sq se sqd sed sqt set
          htV'' htW' htD').hom.app T :=
  CategoricalPullback.hom_ext
    (frobeniusColimitVectorBundlesPullbackTriangleIso_pentagon_app p μW κW ιW dW cW tW
      hW₃ hW₂ hW hZ hdW hcW htW htW' T.fst).symm
    (frobeniusColimitVectorBundlesPullbackTriangleIso_pentagon_app p μV' κV' ιV' dV' cV' tV'
      hV₃' hV₂' hV' hX' hdV' hcV' htV' htV'' T.snd).symm

end LocPentagon

end AlgebraicGeometry

end
