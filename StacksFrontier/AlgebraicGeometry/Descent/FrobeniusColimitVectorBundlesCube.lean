module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitSquarePaste

/-!
# The pasting law and the cube coherence on the finite locally free modules

Let `p` be a prime. `StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitSquarePaste` proves the
pasting law and the cube coherence of the square comparisons **on all sheaves of modules** over the
Frobenius colimits of the structure sheaves, and the pasting law also on the finite locally free
ones. This file carries the remaining statements to the finite locally free modules, which are the
fibre categories of the category fibred in groupoids of [Stacks, Tag 0EXE] and the categories the
comparison functor of [Stacks, Tag 0EXD] is a functor between.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitVectorBundlesPullbackTriangleIso`: the comparison of the two
  transition functors attached to a commuting triangle of schemes, with the composite kept as a
  variable subject to an equation.

## Main results

* `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_paste_app`: **the pasting law on an
  object**, on the finite locally free modules.
* `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_cube_app`: **the cube coherence** on
  the finite locally free modules.

## Implementation notes

**The cube is proved natively at this level, not transported.** The module-level cube
`AlgebraicGeometry.frobeniusColimitPullbackSquareIso_cube_app` does imply this one — a morphism of
the full subcategory of finite locally free modules is determined by the morphism of sheaves of
modules underlying it, so the two statements are interchangeable — but the proof term obtained by
transporting it is too large: the kernel times out on it, even though elaboration succeeds. That is
not an elaboration problem and no tactic choice fixes it. What fixes it is proving the *pasting
law* at this level, where the transport is small, and then running the cube's own argument — the
pasting law read twice at one and the same rectangle — natively over the finite locally free
modules.

**Why the triangle comparison keeps its composite as a variable.** Exactly as for
`AlgebraicGeometry.frobeniusColimitPullbackTriangleIso`: a consumer instantiates the comparison at
whichever morphism its diagram actually names and supplies the equation, instead of having to
produce a diagram in which every composite is literal. This is what makes the cube a transitivity
of two instances of one pasting law.

**The shape of the cube's statement is the point.** Six square comparisons appear, one per face of
the cube, and six transition functors; no comparison for a composite survives and the two diagonals
cancel. Its only hypotheses are the two squares' commutativities and the four side faces'. In
particular the statement contains **no `CategoryTheory.eqToIso`, no `CategoryTheory.eqToHom` and no
open of a scheme at all**: at the square of Example 0EVH over a basic open of the base the fourth
corner of the top face is `e ⁻¹ᵁ (z ⁻¹ᵁ D(g))` read one way and `q ⁻¹ᵁ (b ⁻¹ᵁ D(g))` read the
other, and those two opens are equal only by transport along the bottom square's commutativity. A
statement that *computed* the top face from the bottom one would carry that transport inside its
type, where no rewrite reaches it; here the consumer picks one of the two and supplies the four
side commutativities as ordinary equations between morphisms of schemes.

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

/-! ### The triangle comparison on the finite locally free modules -/

section Triangle

variable {Q R S T : Scheme.{u}}

/-- **The comparison of the two transition functors attached to a commuting triangle of
schemes**, on the finite locally free modules over the Frobenius colimits. -/
noncomputable def frobeniusColimitVectorBundlesPullbackTriangleIso (f : R ⟶ S) (g : S ⟶ T)
    (fg : R ⟶ T) (hR : IsInCharacteristic R p) (hS : IsInCharacteristic S p)
    (hT : IsInCharacteristic T p) (w : f ≫ g = fg) :
    frobeniusColimitVectorBundlesPullback p g hS hT ⋙
        frobeniusColimitVectorBundlesPullback p f hR hS ≅
      frobeniusColimitVectorBundlesPullback p fg hR hT :=
  frobeniusColimitVectorBundlesPullbackComp p f g hR hS hT ≪≫
    eqToIso (congrArg (fun m : R ⟶ T =>
      frobeniusColimitVectorBundlesPullback p m hR hT) w)

/-- At the literal composite the triangle comparison is the composition comparison. -/
@[simp]
lemma frobeniusColimitVectorBundlesPullbackTriangleIso_rfl (f : R ⟶ S) (g : S ⟶ T)
    (hR : IsInCharacteristic R p) (hS : IsInCharacteristic S p)
    (hT : IsInCharacteristic T p) :
    frobeniusColimitVectorBundlesPullbackTriangleIso p f g (f ≫ g) hR hS hT rfl =
      frobeniusColimitVectorBundlesPullbackComp p f g hR hS hT := by
  simp only [frobeniusColimitVectorBundlesPullbackTriangleIso]
  exact Iso.trans_refl _

/-- The triangle comparison on the finite locally free modules, read on the underlying sheaves of
modules, is the triangle comparison on all sheaves of modules. -/
theorem frobeniusColimitVectorBundlesPullbackTriangleIso_hom_app_hom (f : R ⟶ S) (g : S ⟶ T)
    (fg : R ⟶ T) (hR : IsInCharacteristic R p) (hS : IsInCharacteristic S p)
    (hT : IsInCharacteristic T p) (w : f ≫ g = fg)
    (M : frobeniusColimitVectorBundles T p hT) :
    ((frobeniusColimitVectorBundlesPullbackTriangleIso p f g fg hR hS hT w).hom.app M).hom =
      (frobeniusColimitPullbackTriangleIso p f g fg hR hS hT w).hom.app M.obj := by
  subst w
  rw [frobeniusColimitVectorBundlesPullbackTriangleIso_rfl,
    frobeniusColimitPullbackTriangleIso_rfl,
    frobeniusColimitVectorBundlesPullbackComp_hom_app_hom]

end Triangle

/-! ### Pasting two commutative squares, on the finite locally free modules -/

section Paste

variable {X Y Z X' Y' Z' : Scheme.{u}}

/-- **The comparison attached to a horizontal pasting of two commutative squares of schemes is the
pasting of the two comparisons, on the finite locally free modules**, stated on an object. -/
theorem frobeniusColimitVectorBundlesSquareIso_paste_app (g : X ⟶ Y) (h : Y ⟶ Z) (k : X ⟶ X')
    (l : Y ⟶ Y') (m : Z ⟶ Z') (g' : X' ⟶ Y') (h' : Y' ⟶ Z')
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (hZ : IsInCharacteristic Z p)
    (hX' : IsInCharacteristic X' p) (hY' : IsInCharacteristic Y' p)
    (hZ' : IsInCharacteristic Z' p)
    (w₁ : g ≫ l = k ≫ g') (w₂ : h ≫ m = l ≫ h')
    (gh : X ⟶ Z) (wgh : g ≫ h = gh) (g'h' : X' ⟶ Z') (wg'h' : g' ≫ h' = g'h')
    (w : gh ≫ m = k ≫ g'h')
    (M : frobeniusColimitVectorBundles Z' p hZ') :
    (frobeniusColimitVectorBundlesPullbackTriangleIso p g h gh hX hY hZ wgh).hom.app
          ((frobeniusColimitVectorBundlesPullback p m hZ hZ').obj M) ≫
        (frobeniusColimitVectorBundlesSquareIso p g'h' m k gh
          hZ' hX' hZ hX w.symm).hom.app M =
      (frobeniusColimitVectorBundlesPullback p g hX hY).map
          ((frobeniusColimitVectorBundlesSquareIso p h' m l h
            hZ' hY' hZ hY w₂.symm).hom.app M) ≫
        (frobeniusColimitVectorBundlesSquareIso p g' l k g hY' hX' hY hX w₁.symm).hom.app
            ((frobeniusColimitVectorBundlesPullback p h' hY' hZ').obj M) ≫
          (frobeniusColimitVectorBundlesPullback p k hX hX').map
            ((frobeniusColimitVectorBundlesPullbackTriangleIso p g' h' g'h'
              hX' hY' hZ' wg'h').hom.app M) := by
  refine ObjectProperty.hom_ext _ ?_
  have H := frobeniusColimitPullbackSquareIso_paste_app p g h k l m g' h'
    hX hY hZ hX' hY' hZ' w₁ w₂ gh wgh g'h' wg'h' w M.obj
  simpa [frobeniusColimitVectorBundlesPullbackTriangleIso_hom_app_hom,
    frobeniusColimitVectorBundlesSquareIso_hom_app_hom] using H

end Paste

/-! ### The cube coherence on the finite locally free modules -/

section Cube

variable {R S₁ S₂ T : Scheme.{u}}

/-- **Two factorisations of one morphism differ by the square comparison of the square they
span**, on the finite locally free modules. -/
lemma frobeniusColimitVectorBundlesSquareIso_hom_app_comp_triangleIso (f₁ : R ⟶ S₁) (g₁ : S₁ ⟶ T)
    (f₂ : R ⟶ S₂) (g₂ : S₂ ⟶ T) (hR : IsInCharacteristic R p)
    (hS₁ : IsInCharacteristic S₁ p) (hS₂ : IsInCharacteristic S₂ p)
    (hT : IsInCharacteristic T p) (sq : f₁ ≫ g₁ = f₂ ≫ g₂) (fg : R ⟶ T)
    (hfg : f₁ ≫ g₁ = fg) (N : frobeniusColimitVectorBundles T p hT) :
    (frobeniusColimitVectorBundlesSquareIso p g₁ g₂ f₁ f₂ hT hS₁ hS₂ hR sq).hom.app N ≫
        (frobeniusColimitVectorBundlesPullbackTriangleIso p f₁ g₁ fg
          hR hS₁ hT hfg).hom.app N =
      (frobeniusColimitVectorBundlesPullbackTriangleIso p f₂ g₂ fg hR hS₂ hT
        (sq.symm.trans hfg)).hom.app N := by
  refine ObjectProperty.hom_ext _ ?_
  have H := frobeniusColimitPullbackSquareIso_hom_app_comp_triangleIso p f₁ g₁ f₂ g₂
    hR hS₁ hS₂ hT sq fg hfg N.obj
  simpa [frobeniusColimitVectorBundlesPullbackTriangleIso_hom_app_hom,
    frobeniusColimitVectorBundlesSquareIso_hom_app_hom] using H

end Cube

section CubeFaces

variable {X X' Z E V V' W D : Scheme.{u}}

/-- **The cube coherence of the square comparisons, on the finite locally free modules over the
Frobenius colimits.**  Given two commutative squares of schemes in characteristic `p` — a
"bottom" one `q ≫ b = e ≫ z` with corners `X`, `X'`, `Z`, `E`, and a "top" one
`qV ≫ bV = eV ≫ zV` with corners `V`, `V'`, `W`, `D` — together with four vertical morphisms
making the four side faces commute, the two routes around the cube agree.

This is the form the trivialising-cover step of [Stacks, Tag 0EXD] needs, since the comparison
functor of that tag is built from `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso` and
not from its module-level underlying comparison. It is proved **natively** at this level, from the
pasting law `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_paste_app` read twice at one
and the same rectangle, and not by transporting the module-level cube
`AlgebraicGeometry.frobeniusColimitPullbackSquareIso_cube_app`: that transport is semantically
right but its proof term is too large for the kernel. -/
theorem frobeniusColimitVectorBundlesSquareIso_cube_app
    (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
    (bV : V' ⟶ V) (zV : W ⟶ V) (qV : D ⟶ V') (eV : D ⟶ W)
    (ιV : V ⟶ X) (ιV' : V' ⟶ X') (ιW : W ⟶ Z) (ιD : D ⟶ E)
    (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
    (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)
    (hV : IsInCharacteristic V p) (hV' : IsInCharacteristic V' p)
    (hW : IsInCharacteristic W p) (hD : IsInCharacteristic D p)
    (hw : q ≫ b = e ≫ z) (hwV : qV ≫ bV = eV ≫ zV)
    (sb : bV ≫ ιV = ιV' ≫ b) (sz : zV ≫ ιV = ιW ≫ z)
    (sq : qV ≫ ιV' = ιD ≫ q) (se : eV ≫ ιW = ιD ≫ e)
    (M : frobeniusColimitVectorBundles X p hX) :
    (frobeniusColimitVectorBundlesSquareIso p ιV' q qV ιD hX' hV' hE hD sq).hom.app
          ((frobeniusColimitVectorBundlesPullback p b hX' hX).obj M) ≫
        (frobeniusColimitVectorBundlesPullback p qV hD hV').map
            ((frobeniusColimitVectorBundlesSquareIso p ιV b bV ιV'
              hX hV hX' hV' sb).hom.app M) ≫
          (frobeniusColimitVectorBundlesSquareIso p zV bV eV qV
              hV hW hV' hD hwV.symm).hom.app
            ((frobeniusColimitVectorBundlesPullback p ιV hV hX).obj M) =
      (frobeniusColimitVectorBundlesPullback p ιD hD hE).map
          ((frobeniusColimitVectorBundlesSquareIso p z b e q
            hX hZ hX' hE hw.symm).hom.app M) ≫
        (frobeniusColimitVectorBundlesSquareIso p ιW e eV ιD hZ hW hE hD se).hom.app
            ((frobeniusColimitVectorBundlesPullback p z hZ hX).obj M) ≫
          (frobeniusColimitVectorBundlesPullback p eV hD hW).map
            ((frobeniusColimitVectorBundlesSquareIso p ιV z zV ιW
              hX hV hZ hW sz).hom.app M) := by
  have hcube : (qV ≫ ιV') ≫ b = eV ≫ zV ≫ ιV := by
    rw [Category.assoc, ← sb, ← Category.assoc, hwV, Category.assoc]
  have h1 := frobeniusColimitVectorBundlesSquareIso_paste_app p qV ιV' eV bV b zV ιV
    hD hV' hX' hW hV hX hwV sb.symm (qV ≫ ιV') rfl (zV ≫ ιV) rfl hcube M
  have h2 := frobeniusColimitVectorBundlesSquareIso_paste_app p ιD q eV e b ιW z
    hD hE hX' hW hZ hX se.symm hw (qV ≫ ιV') (sq.symm.trans rfl)
    (zV ≫ ιV) (sz.symm.trans rfl) hcube M
  have h3 := frobeniusColimitVectorBundlesSquareIso_hom_app_comp_triangleIso p qV ιV' ιD q
    hD hV' hE hX' sq (qV ≫ ιV') rfl
    ((frobeniusColimitVectorBundlesPullback p b hX' hX).obj M)
  have h4 := frobeniusColimitVectorBundlesSquareIso_hom_app_comp_triangleIso p zV ιV ιW z
    hW hV hZ hX sz (zV ≫ ιV) rfl M
  simp only [frobeniusColimitVectorBundlesPullbackTriangleIso_rfl] at h1 h2 h3 h4
  have hiso : IsIso ((frobeniusColimitVectorBundlesPullback p eV hD hW).map
      ((frobeniusColimitVectorBundlesPullbackComp p zV ιV hW hV hX).hom.app M)) :=
    inferInstance
  apply (cancel_mono ((frobeniusColimitVectorBundlesPullback p eV hD hW).map
    ((frobeniusColimitVectorBundlesPullbackComp p zV ιV hW hV hX).hom.app M))).mp
  simp only [Category.assoc]
  rw [← Functor.map_comp, h4, ← h2, ← h3, Category.assoc, h1]

end CubeFaces

end AlgebraicGeometry

end
