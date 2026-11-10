module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeHorizontalMate

/-!
# Base change in degree zero for a composite of two morphisms

Consider morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of schemes with named composite `gf : X ⟶ Z`, a
morphism `c : Z' ⟶ Z`, and the two squares
```
X' --e--> X      Y' --d--> Y
|f'       |f     |g'       |g
v         v      v         v
Y' --d--> Y      Z' --c--> Z
```
whose outer rectangle is the square
```
X' --e--> X
|q        |gf
v         v
Z' --c--> Z
```
with `q : X' ⟶ Z'` the named composite of `f'` and `g'`.  This file proves that the **underived**
base change comparison `c⁻¹ (gf)_* ⟶ q_* e⁻¹` of the rectangle is, up to the two isomorphisms
identifying a direct image along a composite with the composite of the direct images, the
composite of the comparison of the lower square at `f_* F` with the direct image under `g'_*` of
the comparison of the upper square at `F`.  Hence it is invertible as soon as those two are.

This is the degree-zero shadow of
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_isIso_of_compDirectImage`, and it is proved
the same way, by the calculus of mates; the point of having it is that the degree-zero comparison
is the one whose invertibility is available unconditionally for a finite morphism
(`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite`) and the one that the
cancellation argument of Tag 0A4C can be run on.

It is not the composition statement of Tag 0EZS, which is already available in degree zero as
`Stacks.EtaleCohomology.etaleAbelianBaseChange_comp_app`: there the pushed-forward morphism is
held fixed and the two *base change* morphisms are composed, so the two squares are stacked in
the other direction and the mates compose vertically rather than horizontally.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianBaseChange_compDirectImage_app` — the composition formula
  for the comparison of the rectangle, at an abelian sheaf.
* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_compDirectImage` — the invertibility
  statement it yields.

## Implementation notes

*Route.*  The base change comparison of a commutative square is the mate, under the two
inverse-image/direct-image adjunctions of the pushed-forward morphisms, of the comparison of the
two composite inverse images around the square
(`Stacks.EtaleCohomology.etaleAbelianBaseChange_eq_mateEquiv`).  Composing the pushed-forward
morphisms therefore means composing the *adjunctions*, and the statement is Mathlib's
`CategoryTheory.mateEquiv_hcomp` — mates turn vertical composition of squares of left adjoints
into horizontal composition of squares of right adjoints — read through
`CategoryTheory.conjugateEquiv_mateEquiv_vcomp` and
`CategoryTheory.mateEquiv_conjugateEquiv_vcomp`, which replace a composite adjunction by an
adjunction of the composite at the cost of the conjugate comparisons.  Those conjugate
comparisons are the direct-image composition isomorphisms, by
`Stacks.EtaleCohomology.conjugateEquiv_etaleAbelianInverseImageCompIso'_hom` and its inverse
half.

The geometric content is therefore entirely the identity
`Stacks.EtaleCohomology.underivedSquare_compDirectImage` of comparisons of inverse images, which
is the associativity pentagon
`Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso'_assoc` for the three chains
`X' ⟶ Y' ⟶ Z' ⟶ Z`, `X' ⟶ Y' ⟶ Y ⟶ Z` and `X' ⟶ X ⟶ Y ⟶ Z`.

*Named composites.*  As in `Stacks.EtaleCohomology.etaleAbelianBaseChange_comp_app`, every
composite of two morphisms of schemes that occurs is carried as a separate morphism together with
equations naming it, so that no comparison has to be transported along `Category.assoc`.

## References

* [Stacks Project, Tag 0A4D](https://stacks.math.columbia.edu/tag/0A4D)
* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

section Whisker

end Whisker

section CompositeSquare

variable {X Y Z X' Y' Z' : Scheme.{u}}

/-- The comparison of the two composite inverse images around a commutative square, with the
common composite `X' ⟶ Y` carried as a named morphism together with the two equations naming it.
This is the 2-square whose mate is the underived base change comparison. -/
private def underivedSquare (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (P : X' ⟶ Y) (hP₁ : P = g' ≫ f) (hP₂ : P = f' ≫ g) :
    TwoSquare (etaleAbelianInverseImage.{u, v} g) (etaleAbelianInverseImage.{u, v} f)
      (etaleAbelianInverseImage.{u, v} f') (etaleAbelianInverseImage.{u, v} g') :=
  TwoSquare.mk _ _ _ _
    ((etaleAbelianInverseImageCompIso'.{u, v} f' g P hP₂).inv ≫
      (etaleAbelianInverseImageCompIso'.{u, v} g' f P hP₁).hom)

/-- The base change comparison of a square is the mate of its `underivedSquare`. -/
private theorem etaleAbelianBaseChange_eq_mateEquiv_underivedSquare
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (hyp : g' ≫ f = f' ≫ g)
    (P : X' ⟶ Y) (hP₁ : P = g' ≫ f) (hP₂ : P = f' ≫ g) :
    etaleAbelianBaseChange.{u, v} f g g' f' hyp =
      mateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
        (etaleAbelianInverseImageDirectImageAdj.{u, v} f')
        (underivedSquare.{u, v} f g g' f' P hP₁ hP₂) :=
  etaleAbelianBaseChange_eq_mateEquiv.{u, v} f g g' f' hyp P hP₁ hP₂

/-- **The comparison of composite inverse images around the outer rectangle is the vertical
composite of the comparisons of the two squares**, whiskered with the comparisons identifying the
inverse image along a composite — stated as an equation between natural transformations, with
every whiskering and every associator written out.

This is the associativity pentagon
`Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso'_assoc` for the three chains
`X' ⟶ Y' ⟶ Z' ⟶ Z`, `X' ⟶ Y' ⟶ Y ⟶ Z` and `X' ⟶ X ⟶ Y ⟶ Z`; the two comparisons attached to the
middle vertices `Y' ⟶ Z` and `X' ⟶ Y` cancel between consecutive instances.  Nothing is assumed
of the squares beyond commutativity. -/
private theorem underivedSquare_compDirectImage_natTrans
    (f : X ⟶ Y) (g : Y ⟶ Z) (gf : X ⟶ Z) (hgf : gf = f ≫ g)
    (c : Z' ⟶ Z) (d : Y' ⟶ Y) (g' : Y' ⟶ Z') (e : X' ⟶ X) (f' : X' ⟶ Y')
    (q : X' ⟶ Z') (hq : q = f' ≫ g')
    (P₁ : Y' ⟶ Z) (hP₁d : P₁ = d ≫ g) (hP₁g' : P₁ = g' ≫ c)
    (P₂ : X' ⟶ Y) (hP₂e : P₂ = e ≫ f) (hP₂f' : P₂ = f' ≫ d)
    (P : X' ⟶ Z) (hPe : P = e ≫ gf) (hPq : P = q ≫ c)
    (hPf' : P = f' ≫ P₁) (hPg : P = P₂ ≫ g) :
    (etaleAbelianInverseImageCompIso'.{u, v} q c P hPq).inv ≫
        (etaleAbelianInverseImageCompIso'.{u, v} e gf P hPe).hom =
      (Functor.whiskerLeft (etaleAbelianInverseImage.{u, v} c)
            (etaleAbelianInverseImageCompIso'.{u, v} f' g' q hq).hom ≫
        ((Functor.associator (etaleAbelianInverseImage.{u, v} c)
                (etaleAbelianInverseImage.{u, v} g')
                (etaleAbelianInverseImage.{u, v} f')).inv ≫
            Functor.whiskerRight
                ((etaleAbelianInverseImageCompIso'.{u, v} g' c P₁ hP₁g').inv ≫
                  (etaleAbelianInverseImageCompIso'.{u, v} d g P₁ hP₁d).hom)
                (etaleAbelianInverseImage.{u, v} f') ≫
              (Functor.associator (etaleAbelianInverseImage.{u, v} g)
                  (etaleAbelianInverseImage.{u, v} d)
                  (etaleAbelianInverseImage.{u, v} f')).hom ≫
                Functor.whiskerLeft (etaleAbelianInverseImage.{u, v} g)
                    ((etaleAbelianInverseImageCompIso'.{u, v} f' d P₂ hP₂f').inv ≫
                      (etaleAbelianInverseImageCompIso'.{u, v} e f P₂ hP₂e).hom) ≫
                  (Functor.associator (etaleAbelianInverseImage.{u, v} g)
                    (etaleAbelianInverseImage.{u, v} f)
                    (etaleAbelianInverseImage.{u, v} e)).inv)) ≫
          Functor.whiskerRight
            (etaleAbelianInverseImageCompIso'.{u, v} f g gf hgf).inv
            (etaleAbelianInverseImage.{u, v} e) := by
  have hIh := congrArg Iso.hom
    (etaleAbelianInverseImageCompIso'_assoc.{u, v} c g' f' P₁ hP₁g' q hq P hPq hPf')
  have hIIh := congrArg Iso.hom
    (etaleAbelianInverseImageCompIso'_assoc.{u, v} g d f' P₁ hP₁d P₂ hP₂f' P hPg hPf')
  have hIIIh := congrArg Iso.hom
    (etaleAbelianInverseImageCompIso'_assoc.{u, v} g f e gf hgf P₂ hP₂e P hPg hPe)
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom] at hIh hIIh hIIIh
  have hstep : (Functor.associator (etaleAbelianInverseImage.{u, v} g)
          (etaleAbelianInverseImage.{u, v} f)
          (etaleAbelianInverseImage.{u, v} e)).inv ≫
        Functor.whiskerRight
          (etaleAbelianInverseImageCompIso'.{u, v} f g gf hgf).inv
          (etaleAbelianInverseImage.{u, v} e) =
      (Functor.whiskerLeft (etaleAbelianInverseImage.{u, v} g)
            (etaleAbelianInverseImageCompIso'.{u, v} e f P₂ hP₂e).inv ≫
          (etaleAbelianInverseImageCompIso'.{u, v} P₂ g P hPg).inv) ≫
        (etaleAbelianInverseImageCompIso'.{u, v} e gf P hPe).hom := by
    rw [← Iso.comp_inv_eq, Category.assoc]
    exact hIIIh.symm
  have hcancel : Functor.whiskerLeft (etaleAbelianInverseImage.{u, v} g)
          (etaleAbelianInverseImageCompIso'.{u, v} e f P₂ hP₂e).hom ≫
        (Functor.associator (etaleAbelianInverseImage.{u, v} g)
            (etaleAbelianInverseImage.{u, v} f)
            (etaleAbelianInverseImage.{u, v} e)).inv ≫
          Functor.whiskerRight
            (etaleAbelianInverseImageCompIso'.{u, v} f g gf hgf).inv
            (etaleAbelianInverseImage.{u, v} e) =
      (etaleAbelianInverseImageCompIso'.{u, v} P₂ g P hPg).inv ≫
        (etaleAbelianInverseImageCompIso'.{u, v} e gf P hPe).hom := by
    rw [hstep]
    simp only [Category.assoc]
    exact whiskerLeft_hom_inv_id_assoc (etaleAbelianInverseImage.{u, v} g)
      (etaleAbelianInverseImageCompIso'.{u, v} e f P₂ hP₂e) _
  simp only [Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc]
  rw [hcancel, reassoc_of% hIIh, Iso.hom_inv_id_assoc, whiskerRight_hom_inv_id_assoc,
    ← reassoc_of% hIh]
  exact (whiskerLeft_hom_inv_id_assoc (etaleAbelianInverseImage.{u, v} c)
    (etaleAbelianInverseImageCompIso'.{u, v} f' g' q hq) _).symm

/-- **The comparison of composite inverse images around the outer rectangle is the vertical
composite of the comparisons of the two squares**, as an identity of 2-squares. -/
private theorem underivedSquare_compDirectImage
    (f : X ⟶ Y) (g : Y ⟶ Z) (gf : X ⟶ Z) (hgf : gf = f ≫ g)
    (c : Z' ⟶ Z) (d : Y' ⟶ Y) (g' : Y' ⟶ Z') (e : X' ⟶ X) (f' : X' ⟶ Y')
    (q : X' ⟶ Z') (hq : q = f' ≫ g')
    (P₁ : Y' ⟶ Z) (hP₁d : P₁ = d ≫ g) (hP₁g' : P₁ = g' ≫ c)
    (P₂ : X' ⟶ Y) (hP₂e : P₂ = e ≫ f) (hP₂f' : P₂ = f' ≫ d)
    (P : X' ⟶ Z) (hPe : P = e ≫ gf) (hPq : P = q ≫ c)
    (hPf' : P = f' ≫ P₁) (hPg : P = P₂ ≫ g) :
    underivedSquare.{u, v} gf c e q P hPe hPq =
      ((TwoSquare.vComp (underivedSquare.{u, v} g c d g' P₁ hP₁d hP₁g')
            (underivedSquare.{u, v} f d e f' P₂ hP₂e hP₂f')).whiskerRight
          (etaleAbelianInverseImageCompIso'.{u, v} f' g' q hq).hom).whiskerLeft
        (etaleAbelianInverseImageCompIso'.{u, v} f g gf hgf).inv := by
  refine NatTrans.ext (funext fun W => ?_)
  exact NatTrans.congr_app
    (underivedSquare_compDirectImage_natTrans.{u, v} f g gf hgf c d g' e f' q hq P₁ hP₁d hP₁g'
      P₂ hP₂e hP₂f' P hPe hPq hPf' hPg) W

end CompositeSquare

section Main

variable {X Y Z X' Y' Z' : Scheme.{u}}

/-- **The underived base change comparison of the outer rectangle, as a composite.**  For
morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` with named composite `gf`, a morphism `c : Z' ⟶ Z`, and
commutative squares `d ≫ g = g' ≫ c` and `e ≫ f = f' ≫ d`, the comparison
`c⁻¹ (gf)_* F ⟶ q_* e⁻¹ F` of the outer rectangle is the comparison of the lower square at
`f_* F`, followed by `g'_*` of the comparison of the upper square at `F`, read through the two
comparisons identifying a direct image along a composite with the composite of the direct
images.

Nothing is assumed of the two squares beyond commutativity: neither need be cartesian, and no
properness enters. -/
public theorem etaleAbelianBaseChange_compDirectImage_app
    (f : X ⟶ Y) (g : Y ⟶ Z) (gf : X ⟶ Z) (hgf : gf = f ≫ g)
    (c : Z' ⟶ Z) (d : Y' ⟶ Y) (g' : Y' ⟶ Z') (e : X' ⟶ X) (f' : X' ⟶ Y')
    (q : X' ⟶ Z') (hq : q = f' ≫ g')
    (sq₁ : d ≫ g = g' ≫ c) (sq₂ : e ≫ f = f' ≫ d) (hyp : e ≫ gf = q ≫ c)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianBaseChange.{u, v} gf c e q hyp).app F =
      (etaleAbelianInverseImage.{u, v} c).map
          ((etaleAbelianDirectImageCompIso'.{u, v} f g gf hgf).inv.app F) ≫
        (etaleAbelianBaseChange.{u, v} g c d g' sq₁).app
            ((etaleAbelianDirectImage.{u, v} f).obj F) ≫
          (etaleAbelianDirectImage.{u, v} g').map
              ((etaleAbelianBaseChange.{u, v} f d e f' sq₂).app F) ≫
            (etaleAbelianDirectImageCompIso'.{u, v} f' g' q hq).hom.app
              ((etaleAbelianInverseImage.{u, v} e).obj F) := by
  have hPf' : (e ≫ gf : X' ⟶ Z) = f' ≫ d ≫ g := by
    rw [hgf, ← Category.assoc, sq₂, Category.assoc]
  have hPg : (e ≫ gf : X' ⟶ Z) = (e ≫ f) ≫ g := by rw [hgf, Category.assoc]
  have hsq : underivedSquare.{u, v} gf c e q (e ≫ gf) rfl hyp =
      ((TwoSquare.vComp
              (underivedSquare.{u, v} g c d g' (d ≫ g) rfl sq₁)
              (underivedSquare.{u, v} f d e f' (e ≫ f) rfl sq₂)).whiskerRight
          (etaleAbelianInverseImageCompIso'.{u, v} f' g' q hq).hom).whiskerLeft
        (etaleAbelianInverseImageCompIso'.{u, v} f g gf hgf).inv :=
    underivedSquare_compDirectImage.{u, v} f g gf hgf c d g' e f' q hq (d ≫ g) rfl sq₁
      (e ≫ f) rfl sq₂ (e ≫ gf) rfl hyp hPf' hPg
  rw [etaleAbelianBaseChange_eq_mateEquiv_underivedSquare.{u, v} gf c e q hyp (e ≫ gf) rfl hyp,
    etaleAbelianBaseChange_eq_mateEquiv_underivedSquare.{u, v} g c d g' sq₁ (d ≫ g) rfl sq₁,
    etaleAbelianBaseChange_eq_mateEquiv_underivedSquare.{u, v} f d e f' sq₂ (e ≫ f) rfl sq₂,
    hsq, conjugateEquiv_mateEquiv_vcomp (etaleAbelianInverseImageDirectImageAdj.{u, v} gf)
      ((etaleAbelianInverseImageDirectImageAdj.{u, v} g).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, v} f))
      (etaleAbelianInverseImageDirectImageAdj.{u, v} q),
    mateEquiv_conjugateEquiv_vcomp
      ((etaleAbelianInverseImageDirectImageAdj.{u, v} g).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, v} f))
      ((etaleAbelianInverseImageDirectImageAdj.{u, v} g').comp
        (etaleAbelianInverseImageDirectImageAdj.{u, v} f'))
      (etaleAbelianInverseImageDirectImageAdj.{u, v} q),
    mateEquiv_hcomp (etaleAbelianInverseImageDirectImageAdj.{u, v} g)
      (etaleAbelianInverseImageDirectImageAdj.{u, v} g')
      (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
      (etaleAbelianInverseImageDirectImageAdj.{u, v} f'),
    ← conjugateEquiv_etaleAbelianInverseImageCompIso'_inv.{u, v} f g gf hgf,
    ← conjugateEquiv_etaleAbelianInverseImageCompIso'_hom.{u, v} f' g' q hq]
  simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp]

/-- **The composition statement for the underived base change comparison.**  Let `f : X ⟶ Y` and
`g : Y ⟶ Z` be morphisms of schemes with named composite `gf : X ⟶ Z`, let `c : Z' ⟶ Z`, and
consider commutative squares
```
X' --e--> X      Y' --d--> Y
|f'       |f     |g'       |g
v         v      v         v
Y' --d--> Y      Z' --c--> Z
```
with `q : X' ⟶ Z'` the named composite of `f'` and `g'`.  Let `F` be an abelian sheaf on
`X_étale`.  If the comparison `c⁻¹ g_* ⟶ g'_* d⁻¹` of the lower square is an isomorphism at
`f_* F`, and the comparison `d⁻¹ f_* ⟶ f'_* e⁻¹` of the upper square is an isomorphism at `F`,
then the comparison `c⁻¹ (gf)_* F ⟶ q_* e⁻¹ F` of the outer rectangle is an isomorphism.

It is formal, by `Stacks.EtaleCohomology.etaleAbelianBaseChange_compDirectImage_app`, which
exhibits the comparison of the rectangle as the composite of the two given maps with two
isomorphisms; neither square need be cartesian and neither morphism need be proper. -/
public theorem isIso_etaleAbelianBaseChange_of_compDirectImage
    (f : X ⟶ Y) (g : Y ⟶ Z) (gf : X ⟶ Z) (hgf : gf = f ≫ g)
    (c : Z' ⟶ Z) (d : Y' ⟶ Y) (g' : Y' ⟶ Z') (e : X' ⟶ X) (f' : X' ⟶ Y')
    (q : X' ⟶ Z') (hq : q = f' ≫ g')
    (sq₁ : d ≫ g = g' ≫ c) (sq₂ : e ≫ f = f' ≫ d) (hyp : e ≫ gf = q ≫ c)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (h₁ : IsIso ((etaleAbelianBaseChange.{u, v} g c d g' sq₁).app
      ((etaleAbelianDirectImage.{u, v} f).obj F)))
    (h₂ : IsIso ((etaleAbelianBaseChange.{u, v} f d e f' sq₂).app F)) :
    IsIso ((etaleAbelianBaseChange.{u, v} gf c e q hyp).app F) := by
  rw [etaleAbelianBaseChange_compDirectImage_app.{u, v} f g gf hgf c d g' e f' q hq
    sq₁ sq₂ hyp F]
  infer_instance

end Main

end Stacks.EtaleCohomology

end
