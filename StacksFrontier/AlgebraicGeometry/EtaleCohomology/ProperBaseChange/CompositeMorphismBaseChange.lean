module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMate
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change for a composite of two morphisms

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
with `q : X' ⟶ Z'` the named composite of `f'` and `g'`.  This file proves that the derived base
change map `c⁻¹ R(gf)_* ⟶ Rq_* e⁻¹` of the rectangle is, up to the two isomorphisms identifying
a derived direct image along a composite with the composite of the derived direct images, the
composite of the base change map of the lower square at `Rf_* K` with the direct image under
`Rg'_*` of the base change map of the upper square at `K`.  Hence it is invertible as soon as
those two are.

This is the composition statement in the direction of the **pushed-forward** morphism.  It is
not the composition statement of Tag 0EZS, which is already available as
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_isIso_of_comp`: there the pushed-forward
morphism is held fixed and the two *base change* morphisms are composed, so the two squares are
stacked in the other direction and the mates compose vertically rather than horizontally.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianDerivedDirectImageCompIso'` — the composition isomorphism
  `R(gf)_* ≅ Rf_* ⋙ Rg_*` for derived direct image, with the composite carried as a named
  morphism together with an equation naming it.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_compDirectImage_app` — the composition
  formula for the base change map of the rectangle, at an object of the derived category.
* `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_isIso_of_compDirectImage` — the
  invertibility statement it yields.

## Implementation notes

*The derived direct image comparison.*  `Rf_* ⋙ Rg_*` and `R(gf)_*` are both right adjoint to a
functor isomorphic to `(gf)⁻¹`, the comparison of the left adjoints being
`Stacks.EtaleCohomology.etaleAbelianDerivedInverseImageCompIso'`, so the comparison of the right
adjoints is its conjugate, `CategoryTheory.conjugateIsoEquiv`.  No Leray acyclicity and no
K-injective bookkeeping is needed for this: it is the uniqueness of a right adjoint.

*Route.*  The base change map of a commutative square is the mate, under the two derived
inverse-image/direct-image adjunctions of the pushed-forward morphisms, of the comparison of the
two composite derived inverse images around the square
(`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_eq_mateEquiv`).  Composing the
pushed-forward morphisms therefore means composing the *adjunctions*, and the statement is
Mathlib's `CategoryTheory.mateEquiv_hcomp` — mates turn vertical composition of squares of left
adjoints into horizontal composition of squares of right adjoints — read through
`CategoryTheory.conjugateEquiv_mateEquiv_vcomp` and
`CategoryTheory.mateEquiv_conjugateEquiv_vcomp`, which replace a composite adjunction by an
adjunction of the composite at the cost of the conjugate comparisons.

The geometric content is therefore entirely the identity
`Stacks.EtaleCohomology.derivedSquare_compDirectImage` of comparisons of derived inverse images,
which is the associativity pentagon
`Stacks.EtaleCohomology.etaleAbelianDerivedInverseImageCompIso'_assoc` for the three chains
`X' ⟶ Y' ⟶ Z' ⟶ Z`, `X' ⟶ Y' ⟶ Y ⟶ Z` and `X' ⟶ X ⟶ Y ⟶ Z`.

*Named composites.*  As in
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_comp_app`, every composite of two
morphisms of schemes that occurs is carried as a separate morphism together with equations
naming it, so that no comparison has to be transported along `Category.assoc`.

## References

* [Stacks Project, Tag 0A4D](https://stacks.math.columbia.edu/tag/0A4D)
* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

section DirectImageCompIso

variable {X Y Z : Scheme.{u}}

/-- **The composition isomorphism `R(fg)_* ≅ Rf_* ⋙ Rg_*` for derived direct image** of abelian
sheaves on the small étale sites, with the composite `fg` carried as a named morphism together
with an equation naming it.

Both functors are right adjoint to a functor isomorphic to `(fg)⁻¹` — the comparison of the left
adjoints being `Stacks.EtaleCohomology.etaleAbelianDerivedInverseImageCompIso'` — so this is the
conjugate of that comparison under the adjunctions. -/
@[sga "4½ Th_finitude 1.3" "partial"]
public def etaleAbelianDerivedDirectImageCompIso' (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    etaleAbelianDerivedDirectImage.{u, v} fg ≅
      etaleAbelianDerivedDirectImage.{u, v} f ⋙ etaleAbelianDerivedDirectImage.{u, v} g :=
  conjugateIsoEquiv (etaleAbelianDerivedAdjunction.{u, v} fg)
    ((etaleAbelianDerivedAdjunction.{u, v} g).comp (etaleAbelianDerivedAdjunction.{u, v} f))
    (etaleAbelianDerivedInverseImageCompIso'.{u, v} f g fg hfg).symm

/-- The forward direction of the derived direct image comparison is the conjugate of the inverse
of the derived inverse image comparison. -/
private theorem etaleAbelianDerivedDirectImageCompIso'_hom (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    (etaleAbelianDerivedDirectImageCompIso'.{u, v} f g fg hfg).hom =
      conjugateEquiv (etaleAbelianDerivedAdjunction.{u, v} fg)
        ((etaleAbelianDerivedAdjunction.{u, v} g).comp
          (etaleAbelianDerivedAdjunction.{u, v} f))
        (etaleAbelianDerivedInverseImageCompIso'.{u, v} f g fg hfg).inv :=
  rfl

/-- The backward direction of the derived direct image comparison is the conjugate of the
derived inverse image comparison. -/
private theorem etaleAbelianDerivedDirectImageCompIso'_inv (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    (etaleAbelianDerivedDirectImageCompIso'.{u, v} f g fg hfg).inv =
      conjugateEquiv
        ((etaleAbelianDerivedAdjunction.{u, v} g).comp
          (etaleAbelianDerivedAdjunction.{u, v} f))
        (etaleAbelianDerivedAdjunction.{u, v} fg)
        (etaleAbelianDerivedInverseImageCompIso'.{u, v} f g fg hfg).hom :=
  rfl

end DirectImageCompIso

section Whisker

end Whisker

section CompositeSquare

variable {X Y Z X' Y' Z' : Scheme.{u}}

/-- **The comparison of composite derived inverse images around the outer rectangle is the
vertical composite of the comparisons of the two squares**, whiskered with the comparisons
identifying the inverse image along a composite — stated as an equation between natural
transformations, with every whiskering and every associator written out.

This is the associativity pentagon
`Stacks.EtaleCohomology.etaleAbelianDerivedInverseImageCompIso'_assoc` for the three chains
`X' ⟶ Y' ⟶ Z' ⟶ Z`, `X' ⟶ Y' ⟶ Y ⟶ Z` and `X' ⟶ X ⟶ Y ⟶ Z`; the two comparisons attached to the
middle vertices `Y' ⟶ Z` and `X' ⟶ Y` cancel between consecutive instances.  Nothing is assumed
of the squares beyond commutativity. -/
private theorem derivedSquare_compDirectImage_natTrans
    (f : X ⟶ Y) (g : Y ⟶ Z) (gf : X ⟶ Z) (hgf : gf = f ≫ g)
    (c : Z' ⟶ Z) (d : Y' ⟶ Y) (g' : Y' ⟶ Z') (e : X' ⟶ X) (f' : X' ⟶ Y')
    (q : X' ⟶ Z') (hq : q = f' ≫ g')
    (P₁ : Y' ⟶ Z) (hP₁d : P₁ = d ≫ g) (hP₁g' : P₁ = g' ≫ c)
    (P₂ : X' ⟶ Y) (hP₂e : P₂ = e ≫ f) (hP₂f' : P₂ = f' ≫ d)
    (P : X' ⟶ Z) (hPe : P = e ≫ gf) (hPq : P = q ≫ c)
    (hPf' : P = f' ≫ P₁) (hPg : P = P₂ ≫ g) :
    (etaleAbelianDerivedInverseImageCompIso'.{u, v} q c P hPq).inv ≫
        (etaleAbelianDerivedInverseImageCompIso'.{u, v} e gf P hPe).hom =
      (Functor.whiskerLeft (etaleAbelianDerivedInverseImage.{u, v} c)
            (etaleAbelianDerivedInverseImageCompIso'.{u, v} f' g' q hq).hom ≫
        ((Functor.associator (etaleAbelianDerivedInverseImage.{u, v} c)
                (etaleAbelianDerivedInverseImage.{u, v} g')
                (etaleAbelianDerivedInverseImage.{u, v} f')).inv ≫
            Functor.whiskerRight
                ((etaleAbelianDerivedInverseImageCompIso'.{u, v} g' c P₁ hP₁g').inv ≫
                  (etaleAbelianDerivedInverseImageCompIso'.{u, v} d g P₁ hP₁d).hom)
                (etaleAbelianDerivedInverseImage.{u, v} f') ≫
              (Functor.associator (etaleAbelianDerivedInverseImage.{u, v} g)
                  (etaleAbelianDerivedInverseImage.{u, v} d)
                  (etaleAbelianDerivedInverseImage.{u, v} f')).hom ≫
                Functor.whiskerLeft (etaleAbelianDerivedInverseImage.{u, v} g)
                    ((etaleAbelianDerivedInverseImageCompIso'.{u, v} f' d P₂ hP₂f').inv ≫
                      (etaleAbelianDerivedInverseImageCompIso'.{u, v} e f P₂ hP₂e).hom) ≫
                  (Functor.associator (etaleAbelianDerivedInverseImage.{u, v} g)
                    (etaleAbelianDerivedInverseImage.{u, v} f)
                    (etaleAbelianDerivedInverseImage.{u, v} e)).inv)) ≫
          Functor.whiskerRight
            (etaleAbelianDerivedInverseImageCompIso'.{u, v} f g gf hgf).inv
            (etaleAbelianDerivedInverseImage.{u, v} e) := by
  have hIh := congrArg Iso.hom
    (etaleAbelianDerivedInverseImageCompIso'_assoc.{u, v} c g' f' P₁ hP₁g' q hq P hPq hPf')
  have hIIh := congrArg Iso.hom
    (etaleAbelianDerivedInverseImageCompIso'_assoc.{u, v} g d f' P₁ hP₁d P₂ hP₂f' P hPg hPf')
  have hIIIh := congrArg Iso.hom
    (etaleAbelianDerivedInverseImageCompIso'_assoc.{u, v} g f e gf hgf P₂ hP₂e P hPg hPe)
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom] at hIh hIIh hIIIh
  have hstep : (Functor.associator (etaleAbelianDerivedInverseImage.{u, v} g)
          (etaleAbelianDerivedInverseImage.{u, v} f)
          (etaleAbelianDerivedInverseImage.{u, v} e)).inv ≫
        Functor.whiskerRight
          (etaleAbelianDerivedInverseImageCompIso'.{u, v} f g gf hgf).inv
          (etaleAbelianDerivedInverseImage.{u, v} e) =
      (Functor.whiskerLeft (etaleAbelianDerivedInverseImage.{u, v} g)
            (etaleAbelianDerivedInverseImageCompIso'.{u, v} e f P₂ hP₂e).inv ≫
          (etaleAbelianDerivedInverseImageCompIso'.{u, v} P₂ g P hPg).inv) ≫
        (etaleAbelianDerivedInverseImageCompIso'.{u, v} e gf P hPe).hom := by
    rw [← Iso.comp_inv_eq, Category.assoc]
    exact hIIIh.symm
  have hcancel : Functor.whiskerLeft (etaleAbelianDerivedInverseImage.{u, v} g)
          (etaleAbelianDerivedInverseImageCompIso'.{u, v} e f P₂ hP₂e).hom ≫
        (Functor.associator (etaleAbelianDerivedInverseImage.{u, v} g)
            (etaleAbelianDerivedInverseImage.{u, v} f)
            (etaleAbelianDerivedInverseImage.{u, v} e)).inv ≫
          Functor.whiskerRight
            (etaleAbelianDerivedInverseImageCompIso'.{u, v} f g gf hgf).inv
            (etaleAbelianDerivedInverseImage.{u, v} e) =
      (etaleAbelianDerivedInverseImageCompIso'.{u, v} P₂ g P hPg).inv ≫
        (etaleAbelianDerivedInverseImageCompIso'.{u, v} e gf P hPe).hom := by
    rw [hstep]
    simp only [Category.assoc]
    exact whiskerLeft_hom_inv_id_assoc (etaleAbelianDerivedInverseImage.{u, v} g)
      (etaleAbelianDerivedInverseImageCompIso'.{u, v} e f P₂ hP₂e) _
  simp only [Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc]
  rw [hcancel, reassoc_of% hIIh, Iso.hom_inv_id_assoc, whiskerRight_hom_inv_id_assoc,
    ← reassoc_of% hIh]
  exact (whiskerLeft_hom_inv_id_assoc (etaleAbelianDerivedInverseImage.{u, v} c)
    (etaleAbelianDerivedInverseImageCompIso'.{u, v} f' g' q hq) _).symm

/-- **The comparison of composite derived inverse images around the outer rectangle is the
vertical composite of the comparisons of the two squares**, as an identity of 2-squares. -/
private theorem derivedSquare_compDirectImage
    (f : X ⟶ Y) (g : Y ⟶ Z) (gf : X ⟶ Z) (hgf : gf = f ≫ g)
    (c : Z' ⟶ Z) (d : Y' ⟶ Y) (g' : Y' ⟶ Z') (e : X' ⟶ X) (f' : X' ⟶ Y')
    (q : X' ⟶ Z') (hq : q = f' ≫ g')
    (P₁ : Y' ⟶ Z) (hP₁d : P₁ = d ≫ g) (hP₁g' : P₁ = g' ≫ c)
    (P₂ : X' ⟶ Y) (hP₂e : P₂ = e ≫ f) (hP₂f' : P₂ = f' ≫ d)
    (P : X' ⟶ Z) (hPe : P = e ≫ gf) (hPq : P = q ≫ c)
    (hPf' : P = f' ≫ P₁) (hPg : P = P₂ ≫ g) :
    etaleAbelianDerivedSquare.{u, v} gf c e q P hPe hPq =
      ((TwoSquare.vComp (etaleAbelianDerivedSquare.{u, v} g c d g' P₁ hP₁d hP₁g')
            (etaleAbelianDerivedSquare.{u, v} f d e f' P₂ hP₂e hP₂f')).whiskerRight
          (etaleAbelianDerivedInverseImageCompIso'.{u, v} f' g' q hq).hom).whiskerLeft
        (etaleAbelianDerivedInverseImageCompIso'.{u, v} f g gf hgf).inv := by
  refine TwoSquare.ext _ _ fun W => ?_
  exact NatTrans.congr_app
    (derivedSquare_compDirectImage_natTrans.{u, v} f g gf hgf c d g' e f' q hq P₁ hP₁d hP₁g'
      P₂ hP₂e hP₂f' P hPe hPq hPf' hPg) W

end CompositeSquare

section Main

variable {X Y Z X' Y' Z' : Scheme.{u}}

/-- **The base change map of the outer rectangle, as a composite.**  For morphisms `f : X ⟶ Y`,
`g : Y ⟶ Z` with named composite `gf`, a morphism `c : Z' ⟶ Z`, and commutative squares
`d ≫ g = g' ≫ c` and `e ≫ f = f' ≫ d`, the base change map `c⁻¹ R(gf)_* K ⟶ Rq_* e⁻¹ K` of the
outer rectangle is the base change map of the lower square at `Rf_* K`, followed by `Rg'_*` of
the base change map of the upper square at `K`, read through the two comparisons identifying a
derived direct image along a composite with the composite of the derived direct images.

Nothing is assumed of the two squares beyond commutativity: neither need be cartesian, and no
properness enters. -/
public theorem etaleAbelianDerivedBaseChange_compDirectImage_app
    (f : X ⟶ Y) (g : Y ⟶ Z) (gf : X ⟶ Z) (hgf : gf = f ≫ g)
    (c : Z' ⟶ Z) (d : Y' ⟶ Y) (g' : Y' ⟶ Z') (e : X' ⟶ X) (f' : X' ⟶ Y')
    (q : X' ⟶ Z') (hq : q = f' ≫ g')
    (sq₁ : d ≫ g = g' ≫ c) (sq₂ : e ≫ f = f' ≫ d) (hyp : e ≫ gf = q ≫ c)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    (etaleAbelianDerivedBaseChange.{u, v} gf c e q hyp).app K =
      (etaleAbelianDerivedInverseImage.{u, v} c).map
          ((etaleAbelianDerivedDirectImageCompIso'.{u, v} f g gf hgf).hom.app K) ≫
        (etaleAbelianDerivedBaseChange.{u, v} g c d g' sq₁).app
            ((etaleAbelianDerivedDirectImage.{u, v} f).obj K) ≫
          (etaleAbelianDerivedDirectImage.{u, v} g').map
              ((etaleAbelianDerivedBaseChange.{u, v} f d e f' sq₂).app K) ≫
            (etaleAbelianDerivedDirectImageCompIso'.{u, v} f' g' q hq).inv.app
              ((etaleAbelianDerivedInverseImage.{u, v} e).obj K) := by
  have hPf' : (e ≫ gf : X' ⟶ Z) = f' ≫ d ≫ g := by
    rw [hgf, ← Category.assoc, sq₂, Category.assoc]
  have hPg : (e ≫ gf : X' ⟶ Z) = (e ≫ f) ≫ g := by rw [hgf, Category.assoc]
  rw [etaleAbelianDerivedBaseChange_eq_mateEquiv.{u, v} gf c e q (e ≫ gf) rfl hyp,
    etaleAbelianDerivedBaseChange_eq_mateEquiv.{u, v} g c d g' (d ≫ g) rfl sq₁,
    etaleAbelianDerivedBaseChange_eq_mateEquiv.{u, v} f d e f' (e ≫ f) rfl sq₂,
    derivedSquare_compDirectImage.{u, v} f g gf hgf c d g' e f' q hq (d ≫ g) rfl sq₁
      (e ≫ f) rfl sq₂ (e ≫ gf) rfl hyp hPf' hPg,
    conjugateEquiv_mateEquiv_vcomp (etaleAbelianDerivedAdjunction.{u, v} gf)
      ((etaleAbelianDerivedAdjunction.{u, v} g).comp (etaleAbelianDerivedAdjunction.{u, v} f))
      (etaleAbelianDerivedAdjunction.{u, v} q),
    mateEquiv_conjugateEquiv_vcomp
      ((etaleAbelianDerivedAdjunction.{u, v} g).comp (etaleAbelianDerivedAdjunction.{u, v} f))
      ((etaleAbelianDerivedAdjunction.{u, v} g').comp (etaleAbelianDerivedAdjunction.{u, v} f'))
      (etaleAbelianDerivedAdjunction.{u, v} q),
    mateEquiv_hcomp (etaleAbelianDerivedAdjunction.{u, v} g)
      (etaleAbelianDerivedAdjunction.{u, v} g') (etaleAbelianDerivedAdjunction.{u, v} f)
      (etaleAbelianDerivedAdjunction.{u, v} f'),
    etaleAbelianDerivedDirectImageCompIso'_hom.{u, v} f g gf hgf,
    etaleAbelianDerivedDirectImageCompIso'_inv.{u, v} f' g' q hq]
  simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp]

/-- **Stacks 0A4D, the derived half.**  Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes
with named composite `gf : X ⟶ Z`, let `c : Z' ⟶ Z`, and consider commutative squares
```
X' --e--> X      Y' --d--> Y
|f'       |f     |g'       |g
v         v      v         v
Y' --d--> Y      Z' --c--> Z
```
with `q : X' ⟶ Z'` the named composite of `f'` and `g'`.  Let `K` be an object of
`D(X_étale)`.  If the base change map `c⁻¹ Rg_* ⟶ Rg'_* d⁻¹` of the lower square is an
isomorphism at `Rf_* K`, and the base change map `d⁻¹ Rf_* ⟶ Rf'_* e⁻¹` of the upper square is
an isomorphism at `K`, then the base change map `c⁻¹ R(gf)_* K ⟶ Rq_* e⁻¹ K` of the outer
rectangle is an isomorphism.

This is the composition statement of the source in the derived formulation of
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`: both hypotheses and conclusion say that
a base change map of unbounded derived categories is invertible, so no torsion condition is
imposed on the coefficients.  It is formal, by
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_compDirectImage_app`, which exhibits the
map of the rectangle as the composite of the two given maps with two isomorphisms; neither
square need be cartesian and neither morphism need be proper. -/
@[stacks 0A4D "the derived half: for K in D(X_étale), if c⁻¹Rg_*(Rf_*K) → Rg'_*d⁻¹(Rf_*K) and \
d⁻¹Rf_*K → Rf'_*e⁻¹K are isomorphisms then c⁻¹R(g∘f)_*K → R(g'∘f')_*e⁻¹K is an isomorphism; \
the R^q statement of the same tag, and the reduction to injective Z/l-modules of 0A4B that the \
source proof uses to obtain it, are not covered here"]
public theorem etaleAbelianDerivedBaseChange_isIso_of_compDirectImage
    (f : X ⟶ Y) (g : Y ⟶ Z) (gf : X ⟶ Z) (hgf : gf = f ≫ g)
    (c : Z' ⟶ Z) (d : Y' ⟶ Y) (g' : Y' ⟶ Z') (e : X' ⟶ X) (f' : X' ⟶ Y')
    (q : X' ⟶ Z') (hq : q = f' ≫ g')
    (sq₁ : d ≫ g = g' ≫ c) (sq₂ : e ≫ f = f' ≫ d) (hyp : e ≫ gf = q ≫ c)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))
    (h₁ : IsIso ((etaleAbelianDerivedBaseChange.{u, v} g c d g' sq₁).app
      ((etaleAbelianDerivedDirectImage.{u, v} f).obj K)))
    (h₂ : IsIso ((etaleAbelianDerivedBaseChange.{u, v} f d e f' sq₂).app K)) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, v} gf c e q hyp).app K) := by
  rw [etaleAbelianDerivedBaseChange_compDirectImage_app.{u, v} f g gf hgf c d g' e f' q hq
    sq₁ sq₂ hyp K]
  infer_instance

end Main

end Stacks.EtaleCohomology

end
