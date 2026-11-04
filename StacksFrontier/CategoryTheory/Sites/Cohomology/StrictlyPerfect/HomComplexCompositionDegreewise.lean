module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.InternalHomSheafComposition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexOfAStrictlyPerfectComplex

/-!
# The composition morphism of internal Hom complexes, read degreewise

Let `(C, O)` be a ringed site and let `K`, `L`, `M` be complexes of `O`-modules. The internal Hom
complex `SheafHom(K, M)` of Stacks 0A8Z has for its degree-`n` term the product, over `q : ℤ`, of
the internal Hom sheaves `Hom_O(K^{-q}, M^{n-q})`, the projections being
`AlgebraicGeometry.RingedSite.homDegreeProjection`. This file identifies the composition morphism
of Stacks 0A91

`Tot(SheafHom(L, M) ⊗_O SheafHom(K, L)) ⟶ SheafHom(K, M)`

in each of those components: the component of a composite is the composite of the components,
paired by the composition pairing of internal Hom sheaves of Stacks 03EM. No sign and no
intermediate sum occur, because a homogeneous component of the composition morphism of Stacks
0A91 is evaluation of one factor after the other.

## Main definitions

* `AlgebraicGeometry.RingedSite.homDegreeProj`: the degreewise projection of the internal Hom
  complex, **indexed by the degrees of the two modules** rather than by a single degree.

## Main results

* `AlgebraicGeometry.RingedSite.homDegreeProj_val_app`: the degreewise projection is the
  homogeneous component of the cochain a section describes.
* `AlgebraicGeometry.RingedSite.homDegreeProj_compositionMap`: **the degreewise component of the
  composition morphism of Stacks 0A91 is the composite of the degreewise components.**
* `AlgebraicGeometry.RingedSite.homDegreeProj_compositionMap_pairing`: the same statement with
  the composite of the two components named through the composition pairing
  `AlgebraicGeometry.RingedSite.internalHomComposition`.

## Implementation notes

**Why a second projection.** `AlgebraicGeometry.RingedSite.homDegreeProjection X E F n q` lands in
`Hom_O(E^{-q}, F^{n-q})`: its source degree is `-q` and its target degree is `n - q`, both
determined by the single index `q`. Two such projections can therefore never be composed without a
transport, because the target degree `n - q` of one is not syntactically the negation of any index.
`homDegreeProj X E F n r b` keeps the source degree in the form `-r`, which is what the index of
the underlying projection forces, but takes the target degree `b` as a *parameter* constrained by
`n - r = b`. One transport remains, on the target alone, and it is the transport along an
equation between integers which `omega` discharges; substituting that equation makes it the
identity, which is how `homDegreeProj_val_app` is proved.

With the target degree free, the three projections entering a composition can be indexed so that
the middle module is spelt the same way on both sides: the degree-`q` projection of
`SheafHom(K, L)` is asked for the target degree `-(r - q)`, which is exactly the source degree of
the degree-`p` projection of `SheafHom(L, M)` at the index `r - q`. So the statement of
`homDegreeProj_compositionMap` carries no `eqToHom` at all.

**The statement is about local sections.** Both sides of `homDegreeProj_compositionMap` are
sections of an internal Hom sheaf over an object of the site, evaluated on the local pure tensor
`AlgebraicGeometry.RingedSite.tensorTotalSection`. That is the form the composition morphism of
Stacks 0A91 is characterised in, by
`AlgebraicGeometry.RingedSite.compositionMap_tensorTotalSection`, and the form in which the
identity is used: a local computation of the composition product recognises the components of the
factors, not the morphism out of the total complex.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

/-- **The degreewise projection of the internal Hom complex, indexed by the degrees of the two
modules.** For `n - r = b` it is the projection of the degree-`n` term of `SheafHom(E, F)` onto
`Hom_O(E^{-r}, F^b)`.

This is `AlgebraicGeometry.RingedSite.homDegreeProjection` with the target degree taken as a
parameter, so that two of these can be composed with no transport; see the implementation notes. -/
def homDegreeProj
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n r b : ℤ) (hb : n - r = b) :
    (sheafHomComplex X E F).obj.X n ⟶ internalHomSheaf X (E.X (-r)) (F.X b) :=
  homDegreeProjection X E F n r ≫
    eqToHom (congrArg (fun m => internalHomSheaf X (E.X (-r)) (F.X m)) hb)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The degreewise projection is the homogeneous component of the cochain a section describes.**
The morphism `E^{-r}|_U ⟶ F^b|_U` that the projection attaches to a degree-`n` section `s` of
`SheafHom(E, F)` over `U` is the `(-r, b)` component of the cochain
`AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsEquiv` attaches to `s`. -/
theorem homDegreeProj_val_app
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n r b : ℤ) (hb : n - r = b) (U : X.C)
    (s : ((sheafHomComplex X E F).obj.X n).val.obj (op U)) :
    (homDegreeProj X E F n r b hb).val.app (op U) s =
      (((sheafHomComplex X E F).sectionsEquiv U n s).v (-r) b (by omega)).val := by
  subst hb
  rfl

section Composition

variable (K L M : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The degreewise component of the composition morphism of Stacks 0A91 is the composite of the
degreewise components.** For a degree-`p` section `β` of `SheafHom(L, M)` and a degree-`q` section
`γ` of `SheafHom(K, L)` over the same object `U`, the component of their composite in
`Hom_O(K^{-r}, M^{p+q-r})` is the composite of the component of `γ` in `Hom_O(K^{-r}, L^{-(r-q)})`
with the component of `β` in `Hom_O(L^{-(r-q)}, M^{p+q-r})`.

The cochain that the composite section describes is, by
`AlgebraicGeometry.RingedSite.compositionSection_cochain`, the composite of the cochains the two
factors describe, and the homogeneous components of a composite of cochains are the composites of
their components, which is `CochainComplex.HomComplex.Cochain.comp_v`. -/
theorem homDegreeProj_compositionMap (p q r : ℤ) (U : X.C)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    (homDegreeProj X K M (p + q) r (p + q - r) rfl).val.app (op U)
        (((compositionMap X K L M).f (p + q)).val.app (op U)
          (tensorTotalSection X (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj U p q
            β γ)) =
      internalHomComposeSection X U
        ((homDegreeProj X L M p (r - q) (p + q - r) (by omega)).val.app (op U) β)
        ((homDegreeProj X K L q r (-(r - q)) (by omega)).val.app (op U) γ) := by
  rw [compositionMap_tensorTotalSection, internalHomComposeSection_eq, homDegreeProj_val_app,
    homDegreeProj_val_app, homDegreeProj_val_app, compositionSection_cochain]
  show (((compositionCochain X U p q (p + q) rfl β γ).v (-r) (p + q - r) (by omega)).val) = _
  rw [compositionCochain,
    Cochain.comp_v _ _ (show q + p = p + q from by omega) (-r) (-(r - q)) (p + q - r)
      (by omega) (by omega)]
  rfl

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The degreewise component of the composition morphism of Stacks 0A91 is the composition
pairing of internal Hom sheaves applied to the degreewise components.** This is
`AlgebraicGeometry.RingedSite.homDegreeProj_compositionMap` with the composite of the two
components named through `AlgebraicGeometry.RingedSite.internalHomComposition`. -/
theorem homDegreeProj_compositionMap_pairing (p q r : ℤ) (U : X.C)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    (homDegreeProj X K M (p + q) r (p + q - r) rfl).val.app (op U)
        (((compositionMap X K L M).f (p + q)).val.app (op U)
          (tensorTotalSection X (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj U p q
            β γ)) =
      (internalHomComposition X (K.X (-r)) (L.X (-(r - q))) (M.X (p + q - r))).val.app (op U)
        (internalHomTensorSection X (K.X (-r)) (L.X (-(r - q))) (M.X (p + q - r)) U
          ((homDegreeProj X L M p (r - q) (p + q - r) (by omega)).val.app (op U) β)
          ((homDegreeProj X K L q r (-(r - q)) (by omega)).val.app (op U) γ)) :=
  (homDegreeProj_compositionMap X K L M p q r U β γ).trans
    (internalHomComposition_tensorSection X (K.X (-r)) (L.X (-(r - q))) (M.X (p + q - r)) U _
      _).symm

end Composition

end AlgebraicGeometry.RingedSite

end
