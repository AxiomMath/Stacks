module

public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShiftNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexSourceShiftCommShift

/-! # The derived internal Hom commutes with the translation in its contravariant variable

Let `(C, O)` be a ringed site. This file builds, for arbitrary objects `K`, `L` of `D(O)` and
every integer `b`, the identification

`RSheafHom(K[b], L) ≅ RSheafHom(K, L)[-b]`,

the contravariant companion of
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso`.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedSheafHomSourceShiftIsoOfKInjective`: the commutation at a
  K-injective representative of the covariant variable.
* `AlgebraicGeometry.RingedSite.derivedSheafHomSourceShiftIso`: the commutation for arbitrary
  objects of `D(O)`.
* `AlgebraicGeometry.RingedSite.derivedSheafHomOpShiftNatIso`: the commutation assembled into a
  natural isomorphism of functors on `D(O)ᵒᵖ`, which is the `commShiftIso` datum of a
  `CategoryTheory.Functor.CommShift ℤ` on `RSheafHom(-, M)` for the opposite shift of
  `CategoryTheory.Pretriangulated.Opposite`.
* `AlgebraicGeometry.RingedSite.commShift_derivedSheafHomFlip`: **the whole residual, reduced to
  a statement about complexes.** `RSheafHom(-, M)` commutes with the shift, together with *both*
  of the coherence equations of `CategoryTheory.Functor.CommShift`, as soon as the contravariant
  internal Hom *complex* `SheafHom(-, I)` does for every complex `I`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomSourceShiftIso_hom_naturality`: the commutation is
  natural in both variables, for arbitrary morphisms of `D(O)`.

## Implementation notes

The route is the one of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShift`, with the
cochain-level input changed from `AlgebraicGeometry.RingedSite.sheafHomTargetShiftIso` to
`AlgebraicGeometry.RingedSite.sheafHomSourceShiftIso`, which is the identification
`SheafHom(A, I)[-b] ≅ SheafHom(A[b], I)` of internal Hom complexes. At a K-injective target the
derived internal Hom is the ordinary internal Hom complex
(`AlgebraicGeometry.RingedSite.derivedSheafHomComparison`, Tag 0A97) and the localization
functor commutes with the translation, so the identification is a composite of four
isomorphisms, none of which has to be computed. Unlike the covariant case no condition falls on
the varying variable: the source of an internal Hom complex is arbitrary, so the K-injective
representative used here is the one of the *fixed* target.

The transport to arbitrary objects uses the chosen K-injective representatives
`AlgebraicGeometry.RingedSite.kInjectiveModel` and
`AlgebraicGeometry.RingedSite.derivedSheafHomObjectsModelIso`, exactly as
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso` does; the shifted representative of
`K[b]` is the shift of the representative of `K`, which is why the commutation of the
localization functor with the translation appears twice.

*What is proved and what is not.* The commutation isomorphism itself, its naturality in both
variables, and its assembly into the natural isomorphism the `CategoryTheory.Functor.CommShift`
datum consists of are all proved here. The two coherence equations
`CategoryTheory.Functor.CommShift.commShiftIso_zero` and `commShiftIso_add` are *not*, so no
`CategoryTheory.Functor.CommShift` instance is registered; what is proved instead is that they
follow from the corresponding structure one level down, on the ordinary internal Hom complex, by
localization descent (`AlgebraicGeometry.RingedSite.commShift_derivedSheafHomFlip`). That
descent is available because the opposite shift of
`CategoryTheory.Pretriangulated.Opposite` makes `Q.op` a shift-compatible localization functor,
by Mathlib's `CategoryTheory.Pretriangulated.Opposite.commShiftFunctorOpInt`, so
`CategoryTheory.Functor.commShiftOfLocalization` applies on the opposite category exactly as it
does on `D(O)` itself. Nothing of the derived category, of the K-injective resolution, or of the
localization survives in the hypothesis that is left.

## References

* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 08DH](https://stacks.math.columbia.edu/tag/08DH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-- **The derived internal Hom commutes with the translation in its contravariant variable, at a
K-injective representative of the target.** For an arbitrary complex `A` and a K-injective
complex `I` of `O`-modules,

`RSheafHom(A[b], I) ≅ RSheafHom(A, I)[-b]`.

Both sides are computed by the ordinary internal Hom complex, and the ordinary internal Hom
complex commutes with the translation in its source by
`AlgebraicGeometry.RingedSite.sheafHomSourceShiftIso`. -/
def derivedSheafHomSourceShiftIsoOfKInjective
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] (b : ℤ) :
    ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj (A⟦b⟧)))).obj
        (DerivedCategory.Q.obj I) ≅
      (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
        (DerivedCategory.Q.obj I))⟦-b⟧ :=
  derivedSheafHomComparison X (A⟦b⟧) I ≪≫
    DerivedCategory.Q.mapIso (sheafHomSourceShiftIso X (K := A) (M := I) b).symm ≪≫
      (DerivedCategory.Q.commShiftIso (-b)).app (sheafHomComplex X A I).obj ≪≫
        (CategoryTheory.shiftFunctor
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (-b)).mapIso (derivedSheafHomComparison X A I).symm

/-- **The derived internal Hom commutes with the translation in its contravariant variable.**
For arbitrary objects `K`, `L` of `D(O)` and every integer `b`,

`RSheafHom(K[b], L) ≅ RSheafHom(K, L)[-b]`.

The chosen K-injective representative `I` of `L` and the chosen representative `A` of `K` are
used; `A[b]` represents `K[b]`, and at those representatives the identification is
`AlgebraicGeometry.RingedSite.derivedSheafHomSourceShiftIsoOfKInjective`. -/
def derivedSheafHomSourceShiftIso
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (b : ℤ) :
    ((derivedSheafHomBifunctor X).obj (op (K⟦b⟧))).obj L ≅
      (((derivedSheafHomBifunctor X).obj (op K)).obj L)⟦-b⟧ :=
  derivedSheafHomObjectsModelIso X
      ((DerivedCategory.Q.commShiftIso b).app (kInjectiveModel X K) ≪≫
        (CategoryTheory.shiftFunctor
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          b).mapIso
          (kInjectiveModelIso X K))
      (kInjectiveModelIso X L) ≪≫
    derivedSheafHomSourceShiftIsoOfKInjective X (kInjectiveModel X K) (kInjectiveModel X L) b ≪≫
      (CategoryTheory.shiftFunctor
        (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (-b)).mapIso
        (derivedSheafHomObjectsModelIso X (kInjectiveModelIso X K) (kInjectiveModelIso X L)).symm

/-! ### Naturality -/

/-- The contravariant commutation at a K-injective representative, written out as the composite
of its four factors. -/
theorem derivedSheafHomSourceShiftIsoOfKInjective_hom
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] (b : ℤ) :
    (derivedSheafHomSourceShiftIsoOfKInjective X A I b).hom =
      (derivedSheafHomComparison X (A⟦b⟧) I).hom ≫
        DerivedCategory.Q.map (sheafHomSourceShiftIso X (K := A) (M := I) b).inv ≫
          (DerivedCategory.Q.commShiftIso (-b)).hom.app ((sheafHomComplex X A I).obj) ≫
            (CategoryTheory.shiftFunctor
              (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
                (-b)).map
              (derivedSheafHomComparison X A I).inv := rfl

/-- **The contravariant commutation is natural in both variables at a K-injective
representative.** For `u : A' ⟶ A` and `v : I ⟶ I'` with `I`, `I'` K-injective, the morphism
induced on `RSheafHom` by `u[b]` and `v` is carried by
`AlgebraicGeometry.RingedSite.derivedSheafHomSourceShiftIsoOfKInjective` to the `(-b)`-shift of
the morphism induced by `u` and `v`.

Each of the four factors is natural: the comparison of Tag 0A97 by
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality`, the commutation of the
ordinary internal Hom complex with the translation in its source by
`AlgebraicGeometry.RingedSite.sheafHomSourceShiftIso_hom_naturality`, and the commutation of the
localization functor with the translation by
`CategoryTheory.Functor.commShiftIso_hom_naturality`. -/
theorem derivedSheafHomSourceShiftIsoOfKInjective_hom_naturality
    {A A' I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective] (u : A' ⟶ A) (v : I ⟶ I') (b : ℤ) :
    (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map
              ((CategoryTheory.shiftFunctor
                (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
                b).map u)).op).app
            (DerivedCategory.Q.obj I) ≫
          ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj (A'⟦b⟧)))).map
            (DerivedCategory.Q.map v)) ≫
        (derivedSheafHomSourceShiftIsoOfKInjective X A' I' b).hom =
      (derivedSheafHomSourceShiftIsoOfKInjective X A I b).hom ≫
        (CategoryTheory.shiftFunctor
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (-b)).map
          (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map u).op).app
              (DerivedCategory.Q.obj I) ≫
            ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
              (DerivedCategory.Q.map v)) := by
  have hs : DerivedCategory.Q.map (homMap X
            ((CategoryTheory.shiftFunctor
              (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
              b).map u) v) ≫
        DerivedCategory.Q.map (sheafHomSourceShiftIso X (K := A') (M := I') b).inv =
      DerivedCategory.Q.map (sheafHomSourceShiftIso X (K := A) (M := I) b).inv ≫
        DerivedCategory.Q.map
          ((CategoryTheory.shiftFunctor
            (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
            (-b)).map (homMap X u v)) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
    rw [Iso.comp_inv_eq, Category.assoc, ← sheafHomSourceShiftIso_hom_naturality,
      Iso.inv_hom_id_assoc]
  have ht : (CategoryTheory.shiftFunctor
            (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (-b)).map (DerivedCategory.Q.map (homMap X u v)) ≫
        (CategoryTheory.shiftFunctor
            (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (-b)).map (derivedSheafHomComparison X A' I').inv =
      (CategoryTheory.shiftFunctor
            (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (-b)).map (derivedSheafHomComparison X A I).inv ≫
        (CategoryTheory.shiftFunctor
            (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (-b)).map
          (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map u).op).app
              (DerivedCategory.Q.obj I) ≫
            ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
              (DerivedCategory.Q.map v)) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
    have h := derivedSheafHomComparison_naturality X u v
    rw [Iso.eq_inv_comp, ← Category.assoc, ← h]
    simp
  rw [derivedSheafHomSourceShiftIsoOfKInjective_hom,
    derivedSheafHomSourceShiftIsoOfKInjective_hom, Category.assoc,
    reassoc_of% (derivedSheafHomComparison_naturality X
      ((CategoryTheory.shiftFunctor
        (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
        b).map u) v),
    reassoc_of% hs, CategoryTheory.Functor.commShiftIso_hom_naturality_assoc, ht]
  simp only [Category.assoc]

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The contravariant commutation of the derived internal Hom with the translation is natural
in both variables for arbitrary morphisms of `D(O)`** — equivalently, the identification
`RSheafHom(K[b], L) ≅ RSheafHom(K, L)[-b]` does not depend on the chosen K-injective models. For
`φ : K' ⟶ K` and `ψ : L ⟶ L'` the morphism induced by `φ[b]` and `ψ` is carried by
`AlgebraicGeometry.RingedSite.derivedSheafHomSourceShiftIso` to the `(-b)`-shift of the morphism
induced by `φ` and `ψ`.

The proof is the one of
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso_hom_naturality`, with the shift moved
to the other variable: both variables move by a morphism of complexes because the model used in
both is the K-injective one, so
`AlgebraicGeometry.RingedSite.exists_Q_map_eq_of_isKInjective` applies to each comparison, and the
transports are matched by
`AlgebraicGeometry.RingedSite.derivedSheafHomObjectsModelIso_hom_naturality` together with
`AlgebraicGeometry.RingedSite.Q_map_shift_eq`. -/
theorem derivedSheafHomSourceShiftIso_hom_naturality
    {K K' L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : K' ⟶ K) (ψ : L ⟶ L')
    (b : ℤ) :
    (((derivedSheafHomBifunctor X).map
              ((CategoryTheory.shiftFunctor
                (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
                b).map φ).op).app L ≫
          ((derivedSheafHomBifunctor X).obj (op (K'⟦b⟧))).map ψ) ≫
        (derivedSheafHomSourceShiftIso X K' L' b).hom =
      (derivedSheafHomSourceShiftIso X K L b).hom ≫
        (CategoryTheory.shiftFunctor
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (-b)).map
          (((derivedSheafHomBifunctor X).map φ.op).app L ≫
            ((derivedSheafHomBifunctor X).obj (op K')).map ψ) := by
  obtain ⟨a, ha⟩ := exists_Q_map_eq_of_isKInjective X
    ((kInjectiveModelIso X K').hom ≫ φ ≫ (kInjectiveModelIso X K).inv)
  obtain ⟨c, hc⟩ := exists_Q_map_eq_of_isKInjective X
    ((kInjectiveModelIso X L).hom ≫ ψ ≫ (kInjectiveModelIso X L').inv)
  have hstep1 := derivedSheafHomObjectsModelIso_hom_naturality X
    ((DerivedCategory.Q.commShiftIso b).app (kInjectiveModel X K) ≪≫
      (CategoryTheory.shiftFunctor
        (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        b).mapIso
        (kInjectiveModelIso X K))
    ((DerivedCategory.Q.commShiftIso b).app (kInjectiveModel X K') ≪≫
      (CategoryTheory.shiftFunctor
        (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        b).mapIso
        (kInjectiveModelIso X K'))
    (kInjectiveModelIso X L) (kInjectiveModelIso X L')
    ((CategoryTheory.shiftFunctor
        (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        b).map φ) ψ
    ((CategoryTheory.shiftFunctor
        (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
        b).map a) c
    (Q_map_shift_eq X (kInjectiveModelIso X K') (kInjectiveModelIso X K) φ a ha b) hc
  have hstep3 := derivedSheafHomObjectsModelIso_inv_naturality X
    (kInjectiveModelIso X K) (kInjectiveModelIso X K')
    (kInjectiveModelIso X L) (kInjectiveModelIso X L') φ ψ a c ha hc
  rw [derivedSheafHomSourceShiftIso, derivedSheafHomSourceShiftIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% hstep1,
    reassoc_of% (derivedSheafHomSourceShiftIsoOfKInjective_hom_naturality X a c b),
    ← CategoryTheory.Functor.map_comp, hstep3, CategoryTheory.Functor.map_comp]

/-! ### The commutation in general position, and as a natural isomorphism -/

/-- The contravariant commutation with the index of the outer shift in general position:
`RSheafHom(K[b], L) ≅ RSheafHom(K, L)[c]` whenever `b + c = 0`. This is
`AlgebraicGeometry.RingedSite.derivedSheafHomSourceShiftIso` with the single reindexing
`c = -b` performed once and sealed behind this interface, in the way Mathlib's
`CategoryTheory.shiftFunctorAdd'` seals the reindexing of a sum of shifts: the opposite shift
of `CategoryTheory.Pretriangulated.Opposite` presents `(op K)[n]` as `op (K[-n])`, so a
commutation written with `-b` in the outer position never meets the index the opposite shift
asks for. -/
def derivedSheafHomSourceShiftIso'
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (b c : ℤ) (h : b + c = 0) :
    ((derivedSheafHomBifunctor X).obj (op (K⟦b⟧))).obj L ≅
      (((derivedSheafHomBifunctor X).obj (op K)).obj L)⟦c⟧ :=
  derivedSheafHomSourceShiftIso X K L b ≪≫ eqToIso (by rw [show -b = c from by omega])

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- At `c = -b` the general-position commutation is the one of
`AlgebraicGeometry.RingedSite.derivedSheafHomSourceShiftIso`. -/
theorem derivedSheafHomSourceShiftIso'_eq
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (b : ℤ) :
    derivedSheafHomSourceShiftIso' X K L b (-b) (by omega) =
      derivedSheafHomSourceShiftIso X K L b := by
  ext
  simp only [derivedSheafHomSourceShiftIso', Iso.trans_hom, eqToIso.hom, eqToHom_refl,
    Category.comp_id]

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The contravariant commutation is natural in the contravariant variable alone**: the
special case `ψ = 𝟙` of
`AlgebraicGeometry.RingedSite.derivedSheafHomSourceShiftIso_hom_naturality`, which is the
naturality square the `CategoryTheory.Functor.CommShift` datum of `RSheafHom(-, M)` asks for. -/
theorem derivedSheafHomSourceShiftIso_hom_naturality_left
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (φ : K' ⟶ K) (b : ℤ) :
    ((derivedSheafHomBifunctor X).map
            ((CategoryTheory.shiftFunctor
              (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
              b).map φ).op).app L ≫
        (derivedSheafHomSourceShiftIso X K' L b).hom =
      (derivedSheafHomSourceShiftIso X K L b).hom ≫
        (CategoryTheory.shiftFunctor
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (-b)).map
          (((derivedSheafHomBifunctor X).map φ.op).app L) := by
  have h := derivedSheafHomSourceShiftIso_hom_naturality X φ (𝟙 L) b
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id,
    Category.comp_id] at h
  exact h

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The same naturality square for the general-position commutation
`AlgebraicGeometry.RingedSite.derivedSheafHomSourceShiftIso'`. -/
theorem derivedSheafHomSourceShiftIso'_hom_naturality_left
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (φ : K' ⟶ K) (b c : ℤ)
    (h : b + c = 0) :
    ((derivedSheafHomBifunctor X).map
            ((CategoryTheory.shiftFunctor
              (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
              b).map φ).op).app L ≫
        (derivedSheafHomSourceShiftIso' X K' L b c h).hom =
      (derivedSheafHomSourceShiftIso' X K L b c h).hom ≫
        (CategoryTheory.shiftFunctor
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            c).map
          (((derivedSheafHomBifunctor X).map φ.op).app L) := by
  obtain rfl : c = -b := by omega
  rw [derivedSheafHomSourceShiftIso'_eq, derivedSheafHomSourceShiftIso'_eq]
  exact derivedSheafHomSourceShiftIso_hom_naturality_left X L φ b

open scoped CategoryTheory.Pretriangulated.Opposite

/-- **The commutation of `RSheafHom(-, M)` with the shift, as a natural isomorphism of functors
on `D(O)ᵒᵖ`.** This is exactly the datum a `CategoryTheory.Functor.CommShift ℤ` on the
contravariant derived internal Hom

`RSheafHom(-, M) : D(O)ᵒᵖ ⥤ D(O)`

consists of, for the opposite shift of `CategoryTheory.Pretriangulated.Opposite`: its component
at `op K` is `RSheafHom(K[-n], M) ≅ RSheafHom(K, M)[n]`, because the opposite shift presents
`(op K)[n]` as `op (K[-n])`.

Only the *datum* is built here; the two coherence equations of
`CategoryTheory.Functor.CommShift` are not proved, so this is not registered as an instance. -/
def derivedSheafHomOpShiftNatIso
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ) :
    CategoryTheory.shiftFunctor
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ n ⋙
        (derivedSheafHomBifunctor X).flip.obj M ≅
      (derivedSheafHomBifunctor X).flip.obj M ⋙
        CategoryTheory.shiftFunctor
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n :=
  NatIso.ofComponents
    (fun K => derivedSheafHomSourceShiftIso' X K.unop M (-n) n (by omega))
    (fun {_ _} f =>
      derivedSheafHomSourceShiftIso'_hom_naturality_left X M f.unop (-n) n (by omega))

/-! ### Descent of the commutation from the cochain level

What the commutation *datum* `derivedSheafHomOpShiftNatIso` lacks is the pair of coherence
equations of `CategoryTheory.Functor.CommShift`.  This section shows that both of them come for
free from the corresponding structure on the ordinary internal Hom complex: a
`CategoryTheory.Functor.CommShift ℤ` on

`SheafHom(-, I) : (CochainComplex O-Mod ℤ)ᵒᵖ ⥤ CochainComplex O-Mod ℤ`

for every complex `I`, which is a statement about complexes with no derived category in it,
descends to one on `RSheafHom(-, M)` for every object `M` of `D(O)`.
-/

attribute [local instance] derivedSheafHomBifunctorLifting

attribute [local instance] AlgebraicGeometry.RingedSite.essSurjQ

/-- **The cochain-level model of the contravariant derived internal Hom.**  Fixing the target of
`AlgebraicGeometry.RingedSite.derivedSheafHomModel` at a complex `M₀` gives the composite of the
contravariant internal Hom complex into the chosen K-injective resolution of `M₀` with the
localization functor.  The two functors are definitionally equal; this names the identification
so that the transport of a `CategoryTheory.Functor.CommShift` across it can be written. -/
def derivedSheafHomModelFlipIso
    (M₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((sheafHomComplexBifunctor X).flip.obj ((kInjectiveResolution X).obj M₀)) ⋙
        DerivedCategory.Q ≅
      (derivedSheafHomModel X).flip.obj M₀ :=
  Iso.refl _

/-- **The cochain-level commutation descends to the model.**  If the contravariant internal Hom
complex into every complex commutes with the shift, then so does the cochain-level model
`AlgebraicGeometry.RingedSite.derivedSheafHomModel` of the derived internal Hom with its target
fixed: the model is that functor followed by the localization functor, and the localization
functor commutes with the shift. -/
@[instance_reducible]
def commShift_derivedSheafHomModelFlip
    (hco : ∀ I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      ((sheafHomComplexBifunctor X).flip.obj I).CommShift ℤ)
    (M₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((derivedSheafHomModel X).flip.obj M₀).CommShift ℤ :=
  letI := hco ((kInjectiveResolution X).obj M₀)
  Functor.CommShift.ofIso (derivedSheafHomModelFlipIso X M₀) ℤ

/-- **The contravariant commutation at a target in the image of the localization functor.**  The
derived internal Hom bifunctor is the descent of
`AlgebraicGeometry.RingedSite.derivedSheafHomModel` along `Q.op` and `Q`, so with the target
fixed at the class of a complex it is the descent of the model along `Q.op` alone — that is
`CategoryTheory.Localization.Lifting₂.snd` — and
`CategoryTheory.Functor.commShiftOfLocalization` transports the commutation of the model,
*together with both of its coherence equations*, to the descent.

`Q.op` commutes with the shift for the opposite shift of
`CategoryTheory.Pretriangulated.Opposite` by Mathlib's
`CategoryTheory.Pretriangulated.Opposite.commShiftFunctorOpInt`, which is what makes the descent
available on the opposite category at all. -/
@[instance_reducible]
def commShift_derivedSheafHomFlipOfQ
    (hco : ∀ I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      ((sheafHomComplexBifunctor X).flip.obj I).CommShift ℤ)
    (M₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((derivedSheafHomBifunctor X).flip.obj (DerivedCategory.Q.obj M₀)).CommShift ℤ :=
  letI := commShift_derivedSheafHomModelFlip X hco M₀
  letI : Localization.Lifting DerivedCategory.Q.op
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).op
      ((derivedSheafHomModel X).flip.obj M₀)
      ((derivedSheafHomBifunctor X).flip.obj (DerivedCategory.Q.obj M₀)) :=
    Localization.Lifting₂.snd DerivedCategory.Q.op DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).op
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ))
      (derivedSheafHomModel X) (derivedSheafHomBifunctor X) M₀
  Functor.commShiftOfLocalization DerivedCategory.Q.op
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)).op ℤ
    ((derivedSheafHomModel X).flip.obj M₀)
    ((derivedSheafHomBifunctor X).flip.obj (DerivedCategory.Q.obj M₀))

/-- **The contravariant derived internal Hom commutes with the shift, as soon as the
contravariant internal Hom *complex* does.**

For every object `M` of `D(O)`,

`RSheafHom(-, M) : D(O)ᵒᵖ ⥤ D(O)`

carries a `CategoryTheory.Functor.CommShift ℤ` for the opposite shift of
`CategoryTheory.Pretriangulated.Opposite`, provided the contravariant internal Hom complex
`SheafHom(-, I)` does for every complex `I` of `O`-modules.  **This is the whole residual**: the
hypothesis is a statement about complexes of `O`-modules in which no derived category, no
K-injective resolution and no localization appears, and the two coherence equations of the
conclusion are derived from those of the hypothesis rather than reproved.

An arbitrary target `M` is the class of a complex up to isomorphism, and a
`CategoryTheory.Functor.CommShift` transports along an isomorphism of functors by
`CategoryTheory.Functor.CommShift.ofIso`, which is the last step. -/
@[instance_reducible]
def commShift_derivedSheafHomFlip
    (hco : ∀ I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      ((sheafHomComplexBifunctor X).flip.obj I).CommShift ℤ)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).flip.obj M).CommShift ℤ :=
  letI := commShift_derivedSheafHomFlipOfQ X hco (DerivedCategory.Q.objPreimage M)
  Functor.CommShift.ofIso
    ((derivedSheafHomBifunctor X).flip.mapIso
      (DerivedCategory.Q.objObjPreimageIso M)) ℤ

/-- **The two equations the contravariant commutation is missing, written out at the cochain
level.**  Feeding the coherence equations of
`AlgebraicGeometry.RingedSite.sheafHomOpCommShiftIso` — the commutation datum of the ordinary
internal Hom complex, which is proved in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexSourceShiftCommShift` — to
`AlgebraicGeometry.RingedSite.commShift_derivedSheafHomFlip` gives the
`CategoryTheory.Functor.CommShift ℤ` on `RSheafHom(-, M)`.

So the whole gap between this development and that instance is the pair of hypotheses `hzero`
and `hadd` below: two equations between morphisms of *complexes* of `O`-modules, in which no
derived category, no K-injective resolution and no localization appears. -/
@[instance_reducible]
def commShift_derivedSheafHomFlipOfCochainCoherence
    (hzero : ∀ I : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      sheafHomOpCommShiftIso X I 0 =
        Functor.CommShift.isoZero ((sheafHomComplexBifunctor X).flip.obj I) ℤ)
    (hadd : ∀ (I : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (a b : ℤ),
      sheafHomOpCommShiftIso X I (a + b) =
        Functor.CommShift.isoAdd (sheafHomOpCommShiftIso X I a) (sheafHomOpCommShiftIso X I b))
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).flip.obj M).CommShift ℤ :=
  commShift_derivedSheafHomFlip X
    (fun I => commShift_sheafHomComplexFlip X I (hzero I) (hadd I)) M

end AlgebraicGeometry.RingedSite

end
