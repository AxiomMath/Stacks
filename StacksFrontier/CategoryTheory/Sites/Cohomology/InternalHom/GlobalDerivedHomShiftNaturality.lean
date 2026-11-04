module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomTransport

/-!
# The commutation of the derived internal Hom with the translation is natural

Let `(C, O)` be a ringed site. The commutation of the derived internal Hom with the translation
in its covariant variable,

`RSheafHom(K, L[n]) ≅ RSheafHom(K, L)[n]`,

is `AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShift`, where it is
built at a K-injective representative of the covariant variable and transported, and where no
naturality in either variable is claimed. This file proves that it **is** natural in both
variables, for arbitrary morphisms of `D(O)`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIsoOfKInjective_hom_naturality`: the
  commutation is natural in both variables at a K-injective representative, for morphisms of
  complexes.
* `AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso_hom_naturality`: **the commutation
  is natural in both variables for arbitrary morphisms of `D(O)`.**

## Implementation notes

At a K-injective representative the commutation is a composite of four isomorphisms, and its
naturality is the naturality of each: the comparison of Tag 0A97 with the ordinary internal Hom
complex is natural by `AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality`, the
commutation of the ordinary internal Hom complex with the translation in its target is natural
in both complexes by `AlgebraicGeometry.RingedSite.sheafHomTargetShiftIso_hom_naturality`, and
the localization functor commutes with the translation naturally by
`CategoryTheory.Functor.commShiftIso_hom_naturality`.

*No refinement is needed for the transport.* The section "What this file does not contain" of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects`, and
the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShift` after it, record
that moving a variable of `RSheafHom` along an arbitrary morphism of `D(O)` is obstructed by such
a morphism not being the class of a morphism of complexes. For the present transport the
obstruction does not arise in *either* variable, because the model used in both is the
K-injective one: `AlgebraicGeometry.RingedSite.exists_Q_map_eq_of_isKInjective` therefore applies
to both comparisons, and neither the common K-flat refinement
`AlgebraicGeometry.RingedSite.exists_kFlat_common_refinement` nor Tag 0A96 is used here. What the
transport does need is that the chosen K-injective model of `L[n]` be compared with the shift of
the chosen model of `L`, which is the naturality of the commutation of the localization functor
with the translation again, in
`AlgebraicGeometry.RingedSite.Q_map_shift_eq`.

## References

* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-! ### Naturality at a K-injective representative -/

/-- The commutation of the derived internal Hom with the translation at a K-injective
representative, written out as the composite of its four factors. -/
theorem derivedSheafHomTargetShiftIsoOfKInjective_hom
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] (n : ℤ) :
    (derivedSheafHomTargetShiftIsoOfKInjective X A I n).hom =
      (derivedSheafHomComparison X A (I⟦n⟧)).hom ≫
        DerivedCategory.Q.map (sheafHomTargetShiftIso X (K := A) (M := I) n).inv ≫
          (DerivedCategory.Q.commShiftIso n).hom.app ((sheafHomComplex X A I).obj) ≫
            (CategoryTheory.shiftFunctor (DerivedCategory
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).map
              (derivedSheafHomComparison X A I).inv := rfl

/-- **The commutation of the derived internal Hom with the translation is natural in both
variables at a K-injective representative.** For `f : A' ⟶ A` and `g : I ⟶ I'` with `I`, `I'`
K-injective, the morphism induced on `RSheafHom` by `f` and `g[n]` is carried by
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIsoOfKInjective` to the `n`-shift of the
morphism induced by `f` and `g`.

Each of the four factors is natural: the comparison of Tag 0A97 by
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality`, the commutation of the
ordinary internal Hom complex with the translation by
`AlgebraicGeometry.RingedSite.sheafHomTargetShiftIso_hom_naturality`, and the commutation of the
localization functor with the translation by
`CategoryTheory.Functor.commShiftIso_hom_naturality`. -/
theorem derivedSheafHomTargetShiftIsoOfKInjective_hom_naturality
    {A A' I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective] (f : A' ⟶ A) (g : I ⟶ I') (n : ℤ) :
    (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map f).op).app
            (DerivedCategory.Q.obj (I⟦n⟧)) ≫
          ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
            (DerivedCategory.Q.map
              ((CategoryTheory.shiftFunctor
                (CochainComplex (SheafOfModules.{u}
                    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) n).map g))) ≫
        (derivedSheafHomTargetShiftIsoOfKInjective X A' I' n).hom =
      (derivedSheafHomTargetShiftIsoOfKInjective X A I n).hom ≫
        (CategoryTheory.shiftFunctor
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).map
          (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map f).op).app
              (DerivedCategory.Q.obj I) ≫
            ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
              (DerivedCategory.Q.map g)) := by
  have hs : homMap X f (g⟦n⟧') ≫ (sheafHomTargetShiftIso X (K := A') (M := I') n).inv =
      (sheafHomTargetShiftIso X (K := A) (M := I) n).inv ≫ (homMap X f g)⟦n⟧' := by
    rw [Iso.comp_inv_eq, Category.assoc, ← sheafHomTargetShiftIso_hom_naturality,
      Iso.inv_hom_id_assoc]
  have ht : DerivedCategory.Q.map (homMap X f g) ≫ (derivedSheafHomComparison X A' I').inv =
      (derivedSheafHomComparison X A I).inv ≫
        (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map f).op).app
            (DerivedCategory.Q.obj I) ≫
          ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
            (DerivedCategory.Q.map g)) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← derivedSheafHomComparison_naturality X f g]
    simp
  rw [derivedSheafHomTargetShiftIsoOfKInjective_hom,
    derivedSheafHomTargetShiftIsoOfKInjective_hom, Category.assoc,
    reassoc_of% (derivedSheafHomComparison_naturality X f (g⟦n⟧')),
    ← Functor.map_comp_assoc, hs, Functor.map_comp_assoc,
    Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, ht]
  simp only [Functor.map_comp, Category.assoc]

/-! ### Naturality for arbitrary morphisms of `D(O)` -/

/-- **Transporting a morphism of `D(O)` along the two representing isomorphisms transports the
morphism induced on the derived internal Hom.** If `a` and `b` are morphisms of complexes whose
classes are the conjugates of `φ` and `ψ` by the four representing isomorphisms, then the
comparison `AlgebraicGeometry.RingedSite.derivedSheafHomObjectsModelIso` carries the morphism
induced by `φ` and `ψ` to the one induced by `Q a` and `Q b`.

Both sides are the morphism induced in both variables by a single pair of morphisms of `D(O)`,
by the two-variable functoriality
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor_map_comp`, and the two pairs agree by the
defining properties of `a` and `b`. -/
theorem derivedSheafHomObjectsModelIso_hom_naturality
    {L L' M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A A' I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eA : DerivedCategory.Q.obj A ≅ L) (eA' : DerivedCategory.Q.obj A' ≅ L')
    (eI : DerivedCategory.Q.obj I ≅ M) (eI' : DerivedCategory.Q.obj I' ≅ M')
    (φ : L' ⟶ L) (ψ : M ⟶ M') (a : A' ⟶ A) (b : I ⟶ I')
    (ha : DerivedCategory.Q.map a = eA'.hom ≫ φ ≫ eA.inv)
    (hb : DerivedCategory.Q.map b = eI.hom ≫ ψ ≫ eI'.inv) :
    (((derivedSheafHomBifunctor X).map φ.op).app M ≫
          ((derivedSheafHomBifunctor X).obj (op L')).map ψ) ≫
        (derivedSheafHomObjectsModelIso X eA' eI').hom =
      (derivedSheafHomObjectsModelIso X eA eI).hom ≫
        (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map a).op).app
            (DerivedCategory.Q.obj I) ≫
          ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
            (DerivedCategory.Q.map b)) := by
  have hA : DerivedCategory.Q.map a ≫ eA.hom = eA'.hom ≫ φ := by rw [ha]; simp
  have hB : eI.inv ≫ DerivedCategory.Q.map b = ψ ≫ eI'.inv := by rw [hb]; simp
  rw [derivedSheafHomObjectsModelIso_hom, derivedSheafHomObjectsModelIso_hom,
    derivedSheafHomBifunctor_map_comp, derivedSheafHomBifunctor_map_comp, hA, hB]

/-- `AlgebraicGeometry.RingedSite.derivedSheafHomObjectsModelIso_hom_naturality` read on the
inverses: the comparison with the models carries the morphism induced by `Q a` and `Q b` back to
the one induced by `φ` and `ψ`. -/
theorem derivedSheafHomObjectsModelIso_inv_naturality
    {L L' M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A A' I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eA : DerivedCategory.Q.obj A ≅ L) (eA' : DerivedCategory.Q.obj A' ≅ L')
    (eI : DerivedCategory.Q.obj I ≅ M) (eI' : DerivedCategory.Q.obj I' ≅ M')
    (φ : L' ⟶ L) (ψ : M ⟶ M') (a : A' ⟶ A) (b : I ⟶ I')
    (ha : DerivedCategory.Q.map a = eA'.hom ≫ φ ≫ eA.inv)
    (hb : DerivedCategory.Q.map b = eI.hom ≫ ψ ≫ eI'.inv) :
    (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map a).op).app
            (DerivedCategory.Q.obj I) ≫
          ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
            (DerivedCategory.Q.map b)) ≫
        (derivedSheafHomObjectsModelIso X eA' eI').inv =
      (derivedSheafHomObjectsModelIso X eA eI).inv ≫
        (((derivedSheafHomBifunctor X).map φ.op).app M ≫
          ((derivedSheafHomBifunctor X).obj (op L')).map ψ) := by
  rw [Iso.comp_inv_eq, Category.assoc,
    derivedSheafHomObjectsModelIso_hom_naturality X eA eA' eI eI' φ ψ a b ha hb,
    Iso.inv_hom_id_assoc]

/-- **The shift of a representing isomorphism represents the shift.** If the class of `b` is the
conjugate of `ψ : L ⟶ L'` by `eI` and `eI'`, then the class of `b[n]` is the conjugate of `ψ[n]`
by the two shifted representing isomorphisms, which are built from `eI`, `eI'` and the commutation
of the localization functor with the translation. This is the compatibility the transport of
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso` to arbitrary objects needs in its
covariant variable. -/
theorem Q_map_shift_eq
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eI : DerivedCategory.Q.obj I ≅ L) (eI' : DerivedCategory.Q.obj I' ≅ L')
    (ψ : L ⟶ L') (b : I ⟶ I')
    (hb : DerivedCategory.Q.map b = eI.hom ≫ ψ ≫ eI'.inv) (n : ℤ) :
    DerivedCategory.Q.map
        ((CategoryTheory.shiftFunctor
          (CochainComplex
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) n).map b) =
      ((DerivedCategory.Q.commShiftIso n).app I ≪≫
            (CategoryTheory.shiftFunctor
              (DerivedCategory (SheafOfModules.{u}
                  (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).mapIso eI).hom ≫
        ((CategoryTheory.shiftFunctor
            (DerivedCategory
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).map ψ) ≫
          ((DerivedCategory.Q.commShiftIso n).app I' ≪≫
            (CategoryTheory.shiftFunctor
              (DerivedCategory (SheafOfModules.{u}
                  (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).mapIso eI').inv := by
  have hinner : DerivedCategory.Q.map b ≫ eI'.hom = eI.hom ≫ ψ := by rw [hb]; simp
  rw [← Category.assoc, Iso.eq_comp_inv]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  rw [CategoryTheory.Functor.commShiftIso_hom_naturality_assoc,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hinner]

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The commutation of the derived internal Hom with the translation is natural in both
variables for arbitrary morphisms of `D(O)`** — equivalently, the identification
`RSheafHom(K, L[n]) ≅ RSheafHom(K, L)[n]` does not depend on the chosen K-injective models. For
`φ : K' ⟶ K` and `ψ : L ⟶ L'` the morphism induced by `φ` and `ψ[n]` is carried by
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso` to the `n`-shift of the morphism
induced by `φ` and `ψ`.

Both variables move by a morphism of complexes, because the model used in both is the K-injective
one: `AlgebraicGeometry.RingedSite.exists_Q_map_eq_of_isKInjective` applies to each comparison, so
the naturality at a representative,
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIsoOfKInjective_hom_naturality`, is
available, and the transports are matched by
`AlgebraicGeometry.RingedSite.derivedSheafHomObjectsModelIso_hom_naturality` together with
`AlgebraicGeometry.RingedSite.Q_map_shift_eq`. No K-flat refinement and no
appeal to Tag 0A96 is needed. -/
theorem derivedSheafHomTargetShiftIso_hom_naturality
    {K K' L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : K' ⟶ K) (ψ : L ⟶ L') (n : ℤ) :
    (((derivedSheafHomBifunctor X).map φ.op).app (L⟦n⟧) ≫
          ((derivedSheafHomBifunctor X).obj (op K')).map
            ((CategoryTheory.shiftFunctor
              (DerivedCategory
                  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).map ψ)) ≫
        (derivedSheafHomTargetShiftIso X K' L' n).hom =
      (derivedSheafHomTargetShiftIso X K L n).hom ≫
        (CategoryTheory.shiftFunctor
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).map
          (((derivedSheafHomBifunctor X).map φ.op).app L ≫
            ((derivedSheafHomBifunctor X).obj (op K')).map ψ) := by
  obtain ⟨a, ha⟩ := exists_Q_map_eq_of_isKInjective X
    ((kInjectiveModelIso X K').hom ≫ φ ≫ (kInjectiveModelIso X K).inv)
  obtain ⟨b, hb⟩ := exists_Q_map_eq_of_isKInjective X
    ((kInjectiveModelIso X L).hom ≫ ψ ≫ (kInjectiveModelIso X L').inv)
  have hstep1 := derivedSheafHomObjectsModelIso_hom_naturality X
    (kInjectiveModelIso X K) (kInjectiveModelIso X K')
    ((DerivedCategory.Q.commShiftIso n).app (kInjectiveModel X L) ≪≫
      (CategoryTheory.shiftFunctor (DerivedCategory
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).mapIso
        (kInjectiveModelIso X L))
    ((DerivedCategory.Q.commShiftIso n).app (kInjectiveModel X L') ≪≫
      (CategoryTheory.shiftFunctor (DerivedCategory
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).mapIso
        (kInjectiveModelIso X L'))
    φ ((CategoryTheory.shiftFunctor
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).map ψ)
    a ((CategoryTheory.shiftFunctor
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) n).map b)
    ha (Q_map_shift_eq X (kInjectiveModelIso X L) (kInjectiveModelIso X L')
      ψ b hb n)
  have hstep3 := derivedSheafHomObjectsModelIso_inv_naturality X
    (kInjectiveModelIso X K) (kInjectiveModelIso X K')
    (kInjectiveModelIso X L) (kInjectiveModelIso X L') φ ψ a b ha hb
  rw [derivedSheafHomTargetShiftIso, derivedSheafHomTargetShiftIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% hstep1,
    reassoc_of% (derivedSheafHomTargetShiftIsoOfKInjective_hom_naturality X a b n),
    ← CategoryTheory.Functor.map_comp, hstep3, CategoryTheory.Functor.map_comp]

end AlgebraicGeometry.RingedSite

end
