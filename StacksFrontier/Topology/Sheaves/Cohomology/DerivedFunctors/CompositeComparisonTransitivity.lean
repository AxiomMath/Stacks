module

public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyComp
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonOnResolutions

/-!
# Transitivity of the composite right-derived comparison

`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` is the comparison
`F.rightDerived n ⋙ G ≅ H.rightDerived n` attached to an exact additive `G` and an isomorphism
`e : F ⋙ G ≅ H`.  Applying two exact functors one after the other gives two ways of comparing
`F.rightDerived n ⋙ G ⋙ G'` with `H'.rightDerived n`: the comparison for `G` pushed forward by
`G'` followed by the comparison for `G'`, or the comparison for the single functor `G ⋙ G'`.
This file proves they agree, and records the corresponding congruence when `G ⋙ G'` is only
*isomorphic* to the functor appearing in the second description.

## Main results

* `rightDerivedCompIso_comp`: the composition law
  `whiskerRight (rightDerivedCompIso F G H e p) G' ≫ rightDerivedCompIso H G' H' e' p
  = rightDerivedCompIso F (G ⋙ G') H' e'' p`, for any `e'' : F ⋙ G ⋙ G' ≅ H'` that is
  pointwise `G'` applied to `e` followed by `e'`.
* `rightDerivedCompIso_congr`: the comparison is natural in the second functor — a natural
  transformation `α : G₁ ⟶ G₂` compatible with `e₁` and `e₂` intertwines the two comparisons.
* `rightDerivedCompIso_comp_congr`: the two combined: `G ⋙ G'` is compared with a single
  functor `K` through an isomorphism `ι : G ⋙ G' ≅ K`.
* `mapComplexHomologyIso_hom_app_comp` and `mapComplexHomologyIso_hom_app_natTrans`: the same
  two statements for `Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso`, the
  complex-level comparison.

## References

* [The Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [The Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedCompTransport

open Stacks.Cohomology.ModuleComparison

/-! ### Reassociation lemmas -/

section Glue

variable {O : Type*} [Category* O]

/-- A commuting square in the middle of a four-fold composite, with the outer factors absorbed on
either side, gives an equality of composites. -/
private theorem compGlue {P Q R S T U : O} (ga : P ⟶ Q) (gb : Q ⟶ R) (gm : R ⟶ T) (dl : T ⟶ U)
    (g₀ : Q ⟶ S) (mu : S ⟶ T) (a' : P ⟶ S) (d' : S ⟶ U)
    (hsquare : gb ≫ gm = g₀ ≫ mu) (hleft : ga ≫ g₀ = a') (hright : mu ≫ dl = d') :
    (ga ≫ gb) ≫ gm ≫ dl = a' ≫ d' := by
  rw [← hleft, ← hright, Category.assoc, Category.assoc, ← Category.assoc gb, hsquare,
    Category.assoc]

/-- A commuting square followed by a commuting triangle gives an equality of composites. -/
private theorem natGlue {P Q R S T : O} (a : P ⟶ Q) (i₂ : Q ⟶ R) (d₂ : R ⟶ T) (i₁ : P ⟶ S)
    (mu : S ⟶ R) (d₁ : S ⟶ T) (hsquare : a ≫ i₂ = i₁ ≫ mu) (htriangle : mu ≫ d₂ = d₁) :
    a ≫ i₂ ≫ d₂ = i₁ ≫ d₁ := by
  rw [← Category.assoc, hsquare, Category.assoc, htriangle]

/-- A commuting triangle in the middle of a three-fold composite gives an equality of
composites. -/
private theorem congrGlue {P Q R S T : O} (x : P ⟶ Q) (a : Q ⟶ R) (i₂ : R ⟶ S) (d : S ⟶ T)
    (i₁ : Q ⟶ S) (htriangle : a ≫ i₂ = i₁) : (x ≫ a) ≫ i₂ ≫ d = x ≫ i₁ ≫ d := by
  rw [Category.assoc, ← Category.assoc a, htriangle]

/-- Cancelling an isomorphism against its own inverse in the middle of a composite. -/
private theorem cancelGlue {P Q R S : O} (i₁ : P ⟶ Q) (mu : Q ⟶ R) (h : R ⟶ S) (iv : S ⟶ R)
    (hh : h ≫ iv = 𝟙 R) : (i₁ ≫ mu ≫ h) ≫ iv = i₁ ≫ mu := by
  rw [Category.assoc, Category.assoc, hh, Category.comp_id]

end Glue

/-! ### The comparison on complexes -/

section Complexes

variable {A : Type*} {B : Type*} {D : Type*} {D' : Type*}
  [Category* A] [Category* B] [Category* D] [Category* D']
  [Abelian A] [Abelian B] [Abelian D] [Abelian D']

/-- Homology maps compose: an equation of composites of chain maps gives one of homology maps. -/
private theorem homologyMap_comp_eq {C : Type*} [Category* C] [Abelian C]
    {K L M : HomologicalComplex C (ComplexShape.up ℕ)} {φ : K ⟶ L} {ψ : L ⟶ M} {χ : K ⟶ M}
    (p : ℕ) (h : φ ≫ ψ = χ) :
    HomologicalComplex.homologyMap φ p ≫ HomologicalComplex.homologyMap ψ p =
      HomologicalComplex.homologyMap χ p := by
  rw [← HomologicalComplex.homologyMap_comp, h]

/-- The component of `Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso` at a complex:
compare the homology of `G` applied degreewise to the complex of `F` with `G` of its homology,
then take the homology of `e` applied degreewise. -/
theorem mapComplexHomologyIso_hom_app (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [G.PreservesHomology] (e : F ⋙ G ≅ H) (p : ℕ)
    (K : HomologicalComplex A (ComplexShape.up ℕ)) :
    (mapComplexHomologyIso F G H e p).hom.app K =
      (homologyMapFunctorIso G p).inv.app ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ≫
        HomologicalComplex.homologyMap
          ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app K) p := rfl

/-- **The composition law for `Stacks.Cohomology.ModuleComparison.homologyMapFunctorIso`.** The
comparison for a composite of two exact functors is the comparison for the first, pushed forward
by the second, followed by the comparison for the second. -/
theorem homologyMapFunctorIso_inv_app_comp (G : B ⥤ D) (G' : D ⥤ D') [G.Additive] [G'.Additive]
    [G.PreservesHomology] [G'.PreservesHomology] [(G ⋙ G').PreservesHomology] (p : ℕ)
    (L : HomologicalComplex B (ComplexShape.up ℕ)) :
    G'.map ((homologyMapFunctorIso G p).inv.app L) ≫
        (homologyMapFunctorIso G' p).inv.app
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) =
      (homologyMapFunctorIso (G ⋙ G') p).inv.app L :=
  (ShortComplex.mapHomologyIso_comp_inv (L.sc p) G G').symm

/-- `Stacks.Cohomology.ModuleComparison.homologyMapFunctorIso` is natural in the complex. -/
theorem homologyMapFunctorIso_inv_app_naturality (G' : D ⥤ D') [G'.Additive]
    [G'.PreservesHomology] (p : ℕ) {L₁ L₂ : HomologicalComplex D (ComplexShape.up ℕ)}
    (φ : L₁ ⟶ L₂) :
    G'.map (HomologicalComplex.homologyMap φ p) ≫ (homologyMapFunctorIso G' p).inv.app L₂ =
      (homologyMapFunctorIso G' p).inv.app L₁ ≫
        HomologicalComplex.homologyMap
          ((G'.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) p :=
  (homologyMapFunctorIso G' p).inv.naturality φ

/-- `Stacks.Cohomology.ModuleComparison.homologyMapFunctorIso` is natural in the functor: a
natural transformation `α : G₁ ⟶ G₂` of exact functors commutes with the two comparisons. -/
theorem homologyMapFunctorIso_inv_app_natTrans {G₁ G₂ : B ⥤ D} [G₁.Additive] [G₂.Additive]
    [G₁.PreservesHomology] [G₂.PreservesHomology] (α : G₁ ⟶ G₂) (p : ℕ)
    (L : HomologicalComplex B (ComplexShape.up ℕ)) :
    α.app (L.homology p) ≫ (homologyMapFunctorIso G₂ p).inv.app L =
      (homologyMapFunctorIso G₁ p).inv.app L ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app L) p :=
  (congrArg (fun z => z ≫ (homologyMapFunctorIso G₂ p).inv.app L)
    (NatTrans.app_homology α (L.sc p))).trans (cancelGlue _ _ _ _ (Iso.hom_inv_id _))

/-- Applying `G'` degreewise to `e` and following with `e'` is `e''`, given that this holds
pointwise. -/
theorem mapHomologicalComplexCompIso_hom_app_comp (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D)
    (G' : D ⥤ D') (H' : A ⥤ D') [F.Additive] [G.Additive] [H.Additive] [G'.Additive]
    [H'.Additive] (e : F ⋙ G ≅ H) (e' : H ⋙ G' ≅ H') (e'' : F ⋙ G ⋙ G' ≅ H')
    (he : ∀ X : A, G'.map (e.hom.app X) ≫ e'.hom.app X = e''.hom.app X)
    (K : HomologicalComplex A (ComplexShape.up ℕ)) :
    (G'.mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app K) ≫
        (Functor.mapHomologicalComplexCompIso e' (ComplexShape.up ℕ)).hom.app K =
      (Functor.mapHomologicalComplexCompIso e'' (ComplexShape.up ℕ)).hom.app K := by
  ext n
  simpa using he (K.X n)

/-- Applying `α` degreewise and following with `e₂` is `e₁`, given that this holds pointwise. -/
theorem mapHomologicalComplexCompIso_hom_app_natTrans (F : A ⥤ B) {G₁ G₂ : B ⥤ D} (H : A ⥤ D)
    [F.Additive] [G₁.Additive] [G₂.Additive] [H.Additive] (α : G₁ ⟶ G₂)
    (e₁ : F ⋙ G₁ ≅ H) (e₂ : F ⋙ G₂ ≅ H)
    (hα : ∀ X : A, α.app (F.obj X) ≫ e₂.hom.app X = e₁.hom.app X)
    (K : HomologicalComplex A (ComplexShape.up ℕ)) :
    (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ≫
        (Functor.mapHomologicalComplexCompIso e₂ (ComplexShape.up ℕ)).hom.app K =
      (Functor.mapHomologicalComplexCompIso e₁ (ComplexShape.up ℕ)).hom.app K := by
  ext n
  simpa using hα (K.X n)

/-- **The composition law for `Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso`.** -/
theorem mapComplexHomologyIso_hom_app_comp (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D)
    (G' : D ⥤ D') (H' : A ⥤ D')
    [F.Additive] [G.Additive] [H.Additive] [G'.Additive] [H'.Additive]
    [G.PreservesHomology] [G'.PreservesHomology] [(G ⋙ G').PreservesHomology]
    (e : F ⋙ G ≅ H) (e' : H ⋙ G' ≅ H') (e'' : F ⋙ G ⋙ G' ≅ H')
    (he : ∀ X : A, G'.map (e.hom.app X) ≫ e'.hom.app X = e''.hom.app X)
    (p : ℕ) (K : HomologicalComplex A (ComplexShape.up ℕ)) :
    G'.map ((mapComplexHomologyIso F G H e p).hom.app K) ≫
        (mapComplexHomologyIso H G' H' e' p).hom.app K =
      (mapComplexHomologyIso F (G ⋙ G') H' e'' p).hom.app K := by
  refine Eq.trans (congrArg (fun z => z ≫ (mapComplexHomologyIso H G' H' e' p).hom.app K)
    (G'.map_comp
      ((homologyMapFunctorIso G p).inv.app ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K))
      (HomologicalComplex.homologyMap
        ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app K) p))) ?_
  exact compGlue _ _ _ _ _ _ _ _
    (homologyMapFunctorIso_inv_app_naturality G' p
      ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app K))
    (homologyMapFunctorIso_inv_app_comp G G' p
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K))
    (homologyMap_comp_eq p
      (mapHomologicalComplexCompIso_hom_app_comp F G H G' H' e e' e'' he K))

/-- **`Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso` is natural in the second
functor.** -/
theorem mapComplexHomologyIso_hom_app_natTrans (F : A ⥤ B) {G₁ G₂ : B ⥤ D} (H : A ⥤ D)
    [F.Additive] [G₁.Additive] [G₂.Additive] [H.Additive]
    [G₁.PreservesHomology] [G₂.PreservesHomology] (α : G₁ ⟶ G₂)
    (e₁ : F ⋙ G₁ ≅ H) (e₂ : F ⋙ G₂ ≅ H)
    (hα : ∀ X : A, α.app (F.obj X) ≫ e₂.hom.app X = e₁.hom.app X)
    (p : ℕ) (K : HomologicalComplex A (ComplexShape.up ℕ)) :
    α.app (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology p) ≫
        (mapComplexHomologyIso F G₂ H e₂ p).hom.app K =
      (mapComplexHomologyIso F G₁ H e₁ p).hom.app K :=
  natGlue _ _ _ _ _ _
    (homologyMapFunctorIso_inv_app_natTrans α p
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K))
    (homologyMap_comp_eq p (mapHomologicalComplexCompIso_hom_app_natTrans F H α e₁ e₂ hα K))

end Complexes

/-! ### The comparison on right derived functors -/

section Derived

variable {A : Type*} {B : Type*} {D : Type*} {D' : Type*}
  [Category* A] [Category* B] [Category* D] [Category* D']
  [Abelian A] [HasInjectiveResolutions A] [Abelian B] [Abelian D] [Abelian D']

/-- **The composition law for
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`, pointwise.** -/
theorem rightDerivedCompIso_hom_app_comp (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D)
    (G' : D ⥤ D') (H' : A ⥤ D')
    [F.Additive] [G.Additive] [H.Additive] [G'.Additive] [H'.Additive]
    [G.PreservesHomology] [G'.PreservesHomology] [(G ⋙ G').PreservesHomology]
    (e : F ⋙ G ≅ H) (e' : H ⋙ G' ≅ H') (e'' : F ⋙ G ⋙ G' ≅ H')
    (he : ∀ X : A, G'.map (e.hom.app X) ≫ e'.hom.app X = e''.hom.app X)
    (p : ℕ) (M : A) :
    G'.map ((rightDerivedCompIso F G H e p).hom.app M) ≫
        (rightDerivedCompIso H G' H' e' p).hom.app M =
      (rightDerivedCompIso F (G ⋙ G') H' e'' p).hom.app M := by
  rw [rightDerivedCompIso_hom_app, rightDerivedCompIso_hom_app, rightDerivedCompIso_hom_app,
    Functor.map_comp, Functor.map_comp, Functor.comp_map, Category.assoc, Category.assoc,
    Iso.map_inv_hom_id_assoc, ← Category.assoc
      (G'.map ((mapComplexHomologyIso F G H e p).hom.app (injectiveResolution M).cocomplex)),
    mapComplexHomologyIso_hom_app_comp F G H G' H' e e' e'' he p
      (injectiveResolution M).cocomplex]

/-- **The composition law for `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`.**
Deriving `F`, applying `G` and then `G'` compares with deriving `H'` in two steps exactly as it
does in one: the comparison for `G` pushed forward by `G'`, followed by the comparison for `G'`,
is the comparison for the single functor `G ⋙ G'`. The hypothesis `he` says that `e''` is the
composite comparison `F ⋙ G ⋙ G' ≅ H ⋙ G' ≅ H'`, pointwise. -/
theorem rightDerivedCompIso_comp (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D)
    (G' : D ⥤ D') (H' : A ⥤ D')
    [F.Additive] [G.Additive] [H.Additive] [G'.Additive] [H'.Additive]
    [G.PreservesHomology] [G'.PreservesHomology] [(G ⋙ G').PreservesHomology]
    (e : F ⋙ G ≅ H) (e' : H ⋙ G' ≅ H') (e'' : F ⋙ G ⋙ G' ≅ H')
    (he : ∀ X : A, G'.map (e.hom.app X) ≫ e'.hom.app X = e''.hom.app X) (p : ℕ) :
    Functor.whiskerRight (rightDerivedCompIso F G H e p).hom G' ≫
        (rightDerivedCompIso H G' H' e' p).hom =
      (rightDerivedCompIso F (G ⋙ G') H' e'' p).hom :=
  NatTrans.ext (funext fun M =>
    rightDerivedCompIso_hom_app_comp F G H G' H' e e' e'' he p M)

/-- **`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` is natural in the second functor,
pointwise.** -/
theorem rightDerivedCompIso_hom_app_natTrans (F : A ⥤ B) {G₁ G₂ : B ⥤ D} (H : A ⥤ D)
    [F.Additive] [G₁.Additive] [G₂.Additive] [H.Additive]
    [G₁.PreservesHomology] [G₂.PreservesHomology] (α : G₁ ⟶ G₂)
    (e₁ : F ⋙ G₁ ≅ H) (e₂ : F ⋙ G₂ ≅ H)
    (hα : ∀ X : A, α.app (F.obj X) ≫ e₂.hom.app X = e₁.hom.app X)
    (p : ℕ) (M : A) :
    α.app ((F.rightDerived p).obj M) ≫ (rightDerivedCompIso F G₂ H e₂ p).hom.app M =
      (rightDerivedCompIso F G₁ H e₁ p).hom.app M := by
  rw [rightDerivedCompIso_hom_app, rightDerivedCompIso_hom_app, ← Category.assoc,
    ← α.naturality]
  exact congrGlue _ _ _ _ _
    (mapComplexHomologyIso_hom_app_natTrans F H α e₁ e₂ hα p (injectiveResolution M).cocomplex)

/-- **`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` is natural in the second
functor.** A natural transformation `α : G₁ ⟶ G₂` of exact functors which carries `e₁` to `e₂`
intertwines the comparison for `G₁` with the comparison for `G₂`. -/
theorem rightDerivedCompIso_congr (F : A ⥤ B) {G₁ G₂ : B ⥤ D} (H : A ⥤ D)
    [F.Additive] [G₁.Additive] [G₂.Additive] [H.Additive]
    [G₁.PreservesHomology] [G₂.PreservesHomology] (α : G₁ ⟶ G₂)
    (e₁ : F ⋙ G₁ ≅ H) (e₂ : F ⋙ G₂ ≅ H)
    (hα : ∀ X : A, α.app (F.obj X) ≫ e₂.hom.app X = e₁.hom.app X) (p : ℕ) :
    Functor.whiskerLeft (F.rightDerived p) α ≫ (rightDerivedCompIso F G₂ H e₂ p).hom =
      (rightDerivedCompIso F G₁ H e₁ p).hom :=
  NatTrans.ext (funext fun M =>
    rightDerivedCompIso_hom_app_natTrans F H α e₁ e₂ hα p M)

/-- **The composition law for `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` against a
single functor.** Let `ι : G ⋙ G' ≅ K` identify the composite of the two exact functors with a
single exact functor `K`. Then the two-step comparison through `G` and `G'` is the one-step
comparison through `K`, read along `ι`. -/
theorem rightDerivedCompIso_comp_congr (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D)
    (G' : D ⥤ D') (H' : A ⥤ D') (K : B ⥤ D')
    [F.Additive] [G.Additive] [H.Additive] [G'.Additive] [H'.Additive] [K.Additive]
    [G.PreservesHomology] [G'.PreservesHomology] [(G ⋙ G').PreservesHomology]
    [K.PreservesHomology]
    (e : F ⋙ G ≅ H) (e' : H ⋙ G' ≅ H') (ι : G ⋙ G' ≅ K) (eK : F ⋙ K ≅ H')
    (hcompat : ∀ X : A,
      G'.map (e.hom.app X) ≫ e'.hom.app X = ι.hom.app (F.obj X) ≫ eK.hom.app X)
    (p : ℕ) :
    Functor.whiskerRight (rightDerivedCompIso F G H e p).hom G' ≫
        (rightDerivedCompIso H G' H' e' p).hom =
      Functor.whiskerLeft (F.rightDerived p) ι.hom ≫ (rightDerivedCompIso F K H' eK p).hom :=
  (rightDerivedCompIso_comp F G H G' H' e e' (Functor.isoWhiskerLeft F ι ≪≫ eK) hcompat p).trans
    (rightDerivedCompIso_congr F H' ι.hom (Functor.isoWhiskerLeft F ι ≪≫ eK) eK
      (fun _ => rfl) p).symm

end Derived

end Stacks.Cohomology.DerivedCompTransport

end
