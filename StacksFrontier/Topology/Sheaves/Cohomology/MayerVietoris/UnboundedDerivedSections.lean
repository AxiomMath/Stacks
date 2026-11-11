module

public import Mathlib.Topology.Sheaves.MayerVietoris
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RingedSpace.KFlatResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.TriangleOfAPushoutSquare
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.CoverSquare

/-!
# Unbounded Mayer--Vietoris for derived sections

Let `(X, 𝒪_X)` be a ringed space and let `X = U ∪ V` be a union of two open subsets.  Stacks
08BX asserts that every object `E` of the unbounded derived category `D(𝒪_X)` sits in a
distinguished triangle

`RΓ(X, E) ⟶ RΓ(U, E) ⊕ RΓ(V, E) ⟶ RΓ(U ∩ V, E) ⟶ RΓ(X, E)⟦1⟧`

functorially in `E`; applying the cohomological functors to it gives the functorial
Mayer--Vietoris long exact sequence.  Nothing in the argument uses that the two opens cover
the whole space, so the triangle is proved here for a pair of opens `U`, `V` covering an
arbitrary open `W`, with `RΓ(W, E)` in place of `RΓ(X, E)`.

## Main definitions

* `Stacks.Cohomology.SpaceMayerVietoris.ModuleSheaves`: the abelian category of
  `𝒪_X`-modules on a ringed space.
* `Stacks.Cohomology.SpaceMayerVietoris.sectionsComplexDerived`: sections over an open
  applied degreewise to a complex and then localized, the functor whose right derived functor
  is `RΓ(U, -)`.
* `Stacks.Cohomology.SpaceMayerVietoris.sectionsRestrictionDerived`: the canonical
  restriction map between those functors, before deriving.

## Main results

* `Stacks.Cohomology.SpaceMayerVietoris.relativeUnboundedMayerVietoris`: **Stacks 08BX** for a
  pair of opens covering an arbitrary open `W`, the functorial distinguished Mayer--Vietoris
  triangle relating the derived sections over `W`, over each of the two opens, and over their
  intersection.
* `Stacks.Cohomology.SpaceMayerVietoris.unboundedMayerVietoris`: **Stacks 08BX**, the
  functorial distinguished Mayer--Vietoris triangle for a cover by two opens, the case
  `W = ⊤` of the previous result.

## Implementation notes

Rather than fixing models for the four derived sections functors, the statement quantifies
over arbitrary functors `RX`, `RU`, `RV`, `RUV` equipped with
`CategoryTheory.Functor.IsRightDerivedFunctor` data for the degreewise sections functors, so
it applies to every choice of them.  The units are taken at the cochain level, with
`HomologicalComplex.quasiIso` as the localizer: this is the form in which the derived sections
of Stacks 0F16 are constructed, and by uniqueness of right derived functors it quantifies over
the same functors `RΓ(U, -)` as the homotopy-category form does.  Functoriality in the derived
object is expressed by the five maps of the triangle being natural transformations of those
functors; the first two are assembled, and the next two split, through the binary biproduct,
and the sign on the restriction from `V` is the usual Mayer--Vietoris sign.

The first two maps are the right-derived natural transformations of restriction, and the
connecting map is a natural transformation, so the triangle is functorial on the nose rather
than merely existing at each object.

The proof is the ringed-site construction of Stacks 0F16 applied to the site of opens of `X`:
a ringed space is a ringed site whose sheaves of modules are the `𝒪_X`-modules, and the square
`U ∩ V, V, U, X` of opens has sheafified representables forming a pushout square by
`TopologicalSpace.Opens.mayerVietorisSquare'`, with `h_{U ∩ V}^# ⟶ h_V^#` a monomorphism
because the site of opens is thin.  Stacks 0EVY then makes the canonical comparison of Stacks
0F16 invertible, so its triangle is distinguished, and the given derived functors are carried
onto the ones built there by the uniqueness of right derived functors; the restriction maps
match because the units of the constructed system commute with restriction.

## References

* [Stacks Project, Tag 08BX](https://stacks.math.columbia.edu/tag/08BX)
* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
* [Stacks Project, Tag 0EVY](https://stacks.math.columbia.edu/tag/0EVY)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.RingedSpace (ringedSite)

universe u

namespace Stacks.Cohomology.SpaceMayerVietoris

attribute [local instance] HasDerivedCategory.standard

/-- The abelian category of modules over the structure sheaf of a ringed space, the category in
which the object `E` of Stacks 08BX lives after passing to the derived category. -/
public abbrev ModuleSheaves (X : RingedSpace.{u, u}) :=
  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O)

/-- Sections over an open subset applied degreewise to a complex of `𝒪_X`-modules and then
localized to the derived category of abelian groups: the functor whose right derived functor
is the `RΓ(W, -)` of Stacks 08BX. -/
public abbrev sectionsComplexDerived (X : RingedSpace.{u, u}) (W : Opens X.carrier) :
    CochainComplex (ModuleSheaves X) ℤ ⥤ DerivedCategory AddCommGrpCat.{u} :=
  MayerVietoris.sectionsComplex.{u, u, u, u} (ringedSite X) W ⋙ DerivedCategory.Q

/-- Restriction of sections along an inclusion of opens, applied degreewise and localized: the
underived form of the restriction maps appearing in the Mayer--Vietoris triangle of Stacks
08BX. -/
public abbrev sectionsRestrictionDerived (X : RingedSpace.{u, u}) {Z W : Opens X.carrier}
    (f : Z ⟶ W) : sectionsComplexDerived X W ⟶ sectionsComplexDerived X Z :=
  Functor.whiskerRight
    (MayerVietoris.sectionsRestrictionComplex.{u, u, u, u} (ringedSite X) f) DerivedCategory.Q

section Biprod

variable {A : Type*} [Category A] [Limits.HasZeroMorphisms A]

/-- Reading the first component of a lift followed by an isomorphism of biproducts. -/
private lemma lift_mapIso_comp_fst {P Q R Q' R' : A} [HasBinaryBiproduct Q R]
    [HasBinaryBiproduct Q' R'] (x : P ⟶ Q) (y : P ⟶ R) (a : Q ≅ Q') (b : R ≅ R') :
    (biprod.lift x y ≫ (biprod.mapIso a b).hom) ≫ biprod.fst = x ≫ a.hom := by
  rw [biprod.mapIso_hom, Category.assoc, biprod.map_fst, biprod.lift_fst_assoc]

/-- Reading the second component of a lift followed by an isomorphism of biproducts. -/
private lemma lift_mapIso_comp_snd {P Q R Q' R' : A} [HasBinaryBiproduct Q R]
    [HasBinaryBiproduct Q' R'] (x : P ⟶ Q) (y : P ⟶ R) (a : Q ≅ Q') (b : R ≅ R') :
    (biprod.lift x y ≫ (biprod.mapIso a b).hom) ≫ biprod.snd = y ≫ b.hom := by
  rw [biprod.mapIso_hom, Category.assoc, biprod.map_snd, biprod.lift_snd_assoc]

/-- Reading the first component of a lift precomposed with a map. -/
private lemma comp_lift_comp_fst {P P' Q R : A} [HasBinaryBiproduct Q R] (h : P' ⟶ P)
    (x : P ⟶ Q) (y : P ⟶ R) : (h ≫ biprod.lift x y) ≫ biprod.fst = h ≫ x := by
  rw [Category.assoc, biprod.lift_fst]

/-- Reading the second component of a lift precomposed with a map. -/
private lemma comp_lift_comp_snd {P P' Q R : A} [HasBinaryBiproduct Q R] (h : P' ⟶ P)
    (x : P ⟶ Q) (y : P ⟶ R) : (h ≫ biprod.lift x y) ≫ biprod.snd = h ≫ y := by
  rw [Category.assoc, biprod.lift_snd]

/-- Restricting a descent followed by a map to the first summand. -/
private lemma inl_comp_desc_comp {Q R S S' : A} [HasBinaryBiproduct Q R] (x : Q ⟶ S)
    (y : R ⟶ S) (h : S ⟶ S') : biprod.inl ≫ biprod.desc x y ≫ h = x ≫ h := by
  rw [← Category.assoc, biprod.inl_desc]

/-- Restricting a descent followed by a map to the second summand. -/
private lemma inr_comp_desc_comp {Q R S S' : A} [HasBinaryBiproduct Q R] (x : Q ⟶ S)
    (y : R ⟶ S) (h : S ⟶ S') : biprod.inr ≫ biprod.desc x y ≫ h = y ≫ h := by
  rw [← Category.assoc, biprod.inr_desc]

/-- Restricting an isomorphism of biproducts followed by a descent to the first summand. -/
private lemma inl_mapIso_comp_desc {Q R Q' R' S : A} [HasBinaryBiproduct Q R]
    [HasBinaryBiproduct Q' R'] (a : Q ≅ Q') (b : R ≅ R') (p : Q' ⟶ S) (q : R' ⟶ S) :
    biprod.inl ≫ (biprod.mapIso a b).hom ≫ biprod.desc p q = a.hom ≫ p := by
  rw [biprod.mapIso_hom, biprod.inl_map_assoc, biprod.inl_desc]

/-- Restricting an isomorphism of biproducts followed by a descent to the second summand. -/
private lemma inr_mapIso_comp_desc {Q R Q' R' S : A} [HasBinaryBiproduct Q R]
    [HasBinaryBiproduct Q' R'] (a : Q ≅ Q') (b : R ≅ R') (p : Q' ⟶ S) (q : R' ⟶ S) :
    biprod.inr ≫ (biprod.mapIso a b).hom ≫ biprod.desc p q = b.hom ≫ q := by
  rw [biprod.mapIso_hom, biprod.inr_map_assoc, biprod.inr_desc]

/-- Cancelling the image of an inverse pair of maps at the end of a composite. -/
private lemma comp_comp_map_cancel {A : Type*} [Category A] {B : Type*} [Category B]
    (K : A ⥤ B) {P Q : A} {W Y : B} (α : W ⟶ Y) (d : Y ⟶ K.obj P) (i : P ⟶ Q) (h : Q ⟶ P)
    (hih : i ≫ h = 𝟙 P) : (α ≫ d ≫ K.map i) ≫ K.map h = α ≫ d := by
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, hih, K.map_id, Category.comp_id]

end Biprod

section Square

variable {T : Type u} [TopologicalSpace T]

/-- The sheafified representables of the square of two open subsets covering an open subset
form a pushout square: this is `TopologicalSpace.Opens.mayerVietorisSquare'`, transported from
the Yoneda embedding to its universe-raising form. -/
private lemma isPushout_coverSquare (U V : Opens T) {W : Opens T} (hUV : U ⊔ V = W) :
    ((coverSquare U V hUV).map
      (Sheaf.sheafifiedYoneda (Opens.grothendieckTopology T))).IsPushout := by
  have hmv : ((coverSquare U V hUV).map
      (yoneda ⋙ presheafToSheaf (Opens.grothendieckTopology T) (Type u))).IsPushout :=
    (Opens.mayerVietorisSquare' (coverSquare U V hUV)
      (hUV.symm.trans (sup_comm U V)) (inf_comm U V)).isPushout
  let e : Sheaf.sheafifiedYoneda (Opens.grothendieckTopology T) ≅
      yoneda ⋙ presheafToSheaf (Opens.grothendieckTopology T) (Type u) :=
    Functor.isoWhiskerRight uliftYonedaIsoYoneda.{u, u, u}
      (presheafToSheaf (Opens.grothendieckTopology T) (Type u))
  refine hmv.of_iso (Square.isoMk (e.symm.app _) (e.symm.app _) (e.symm.app _) (e.symm.app _)
    ?_ ?_ ?_ ?_)
  all_goals simpa [Square.map] using e.symm.hom.naturality _

end Square

/-- **Stacks 0EVY at a ringed space.** For a cover of an open subset `W` of a ringed space by
two open subsets, the canonical comparison of Stacks 0F16 attached to the square
`U ∩ V, V, U, W` is an isomorphism. -/
private lemma isIso_derivedCSquare_coverSquare (X : RingedSpace.{u, u})
    (U V : Opens X.carrier) {W : Opens X.carrier} (hUV : U ⊔ V = W) :
    IsIso (Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u, u}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
      (coverSquare U V hUV)).derivedCSquare := by
  apply MayerVietoris.isIso_derivedCSquare_of_isPushout.{u, u, u, u}
  · exact isPushout_coverSquare U V hUV
  · have : ∀ {Z W' : Opens X.carrier} (g : Z ⟶ W'), Mono g := fun _ =>
      ⟨fun a b _ => Subsingleton.elim a b⟩
    apply Sheaf.mono_sheafifiedYoneda_map

/-- Two right derived functors of the same functor along the same localizer are compared by a
unique isomorphism, and that isomorphism carries the right-derived transformation induced by a
transformation `τ` of the underived functors onto any transformation `ρ` of the second pair
that induces the same transformation of units.  This is what identifies the restriction maps
of Stacks 08BX with the ones of the construction of Stacks 0F16. -/
private lemma rightDerivedNatTrans_comp_unique {C : Type*} [Category C] {D : Type*}
    [Category D] {H : Type*} [Category H] {L : C ⥤ D} (W : MorphismProperty C)
    [L.IsLocalization W] {F G : C ⥤ H} {RF RG DF DG : D ⥤ H} (α : F ⟶ L ⋙ RF)
    (β : G ⟶ L ⋙ RG) (ηF : F ⟶ L ⋙ DF) (ηG : G ⟶ L ⋙ DG)
    [RF.IsRightDerivedFunctor α W] [RG.IsRightDerivedFunctor β W] (τ : F ⟶ G) (ρ : DF ⟶ DG)
    (eF : RF ≅ DF) (eG : RG ≅ DG) (heF : α ≫ L.whiskerLeft eF.hom = ηF)
    (heG : β ≫ L.whiskerLeft eG.hom = ηG) (hη : τ ≫ ηG = ηF ≫ L.whiskerLeft ρ) :
    RF.rightDerivedNatTrans RG α β W τ ≫ eG.hom = eF.hom ≫ ρ := by
  refine Functor.rightDerived_ext RF α W DG _ _ ?_
  simp only [Functor.whiskerLeft_comp]
  rw [← Category.assoc, Functor.rightDerivedNatTrans_fac, Category.assoc, heG, hη, ← heF,
    Category.assoc]

/-- Transport of the Mayer--Vietoris triangle along isomorphisms of the four derived
functors.  Given a distinguished triangle built from four natural transformations of one
system of functors and a comparison with a second system that matches those transformations,
the corresponding triangle for the second system is distinguished.  Stated for abstract
functors, so that the comparison is carried out on small terms. -/
private lemma distTriang_of_comparison {X : RingedSpace.{u, u}}
    (RX RU RV RUV DX DU DV DUV : DerivedCategory (ModuleSheaves X) ⥤
      DerivedCategory AddCommGrpCat.{u})
    (rXU : RX ⟶ RU) (rXV : RX ⟶ RV) (rUUV : RU ⟶ RUV) (rVUV : RV ⟶ RUV)
    (ρXU : DX ⟶ DU) (ρXV : DX ⟶ DV) (ρUUV : DU ⟶ DUV) (ρVUV : DV ⟶ DUV)
    (eX : RX ≅ DX) (eU : RU ≅ DU) (eV : RV ≅ DV) (eUV : RUV ≅ DUV)
    (hXU : rXU ≫ eU.hom = eX.hom ≫ ρXU) (hXV : rXV ≫ eV.hom = eX.hom ≫ ρXV)
    (hUUV : rUUV ≫ eUV.hom = eU.hom ≫ ρUUV) (hVUV : rVUV ≫ eUV.hom = eV.hom ≫ ρVUV)
    (E : DerivedCategory (ModuleSheaves X))
    (d : DUV.obj E ⟶
      (shiftFunctor (DerivedCategory AddCommGrpCat.{u}) (1 : ℤ)).obj (DX.obj E))
    (d' : RUV.obj E ⟶
      (shiftFunctor (DerivedCategory AddCommGrpCat.{u}) (1 : ℤ)).obj (RX.obj E))
    (hd : d' = eUV.hom.app E ≫ d ≫
      (shiftFunctor (DerivedCategory AddCommGrpCat.{u}) (1 : ℤ)).map (eX.inv.app E))
    (hdist : Triangle.mk (biprod.lift (ρXU.app E) (ρXV.app E))
      (biprod.desc (ρUUV.app E) (-(ρVUV.app E))) d ∈
        distTriang (DerivedCategory AddCommGrpCat.{u})) :
    Triangle.mk (biprod.lift (rXU.app E) (rXV.app E))
        (biprod.desc (rUUV.app E) (-(rVUV.app E))) d' ∈
      distTriang (DerivedCategory AddCommGrpCat.{u}) := by
  refine isomorphic_distinguished _ hdist _ ?_
  refine Triangle.isoMk _ _ (eX.app E) (biprod.mapIso (eU.app E) (eV.app E)) (eUV.app E)
    ?_ ?_ ?_
  · apply biprod.hom_ext
    · dsimp only [Triangle.mk_mor₁]
      rw [lift_mapIso_comp_fst, comp_lift_comp_fst]
      simpa only [NatTrans.comp_app, Iso.app_hom] using congrArg (fun α => α.app E) hXU
    · dsimp only [Triangle.mk_mor₁]
      rw [lift_mapIso_comp_snd, comp_lift_comp_snd]
      simpa only [NatTrans.comp_app, Iso.app_hom] using congrArg (fun α => α.app E) hXV
  · apply biprod.hom_ext'
    · dsimp only [Triangle.mk_mor₂]
      rw [inl_comp_desc_comp, inl_mapIso_comp_desc]
      simpa only [NatTrans.comp_app, Iso.app_hom] using congrArg (fun α => α.app E) hUUV
    · dsimp only [Triangle.mk_mor₂]
      rw [inr_comp_desc_comp, inr_mapIso_comp_desc]
      simpa only [NatTrans.comp_app, Iso.app_hom, Preadditive.neg_comp, Preadditive.comp_neg,
        neg_inj] using congrArg (fun α => α.app E) hVUV
  · dsimp only [Triangle.mk_mor₃]
    rw [hd]
    simpa only [Iso.app_hom] using comp_comp_map_cancel
      (shiftFunctor (DerivedCategory AddCommGrpCat.{u}) (1 : ℤ)) (eUV.hom.app E) d
      (eX.inv.app E) (eX.hom.app E)
      (by rw [← NatTrans.comp_app, eX.inv_hom_id, NatTrans.id_app])

/-- **Stacks 08BX for a cover of an arbitrary open.** Let `X` be a ringed space and let
`W = U ∪ V` be an open subset written as the union of two open subsets.  For any choice of
derived sections functors over `W`, `U`, `V` and `U ∩ V` — that is, any right derived functors
of degreewise sections along the quasi-isomorphisms — the right-derived restriction maps, with
the usual sign on the overlap, fit into a distinguished triangle in the derived category of
abelian groups, naturally in the object of `D(𝒪_X)`: the connecting map is a natural
transformation and the other four maps are natural transformations of the given functors.
Applying the cohomological functors gives the functorial Mayer--Vietoris long exact
sequence. -/
@[stacks 08BX "the triangle, for a pair of opens covering an arbitrary open, not only the whole
space"]
public theorem relativeUnboundedMayerVietoris (X : RingedSpace.{u, u})
    (U V W : Opens X.carrier) (hUV : U ⊔ V = W)
    (RW RU RV RUV : DerivedCategory (ModuleSheaves X) ⥤ DerivedCategory AddCommGrpCat.{u})
    (aW : sectionsComplexDerived X W ⟶ DerivedCategory.Q ⋙ RW)
    (aU : sectionsComplexDerived X U ⟶ DerivedCategory.Q ⋙ RU)
    (aV : sectionsComplexDerived X V ⟶ DerivedCategory.Q ⋙ RV)
    (aUV : sectionsComplexDerived X (U ⊓ V) ⟶ DerivedCategory.Q ⋙ RUV)
    [RW.IsRightDerivedFunctor aW
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RU.IsRightDerivedFunctor aU
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RV.IsRightDerivedFunctor aV
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RUV.IsRightDerivedFunctor aUV
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))] :
    ∃ δ : RUV ⟶ RW ⋙ shiftFunctor (DerivedCategory AddCommGrpCat.{u}) (1 : ℤ),
      ∀ E, Triangle.mk
        (biprod.lift
          ((RW.rightDerivedNatTrans RU aW aU
            (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))
            (sectionsRestrictionDerived X (homOfLE (le_sup_left.trans hUV.le : U ≤ W)))).app E)
          ((RW.rightDerivedNatTrans RV aW aV
            (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))
            (sectionsRestrictionDerived X (homOfLE (le_sup_right.trans hUV.le : V ≤ W)))).app E))
        (biprod.desc
          ((RU.rightDerivedNatTrans RUV aU aUV
            (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))
            (sectionsRestrictionDerived X (homOfLE (inf_le_left : U ⊓ V ≤ U)))).app E)
          (-((RV.rightDerivedNatTrans RUV aV aUV
            (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))
            (sectionsRestrictionDerived X (homOfLE (inf_le_right : U ⊓ V ≤ V)))).app E)))
        (δ.app E) ∈ distTriang (DerivedCategory AddCommGrpCat.{u}) := by
  classical
  let sq : Square (Opens X.carrier) := coverSquare U V hUV
  let squareData := Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u, u}
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O)) sq
  let D := squareData.sectionsData
  let DW := D.functor.obj (op W)
  let DU := D.functor.obj (op U)
  let DV := D.functor.obj (op V)
  let DUV := D.functor.obj (op (U ⊓ V))
  have hDW : DW.IsRightDerivedFunctor (D.unit W)
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) :=
    D.isRightDerivedFunctor W
  have hDU : DU.IsRightDerivedFunctor (D.unit U)
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) :=
    D.isRightDerivedFunctor U
  have hDV : DV.IsRightDerivedFunctor (D.unit V)
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) :=
    D.isRightDerivedFunctor V
  have hDUV : DUV.IsRightDerivedFunctor (D.unit (U ⊓ V))
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) :=
    D.isRightDerivedFunctor (U ⊓ V)
  let eW := Functor.rightDerivedUnique RW DW aW (D.unit W)
    (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))
  let eU := Functor.rightDerivedUnique RU DU aU (D.unit U)
    (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))
  let eV := Functor.rightDerivedUnique RV DV aV (D.unit V)
    (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))
  let eUV := Functor.rightDerivedUnique RUV DUV aUV (D.unit (U ⊓ V))
    (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))
  have heW : aW ≫ DerivedCategory.Q.whiskerLeft eW.hom = D.unit W :=
    (Functor.rightDerivedNatTrans_fac RW DW aW (D.unit W)
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) (𝟙 _)).trans
      (Category.id_comp _)
  have heU : aU ≫ DerivedCategory.Q.whiskerLeft eU.hom = D.unit U :=
    (Functor.rightDerivedNatTrans_fac RU DU aU (D.unit U)
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) (𝟙 _)).trans
      (Category.id_comp _)
  have heV : aV ≫ DerivedCategory.Q.whiskerLeft eV.hom = D.unit V :=
    (Functor.rightDerivedNatTrans_fac RV DV aV (D.unit V)
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) (𝟙 _)).trans
      (Category.id_comp _)
  have heUV : aUV ≫ DerivedCategory.Q.whiskerLeft eUV.hom = D.unit (U ⊓ V) :=
    (Functor.rightDerivedNatTrans_fac RUV DUV aUV (D.unit (U ⊓ V))
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) (𝟙 _)).trans
      (Category.id_comp _)
  have hunit : ∀ {Z Z' : Opens X.carrier} (f : Z ⟶ Z'),
      sectionsRestrictionDerived X f ≫ D.unit Z =
        D.unit Z' ≫ DerivedCategory.Q.whiskerLeft (D.functor.map f.op) := by
    intro Z Z' f
    refine NatTrans.ext (funext fun K => ?_)
    change DerivedCategory.Q.map ((MayerVietoris.sectionsRestrictionComplex.{u, u, u, u}
          (ringedSite X) f).app K) ≫ (D.unit Z).app K =
      (D.unit Z').app K ≫ (D.functor.map f.op).app (DerivedCategory.Q.obj K)
    exact D.unit_restriction f K
  have hWU : RW.rightDerivedNatTrans RU aW aU
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))
      (sectionsRestrictionDerived X (homOfLE (le_sup_left.trans hUV.le : U ≤ W))) ≫ eU.hom =
      eW.hom ≫ D.functor.map sq.f₃₄.op :=
    rightDerivedNatTrans_comp_unique
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) aW aU (D.unit W)
      (D.unit U) _ _ eW eU heW heU (hunit sq.f₃₄)
  have hWV : RW.rightDerivedNatTrans RV aW aV
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))
      (sectionsRestrictionDerived X (homOfLE (le_sup_right.trans hUV.le : V ≤ W))) ≫ eV.hom =
      eW.hom ≫ D.functor.map sq.f₂₄.op :=
    rightDerivedNatTrans_comp_unique
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) aW aV (D.unit W)
      (D.unit V) _ _ eW eV heW heV (hunit sq.f₂₄)
  have hUUV : RU.rightDerivedNatTrans RUV aU aUV
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))
      (sectionsRestrictionDerived X (homOfLE (inf_le_left : U ⊓ V ≤ U))) ≫ eUV.hom =
      eU.hom ≫ D.functor.map sq.f₁₃.op :=
    rightDerivedNatTrans_comp_unique
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) aU aUV (D.unit U)
      (D.unit (U ⊓ V)) _ _ eU eUV heU heUV (hunit sq.f₁₃)
  have hVUV : RV.rightDerivedNatTrans RUV aV aUV
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))
      (sectionsRestrictionDerived X (homOfLE (inf_le_right : U ⊓ V ≤ V))) ≫ eUV.hom =
      eV.hom ≫ D.functor.map sq.f₁₂.op :=
    rightDerivedNatTrans_comp_unique
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) aV aUV (D.unit V)
      (D.unit (U ⊓ V)) _ _ eV eUV heV heUV (hunit sq.f₁₂)
  have hc : IsIso squareData.derivedCSquare := isIso_derivedCSquare_coverSquare X U V hUV
  refine ⟨eUV.hom ≫ (squareData.boundary ≫ Functor.whiskerRight
      (inv squareData.derivedCSquare)
      (shiftFunctor (DerivedCategory AddCommGrpCat.{u}) (1 : ℤ))) ≫
    Functor.whiskerRight eW.inv (shiftFunctor (DerivedCategory AddCommGrpCat.{u}) (1 : ℤ)), ?_⟩
  intro E
  have hES : squareData.IsCSquareIso E :=
    ⟨⟨(inv squareData.derivedCSquare).app E,
      by rw [← NatTrans.comp_app, IsIso.hom_inv_id, NatTrans.id_app],
      by rw [← NatTrans.comp_app, IsIso.inv_hom_id, NatTrans.id_app]⟩⟩
  refine distTriang_of_comparison RW RU RV RUV DW DU DV DUV _ _ _ _
    (D.functor.map sq.f₃₄.op) (D.functor.map sq.f₂₄.op) (D.functor.map sq.f₁₃.op)
    (D.functor.map sq.f₁₂.op) eW eU eV eUV hWU hWV hUUV hVUV E
    (squareData.cSquareTriangle E).mor₃ _ ?_
    (Stacks.MayerVietoris.CanonicalMapOfComplexes.cSquareTriangle_distinguished.{u, u}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O)) sq E)
  have hmor₃ : (squareData.cSquareTriangle E).mor₃ =
      squareData.boundary.app E ≫
        (shiftFunctor (DerivedCategory AddCommGrpCat.{u}) (1 : ℤ)).map
          ((inv squareData.derivedCSquare).app E) := by
    rw [NatIso.isIso_inv_app]
    rfl
  rw [hmor₃]
  rfl

/-- **Stacks 08BX.** Let `X` be a ringed space covered by two open subsets `U` and `V`.  For
any choice of derived sections functors over `X`, `U`, `V` and `U ∩ V` — that is, any right
derived functors of degreewise sections along the quasi-isomorphisms — the right-derived
restriction maps, with the usual sign on the overlap, fit into a distinguished triangle in the
derived category of abelian groups, naturally in the object of `D(𝒪_X)`: the connecting map is
a natural transformation and the other four maps are natural transformations of the given
functors.  The functorial Mayer--Vietoris long exact cohomology sequence obtained from the
triangle is `Stacks.Cohomology.LinearMayerVietoris.linearUnboundedMayerVietoris_longExact`. -/
@[stacks 08BX "the triangle, in the derived category of abelian groups"]
public theorem unboundedMayerVietoris (X : RingedSpace.{u, u}) (U V : Opens X.carrier)
    (hUV : U ⊔ V = ⊤)
    (RX RU RV RUV : DerivedCategory (ModuleSheaves X) ⥤ DerivedCategory AddCommGrpCat.{u})
    (aX : sectionsComplexDerived X ⊤ ⟶ DerivedCategory.Q ⋙ RX)
    (aU : sectionsComplexDerived X U ⟶ DerivedCategory.Q ⋙ RU)
    (aV : sectionsComplexDerived X V ⟶ DerivedCategory.Q ⋙ RV)
    (aUV : sectionsComplexDerived X (U ⊓ V) ⟶ DerivedCategory.Q ⋙ RUV)
    [RX.IsRightDerivedFunctor aX
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RU.IsRightDerivedFunctor aU
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RV.IsRightDerivedFunctor aV
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RUV.IsRightDerivedFunctor aUV
      (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))] :
    ∃ δ : RUV ⟶ RX ⋙ shiftFunctor (DerivedCategory AddCommGrpCat.{u}) (1 : ℤ),
      ∀ E, Triangle.mk
        (biprod.lift
          ((RX.rightDerivedNatTrans RU aX aU
            (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))
            (sectionsRestrictionDerived X (homOfLE (le_top : U ≤ ⊤)))).app E)
          ((RX.rightDerivedNatTrans RV aX aV
            (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))
            (sectionsRestrictionDerived X (homOfLE (le_top : V ≤ ⊤)))).app E))
        (biprod.desc
          ((RU.rightDerivedNatTrans RUV aU aUV
            (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))
            (sectionsRestrictionDerived X (homOfLE (inf_le_left : U ⊓ V ≤ U)))).app E)
          (-((RV.rightDerivedNatTrans RUV aV aUV
            (HomologicalComplex.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))
            (sectionsRestrictionDerived X (homOfLE (inf_le_right : U ⊓ V ≤ V)))).app E)))
        (δ.app E) ∈ distTriang (DerivedCategory AddCommGrpCat.{u}) :=
  relativeUnboundedMayerVietoris X U V ⊤ hUV RX RU RV RUV aX aU aV aUV

end Stacks.Cohomology.SpaceMayerVietoris

end
