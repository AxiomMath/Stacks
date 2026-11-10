module

public import StacksFrontier.Cotangent.ThreefoldTowerFibre
public import Mathlib.Algebra.Homology.AlternatingConst
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.PointResolutionProjectivity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.MooreCochainComplex

/-!
# Acyclicity on the fibres of `u₃`

Let `A → B → C` be ring maps and `u₃ : C_{C/B/A} ⥤ C_{C/B}` the functor of Tag 08QT. The left
Kan extension along `u₃` of an abelian presheaf `𝒢` on `C_{C/B/A}`, evaluated at `(Q̄ → C)`, is
the colimit of `𝒢` over the fibre of `u₃` over `(Q̄ → C)`, which is the site `C_{Q̄/B/A}` of
towers over `Q̄` (`StacksFrontier.Cotangent.ThreefoldTowerFibre`). This file introduces the class
of presheaves on which that colimit is computed without correction by the point resolution of the
fibre, and proves what Stacks 0794 asks of it:

* it contains the presheaves `g₃⁻¹𝒩` pulled back from `C_{C/B}`, which are constant on the point
  resolution (this is where Tag 08QV enters);
* it contains, after restriction to every fibre, the projective presheaves, so every abelian
  presheaf on `C_{C/B/A}` is a quotient of a member;
* a bounded above acyclic complex of members has acyclic colimit over every fibre.

## Main definitions

* `CommAlgCat.fibreRestriction`: restriction of abelian presheaves on `C_{C/B/A}` to the small
  model of the fibre of `u₃` over `(Q̄ → C)`.
* `CommAlgCat.IsFibreAcyclic`: the presheaves whose restriction to every fibre has vanishing
  positive homology on the point resolution of Tag 08QV.

## Main results

* `Stacks.ChaoticSite.projective_proj_comp_freeYoneda`: restriction of a free diagram along the
  projection of a category of costructured arrows is projective.
* `CommAlgCat.isFibreAcyclic_inverseImage`: presheaves pulled back from `C_{C/B}` are acyclic on
  the fibres.
* `CommAlgCat.exists_epi_isFibreAcyclic`: every abelian presheaf is a quotient of one acyclic on
  the fibres.
* `CommAlgCat.acyclic_colim_fibreRestriction`: the colimit over a fibre of a bounded above acyclic
  complex of presheaves acyclic on the fibres is acyclic.

## References

* [Stacks Project, Tag 08QW](https://stacks.math.columbia.edu/tag/08QW)
* [Stacks Project, Tag 08QV](https://stacks.math.columbia.edu/tag/08QV)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.ChaoticSite

universe v₁ u₁ v₂ u₂ vD uD

section ProjectiveRestriction

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y] (L : Xᵒᵖ ⥤ Y) (y : Y)
  {D : Type uD} [Category.{vD} D] [HasCoproducts.{v₁} D] [HasPushouts D]

omit [HasCoproducts D] [HasPushouts D] in
/-- Two morphisms out of costructured arrows `L(op W) ⟶ y` with the same structure map and the
same underlying morphism agree after any functor. -/
lemma map_costructuredArrow_eq {F : CostructuredArrow L y ⥤ D} {M : D} {W : X}
    {j : CostructuredArrow L y}
    {ψ₁ ψ₂ : L.obj (op W) ⟶ y} (h : ψ₁ = ψ₂)
    (l : ∀ ψ : L.obj (op W) ⟶ y, M ⟶ F.obj (CostructuredArrow.mk ψ))
    (n₁ : CostructuredArrow.mk ψ₁ ⟶ j) (n₂ : CostructuredArrow.mk ψ₂ ⟶ j)
    (hn : n₁.left = n₂.left) : l ψ₁ ≫ F.map n₁ = l ψ₂ ≫ F.map n₂ := by
  subst h
  congr 2
  exact CostructuredArrow.hom_ext _ _ hn

/-- **Restriction of a free diagram along the projection of costructured arrows is projective.**
The projection `CostructuredArrow L y ⥤ Xᵒᵖ` has unique lifts of morphisms out of the source of
a costructured arrow, so the restricted free diagram on `W` is free on the costructured arrows
`L(op W) ⟶ y`; a lifting problem against it is solved at each of these by projectivity of the
coefficients, and the solutions spread to every object by functoriality. -/
theorem projective_proj_comp_freeYoneda (W : X) (M : D) [Projective M] :
    Projective (CostructuredArrow.proj L y ⋙ Presheaf.freeYoneda W M) where
  factors {F₁ F₂} f e _ := by
    let G := CostructuredArrow.proj L y ⋙ Presheaf.freeYoneda W M
    let ι : ∀ (j : CostructuredArrow L y) (a : (yoneda.obj W).obj j.left), M ⟶ G.obj j :=
      fun _ a => Sigma.ι (fun _ => M) a
    have hι : ∀ {j j' : CostructuredArrow L y} (k : j ⟶ j') (a : (yoneda.obj W).obj j.left),
        ι j a ≫ G.map k = ι j' ((yoneda.obj W).map k.left a) := fun k a =>
      (Sigma.ι_comp_map' _ _ _).trans (Category.id_comp _)
    have hext : ∀ {j : CostructuredArrow L y} {T : D} (g₁ g₂ : G.obj j ⟶ T),
        (∀ a, ι j a ≫ g₁ = ι j a ≫ g₂) → g₁ = g₂ := fun g₁ g₂ h => Sigma.hom_ext _ _ h
    have he : ∀ j, Epi (e.app j) := fun j => inferInstance
    let l : ∀ ψ : L.obj (op W) ⟶ y, M ⟶ F₁.obj (CostructuredArrow.mk ψ) := fun ψ =>
      Projective.factorThru (ι (CostructuredArrow.mk ψ) (𝟙 W) ≫ f.app (CostructuredArrow.mk ψ))
        (e.app (CostructuredArrow.mk ψ))
    let app : ∀ j : CostructuredArrow L y, G.obj j ⟶ F₁.obj j := fun j =>
      Sigma.desc (fun a : (yoneda.obj W).obj j.left =>
        l (L.map a.op ≫ j.hom) ≫ F₁.map (CostructuredArrow.homMk a.op rfl))
    have happ : ∀ (j : CostructuredArrow L y) (a : (yoneda.obj W).obj j.left),
        ι j a ≫ app j = l (L.map a.op ≫ j.hom) ≫ F₁.map (CostructuredArrow.homMk a.op rfl) :=
      fun j a => Sigma.ι_comp_desc _ _
    refine ⟨{ app := app, naturality := fun j j' k => ?_ }, ?_⟩
    · refine hext _ _ fun a => ?_
      rw [← Category.assoc, hι, happ, ← Category.assoc, happ, Category.assoc, ← F₁.map_comp]
      refine map_costructuredArrow_eq L y ?_ l _ _ rfl
      change L.map (k.left.unop ≫ a).op ≫ j'.hom = L.map a.op ≫ j.hom
      rw [op_comp, Quiver.Hom.op_unop, L.map_comp, Category.assoc, CostructuredArrow.w k]
    · ext j
      refine hext _ _ fun a => ?_
      rw [NatTrans.comp_app, ← Category.assoc, happ, Category.assoc, NatTrans.naturality,
        ← Category.assoc, Projective.factorThru_comp, Category.assoc,
        ← f.naturality, ← Category.assoc, hι]
      congr 2
      exact Category.comp_id a

end ProjectiveRestriction

end Stacks.ChaoticSite

namespace Stacks.ChaoticSite

section Acyclic

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜]

/-- A complex quasi-isomorphic to an acyclic complex is acyclic. -/
lemma acyclic_of_quasiIso {K L : CochainComplex 𝒜 ℤ} (g : K ⟶ L) [QuasiIso g]
    (hK : K.Acyclic) : L.Acyclic := fun i => by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hK i).isZero_homology.of_iso
    (asIso (HomologicalComplex.homologyMap g i)).symm

/-- A complex quasi-isomorphic to an acyclic complex is acyclic. -/
lemma acyclic_of_quasiIso' {K L : CochainComplex 𝒜 ℤ} (g : K ⟶ L) [QuasiIso g]
    (hL : L.Acyclic) : K.Acyclic := fun i => by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hL i).isZero_homology.of_iso (asIso (HomologicalComplex.homologyMap g i))

/-- The morphism from an acyclic complex to a zero complex is a quasi-isomorphism. -/
lemma quasiIso_of_acyclic_of_isZero {K L : CochainComplex 𝒜 ℤ} (g : K ⟶ L) (hK : K.Acyclic)
    (hL : IsZero L) : QuasiIso g := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact IsZero.isIso (hK i).isZero_homology
    ((HomologicalComplex.acyclic_of_isZero _ hL i).isZero_homology) _

open ZeroObject in
/-- A functor preserving homology carries acyclic complexes to acyclic complexes. -/
lemma acyclic_map_of_preservesHomology {ℬ : Type*} [Category* ℬ] [Abelian ℬ] (F : 𝒜 ⥤ ℬ)
    [F.Additive] [F.PreservesHomology] {K : CochainComplex 𝒜 ℤ}
    (hK : K.Acyclic) : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  have : QuasiIso (0 : K ⟶ 0) := quasiIso_of_acyclic_of_isZero _ hK (isZero_zero _)
  exact acyclic_of_quasiIso' ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (0 : K ⟶ 0))
    (HomologicalComplex.acyclic_of_isZero _
      (Functor.map_isZero (F.mapHomologicalComplex (ComplexShape.up ℤ)) (isZero_zero _)))

end Acyclic

end Stacks.ChaoticSite

namespace CommAlgCat

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  (U : PolynomialAugmentation B (towerRelativeAlgebra B C))

variable (A) in
/-- The small model of the site of towers over `Q̄`, read in the costructured arrows of `u₃` over
`(Q̄ → C)`: an equivalence. -/
def fibreSiteToCostructured :
    (FibreSite A U)ᵒᵖ ⥤ CostructuredArrow (polynomialTowerThird A B C).op (op (op U)) :=
  (AsSmall.down).op ⋙ (opOpEquivalence _).functor ⋙ fibreTowerCostructured A B C U

/-- The functor `fibreSiteToCostructured A U` is an equivalence of categories. -/
instance : (fibreSiteToCostructured A U).IsEquivalence := by
  have : (AsSmall.down : FibreSite A U ⥤ _).IsEquivalence :=
    (AsSmall.equiv (C := polynomialTowerSite A B (fibreAlgebra U))).isEquivalence_inverse
  have : (AsSmall.down : FibreSite A U ⥤ _).op.IsEquivalence :=
    (AsSmall.equiv (C := polynomialTowerSite A B (fibreAlgebra U))).op.isEquivalence_inverse
  dsimp only [fibreSiteToCostructured]
  infer_instance

variable (A) in
/-- The small model of the fibre of `u₃` over `(Q̄ → C)`, mapped to `C_{C/B/A}`. -/
abbrev fibreSiteToSite : (FibreSite A U)ᵒᵖ ⥤ (polynomialTowerSite A B C)ᵒᵖ :=
  fibreSiteToCostructured A U ⋙ CostructuredArrow.proj _ _

variable (A) in
/-- Restriction of abelian presheaves on `C_{C/B/A}` to the small model of the fibre of `u₃` over
`(Q̄ → C)`. -/
abbrev fibreRestriction :
    ((polynomialTowerSite A B C)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
      ((FibreSite A U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  (Functor.whiskeringLeft _ _ _).obj (fibreSiteToSite A U)

variable (A B C) in
/-- **Acyclicity on the fibres of `u₃`.** An abelian presheaf on `C_{C/B/A}` is acyclic on the
fibres of `u₃` when, for every object `(Q̄ → C)` of `C_{C/B}`, its restriction to the fibre has
vanishing positive homology on the point resolution of Tag 08QV. -/
def IsFibreAcyclic : ObjectProperty ((polynomialTowerSite A B C)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  fun G => ∀ (U : PolynomialAugmentation B (towerRelativeAlgebra B C)) (n : ℕ),
    IsZero (((Stacks.ChaoticSite.cosimplicialMooreComplex (fibreSmallCosimplicial A U)).obj
      ((fibreRestriction A U).obj G)).homology (n + 1))

variable (A) in
/-- Restriction to a fibre followed by the homology of the point resolution, a functor of the
abelian presheaf on `C_{C/B/A}`. -/
abbrev fibreHomologyFunctor (n : ℕ) :
    ((polynomialTowerSite A B C)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤ AddCommGrpCat.{u + 1} :=
  fibreRestriction A U ⋙
    Stacks.ChaoticSite.cosimplicialMooreComplex (fibreSmallCosimplicial A U) ⋙
      HomologicalComplex.homologyFunctor _ _ n

open ZeroObject in
/-- The property of being acyclic on the fibres of `u₃` holds for some zero presheaf. -/
instance : (IsFibreAcyclic A B C).ContainsZero :=
  ⟨⟨0, isZero_zero _, fun U n => Functor.map_isZero (fibreHomologyFunctor A U (n + 1))
    (isZero_zero _)⟩⟩

/-- Acyclicity on the fibres of `u₃` is invariant under isomorphism. -/
lemma isFibreAcyclic_of_iso {G G' : (polynomialTowerSite A B C)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (e : G ≅ G') (h : IsFibreAcyclic A B C G) : IsFibreAcyclic A B C G' := fun U n =>
  (h U n).of_iso ((fibreHomologyFunctor A U (n + 1)).mapIso e).symm

/-- A zero presheaf is acyclic on the fibres of `u₃`. -/
lemma isFibreAcyclic_of_isZero {G : (polynomialTowerSite A B C)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (h : IsZero G) : IsFibreAcyclic A B C G := fun U n =>
  Functor.map_isZero (fibreHomologyFunctor A U (n + 1)) h

/-- **Acyclicity on the fibres of `u₃` is closed under finite direct sums.** -/
lemma isFibreAcyclic_biprod {G G' : (polynomialTowerSite A B C)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (h : IsFibreAcyclic A B C G) (h' : IsFibreAcyclic A B C G') :
    IsFibreAcyclic A B C (G ⊞ G') := fun U n => by
  let T := fibreHomologyFunctor A U (n + 1)
  have hG : IsZero (T.obj G) := h U n
  have hG' : IsZero (T.obj G') := h' U n
  change IsZero (T.obj (G ⊞ G'))
  rw [IsZero.iff_id_eq_zero, ← T.map_id, ← biprod.total, T.map_add, T.map_comp, T.map_comp,
    hG.eq_of_tgt (T.map biprod.fst) 0, hG'.eq_of_tgt (T.map biprod.snd) 0, zero_comp, zero_comp,
    add_zero]

/-- The towers of the point resolution of the fibre, read in `C_{C/B/A}`, are carried by `u₃` to
`(Q̄ → C)` through isomorphisms. -/
instance isIso_fibreResolution_hom (n : SimplexCategoryᵒᵖ) :
    IsIso ((fibreResolutionCostructured A U).obj n).hom := by
  have h₁ := isIso_fibreTowerBaseChange_simplicial A U (op n.unop)
  have h₂ : IsIso (fibreTowerBaseChange U ((fibreTowerSimplicial A U).obj (op n.unop))).op :=
    inferInstance
  exact isIso_op (fibreTowerBaseChange U ((fibreTowerSimplicial A U).obj (op n.unop))).op

/-- **The restriction of a presheaf pulled back from `C_{C/B}` to the point resolution of a
fibre of `u₃` is constant**, with value the sections over `(Q̄ → C)`. -/
def fibreResolutionInverseImageIso (N : (polynomialSite B (towerRelativeAlgebra B C))ᵒᵖ ⥤
    AddCommGrpCat.{u + 1}) :
    (fibreSmallCosimplicial A U).op ⋙ (fibreRestriction A U).obj
        ((polynomialTowerThird A B C).op ⋙ N) ≅
      (Functor.const SimplexCategoryᵒᵖ).obj (N.obj (op (op U))) :=
  NatIso.ofComponents
    (fun n => N.mapIso (@asIso _ _ _ _ ((fibreResolutionCostructured A U).obj n).hom
      (isIso_fibreResolution_hom U n))) (fun {n m} f => by
    change N.map _ ≫ N.map _ = N.map _ ≫ 𝟙 _
    rw [Category.comp_id, ← N.map_comp]
    congr 1
    exact CostructuredArrow.w ((fibreResolutionCostructured A U).map f))

/-- **Presheaves pulled back from `C_{C/B}` are acyclic on the fibres of `u₃`**: on the point
resolution of a fibre they are constant. -/
theorem isFibreAcyclic_inverseImage (N : (polynomialSite B (towerRelativeAlgebra B C))ᵒᵖ ⥤
    AddCommGrpCat.{u + 1}) :
    IsFibreAcyclic A B C ((polynomialTowerThird A B C).op ⋙ N) := fun U n => by
  refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso
    ((AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u + 1}).mapIso
      (fibreResolutionInverseImageIso U N) ≪≫
      AlgebraicTopology.alternatingFaceMapComplexConst.app (N.obj (op (op U)))))
  exact (ChainComplex.alternatingConst_exactAt _ (n + 1) (Nat.succ_ne_zero n)).isZero_homology

/-- **Restriction to a fibre of `u₃` carries free presheaves to projective presheaves.** -/
instance projective_fibreRestriction_freeYoneda (W : polynomialTowerSite A B C)
    (M : AddCommGrpCat.{u + 1}) [Projective M] :
    Projective ((fibreRestriction A U).obj (Presheaf.freeYoneda W M)) := by
  have h := Stacks.ChaoticSite.projective_proj_comp_freeYoneda
    (polynomialTowerThird A B C).op (op (op U)) W M
  exact ((fibreSiteToCostructured A U).asEquivalence.symm.congrLeft.map_projective_iff
    (CostructuredArrow.proj _ _ ⋙ Presheaf.freeYoneda W M)).2 h

/-- An abelian presheaf whose restrictions to the fibres of `u₃` are projective is acyclic on
the fibres, by Tag 08Q9 for the point resolution of each fibre. -/
theorem isFibreAcyclic_of_projective (G : (polynomialTowerSite A B C)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (h : ∀ U : PolynomialAugmentation B (towerRelativeAlgebra B C),
      Projective ((fibreRestriction A U).obj G)) :
    IsFibreAcyclic A B C G := fun U n =>
  have := h U
  Stacks.ChaoticSite.isZero_cosimplicialHomology_projective_succ _
    (isPointResolution_fibreSmallCosimplicial A U) n _

variable (A B C) in
/-- **Every abelian presheaf on `C_{C/B/A}` is a quotient of one acyclic on the fibres of
`u₃`**: the coproduct of the free presheaves on projective covers of its values. -/
theorem exists_epi_isFibreAcyclic (G : (polynomialTowerSite A B C)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    ∃ (G' : (polynomialTowerSite A B C)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
      (_ : IsFibreAcyclic A B C G') (p : G' ⟶ G), Epi p := by
  refine ⟨Stacks.ChaoticSite.freeYonedaPresentationSrc G,
    isFibreAcyclic_of_projective _ fun U => ?_,
    Stacks.ChaoticSite.freeYonedaPresentation G, inferInstance⟩
  exact Projective.of_iso (PreservesCoproduct.iso (fibreRestriction A U)
    (fun W => Presheaf.freeYoneda W (Projective.over (G.obj (op W))))).symm projective_sigma

omit [Algebra A C] [IsScalarTower A B C] in
open StacksDraft.TotalComplexQuasiIso Stacks.ChaoticSite ZeroObject in
/-- **The rows of the double complex of a fibre of `u₃` are acyclic**: for a bounded above
acyclic complex of abelian presheaves on the fibre, the total complex of the double complex
obtained by evaluating it on the point resolution is acyclic. -/
theorem acyclic_total_mooreBicomplex_fibre
    (L : CochainComplex ((FibreSite A U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℤ) (a : ℤ)
    (hLa : ∀ p, a < p → IsZero (L.X p)) (hL : L.Acyclic)
    [(GeneralValued.mooreBicomplex (fibreSmallCosimplicial A U) L).HasTotal (ComplexShape.up ℤ)] :
    (HomologicalComplex₂.total (GeneralValued.mooreBicomplex (fibreSmallCosimplicial A U) L)
      (ComplexShape.up ℤ)).Acyclic := by
  let V := fibreSmallCosimplicial A U
  have hZp : ∀ p, a < p → IsZero ((GeneralValued.mooreBicomplex V L).X p) := fun p hp =>
    GeneralValued.isZero_mooreBicomplex_X V L p (hLa p hp)
  have hZq : ∀ p q, 0 < q → IsZero (((GeneralValued.mooreBicomplex V L).X p).X q) :=
    fun p q hq => GeneralValued.isZero_mooreBicomplex_X_X V L p q hq
  have h0L : IsZero (0 : CochainComplex ((FibreSite A U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℤ) :=
    isZero_zero _
  have hZ₀ : ∀ p q, IsZero (((GeneralValued.mooreBicomplex V
      (0 : CochainComplex ((FibreSite A U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℤ)).X p).X q) :=
    fun p q => Functor.map_isZero (HomologicalComplex.eval _ _ q)
      (GeneralValued.isZero_mooreBicomplex_X V _ p
        (Functor.map_isZero (HomologicalComplex.eval _ _ p) h0L))
  have := hasTotal_of_upperBound (GeneralValued.mooreBicomplex V
      (0 : CochainComplex ((FibreSite A U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℤ)) a 0
    (fun p _ => GeneralValued.isZero_mooreBicomplex_X V _ p
      (Functor.map_isZero (HomologicalComplex.eval _ _ p) h0L)) (fun p q _ => hZ₀ p q)
  have hf : QuasiIso (0 : L ⟶ 0) := quasiIso_of_acyclic_of_isZero _ hL h0L
  have hrow : QuasiIso (HomologicalComplex₂.total.map
      ((GeneralValued.mooreBicomplexFunctor V AddCommGrpCat.{u + 1}).map (0 : L ⟶ 0))
      (ComplexShape.up ℤ)) := by
    refine quasiIso_total_map_of_upperBound_flip _ a 0 (fun p q hpq => ?_)
      (fun p q _ => hZ₀ p q) (fun q => ?_)
    · rcases hpq with hp | hq
      · exact Functor.map_isZero (HomologicalComplex.eval _ _ q) (hZp p hp)
      · exact hZq p q hq
    · change QuasiIso (((GeneralValued.mooreCochainComplex V AddCommGrpCat.{u + 1} ⋙
        HomologicalComplex.eval AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) q).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (0 : L ⟶ 0))
      exact HomologicalComplex.quasiIso_map_of_preservesHomology _ _
  have hTot₀ : (HomologicalComplex₂.total (GeneralValued.mooreBicomplex V
      (0 : CochainComplex ((FibreSite A U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℤ))
        (ComplexShape.up ℤ)).Acyclic := fun n => by
    refine HomologicalComplex.ExactAt.of_isZero ?_
    rw [IsZero.iff_id_eq_zero]
    exact HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ) fun p q _ =>
      (hZ₀ p q).eq_of_src _ _
  exact acyclic_of_quasiIso' (HomologicalComplex₂.total.map
    ((GeneralValued.mooreBicomplexFunctor V AddCommGrpCat.{u + 1}).map (0 : L ⟶ 0))
    (ComplexShape.up ℤ)) hTot₀

open StacksDraft.TotalComplexQuasiIso Stacks.ChaoticSite in
/-- **Stacks 0794's hypothesis for the colimit over a fibre of `u₃`**: a bounded above acyclic
complex of abelian presheaves on `C_{C/B/A}`, acyclic on the fibres of `u₃`, has acyclic colimit
over every fibre. The double complex obtained by evaluating the restriction to the fibre on its
point resolution has acyclic rows, the evaluation being exact, and columns resolving the colimit,
by the acyclicity on the fibres; the two filtrations then make the colimit quasi-isomorphic to
the total complex, which is acyclic. -/
theorem acyclic_colim_fibreRestriction
    (K : CochainComplex ((polynomialTowerSite A B C)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℤ) (a : ℤ)
    (hKa : ∀ p, a < p → IsZero (K.X p)) (hK : ∀ p, IsFibreAcyclic A B C (K.X p))
    (hac : K.Acyclic) :
    ((((fibreRestriction A U).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
      ((colim : ((FibreSite A U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
        AddCommGrpCat.{u + 1}).mapHomologicalComplex (ComplexShape.up ℤ))).obj K).Acyclic := by
  let V := fibreSmallCosimplicial A U
  let L := ((fibreRestriction A U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have hLa : ∀ p, a < p → IsZero (L.X p) := fun p hp =>
    Functor.map_isZero (fibreRestriction A U) (hKa p hp)
  have hZp : ∀ p, a < p → IsZero ((GeneralValued.mooreBicomplex V L).X p) := fun p hp =>
    GeneralValued.isZero_mooreBicomplex_X V L p (hLa p hp)
  have hZq : ∀ p q, 0 < q → IsZero (((GeneralValued.mooreBicomplex V L).X p).X q) :=
    fun p q hq => GeneralValued.isZero_mooreBicomplex_X_X V L p q hq
  have := hasTotal_of_upperBound _ a 0 hZp hZq
  have hZ'p : ∀ p, a < p → IsZero ((singleRowZero
      (((colim : ((FibreSite A U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
        AddCommGrpCat.{u + 1}).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).X p) :=
    fun p hp => GeneralValued.isZero_singleRowZeroColim_X L p (hLa p hp)
  have hZ'q : ∀ p q, 0 < q → IsZero (((singleRowZero
      (((colim : ((FibreSite A U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
        AddCommGrpCat.{u + 1}).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).X p).X q) :=
    fun p q hq => GeneralValued.isZero_singleRowZeroColim_X_X L p q hq
  have := hasTotal_of_upperBound _ a 0 hZ'p hZ'q
  have hcol : QuasiIso (HomologicalComplex₂.total.map
      (GeneralValued.mooreBicomplexColumnMap V L) (ComplexShape.up ℤ)) :=
    quasiIso_total_map_of_upperBound _ a 0 hZp hZq hZ'p hZ'q fun p =>
      GeneralValued.quasiIso_mooreCochainAugmentation V (L.X p) (fun n => hK p U n)
        (colimitι_isColimit V (isPointResolution_fibreSmallCosimplicial A U) (L.X p))
  have := isIso_totalSingleRowZeroUnit
    (((colim : ((FibreSite A U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
      AddCommGrpCat.{u + 1}).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
  exact acyclic_of_quasiIso' (totalSingleRowZeroUnit
    (((colim : ((FibreSite A U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
      AddCommGrpCat.{u + 1}).mapHomologicalComplex (ComplexShape.up ℤ)).obj L))
    (acyclic_of_quasiIso (HomologicalComplex₂.total.map
      (GeneralValued.mooreBicomplexColumnMap V L) (ComplexShape.up ℤ))
      (acyclic_total_mooreBicomplex_fibre U L a hLa
        (acyclic_map_of_preservesHomology (fibreRestriction A U) hac)))

end CommAlgCat

end
