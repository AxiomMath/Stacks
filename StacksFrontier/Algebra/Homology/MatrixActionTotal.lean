module

public import Mathlib.CategoryTheory.Abelian.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.MapBifunctorNatIso
public import StacksFrontier.Algebra.Homology.MatrixAction
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Homology.TotalComplexTransport

/-!
# Tensoring a complex with a bounded complex of finite free modules, in a linear category

Let `A` be a commutative ring and `C` an `A`-linear category with finite biproducts.  A bounded
complex `Q` of finite free `A`-modules with chosen bases is a bounded cochain complex in
`Mat_ (SingleObj A)`.  For a cochain complex `K` of `C` the total complex

`Tot(K ⊗_A Q) = Tot(matrixAction A (K, Q))`,

whose term in degree `n` is `⨁_{p + q = n} ⨁_{ι_q} Kᵖ`, is the tensor product of `K` with `Q`
over `A`.  It is formed in `C` with no monoidal structure and no infinite colimit: since `Q` is
bounded, only finitely many summands are nonzero in each degree.

This file proves the two facts that make it useful.

* **Exactness.**  When `C` is abelian, `Tot(- ⊗_A Q)` preserves quasi-isomorphisms: a bounded
  complex of finite free modules is K-flat for the matrix action
  (`CochainComplex.KFlatBifunctor`), because tensoring with one finite free module is a finite
  direct sum, which is exact.
* **Linearity.**  An additive `A`-linear functor `G : C ⥤ D` commutes with it,
  `G(Tot(K ⊗_A Q)) ≅ Tot(G(K) ⊗_A Q)`.  An additive functor preserves the coproducts in the
  total complex because only finitely many of their summands are nonzero.

## Main definitions

* `CategoryTheory.MatrixAction.tot`: the functor `K ↦ Tot(K ⊗_A Q)` on cochain complexes.
* `CategoryTheory.MatrixAction.totCompIso`: `G(Tot(K ⊗_A Q)) ≅ Tot(G(K) ⊗_A Q)`, naturally in `K`.

## Main results

* `CategoryTheory.MatrixAction.kFlat_of_bounded`: a bounded complex of finite free modules is
  K-flat for the matrix action.
* `CategoryTheory.MatrixAction.quasiIso_tot_map`: `Tot(- ⊗_A Q)` preserves quasi-isomorphisms.
* `CategoryTheory.Limits.isColimitCofanExtend` and
  `CategoryTheory.Limits.preservesColimit_discrete_of_isZero`: a coproduct of a family whose
  terms vanish off a finite set is the finite coproduct of the remaining terms, and so is
  preserved by every additive functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The cofan over a family `f : J → C` obtained from a cofan over its restriction to a subset
`S` by mapping the remaining terms in by zero. -/
abbrev cofanExtend {J : Type*} (f : J → C) (S : Set J) [DecidablePred (· ∈ S)]
    (c : Cofan fun s : S => f s) : Cofan f :=
  Cofan.mk c.pt fun j => if h : j ∈ S then c.inj ⟨j, h⟩ else 0

/-- **A coproduct of a family vanishing off a subset `S` is the coproduct over `S`.** -/
def isColimitCofanExtend {J : Type*} (f : J → C) (S : Set J) [DecidablePred (· ∈ S)]
    (hz : ∀ j ∉ S, IsZero (f j)) {c : Cofan fun s : S => f s} (hc : IsColimit c) :
    IsColimit (cofanExtend f S c) :=
  Cofan.IsColimit.mk _ (fun s => Cofan.IsColimit.desc hc fun x => s.inj x.1)
    (fun s j => by
      by_cases h : j ∈ S
      · simp only [cofanExtend, cofan_mk_inj, dite_eq_left h]
        exact Cofan.IsColimit.fac hc _ ⟨j, h⟩
      · simp only [cofanExtend, cofan_mk_inj, dite_eq_right h, zero_comp]
        exact (hz j h).eq_of_src _ _)
    (fun s m hm => Cofan.IsColimit.hom_ext hc _ _ fun x => by
      rw [Cofan.IsColimit.fac]
      have := hm x.1
      simp only [cofanExtend, cofan_mk_inj, dite_eq_left x.2] at this
      exact this)

variable {D : Type*} [Category D] [HasZeroMorphisms D]

/-- **A functor preserving zero morphisms and finite coproducts preserves every coproduct of a
family whose terms vanish off a finite set.** -/
lemma preservesColimit_discrete_of_isZero {J : Type*} (f : J → C) (S : Set J) [Finite S]
    (hz : ∀ j ∉ S, IsZero (f j)) [HasCoproduct fun s : S => f s] (Φ : C ⥤ D)
    [Φ.PreservesZeroMorphisms] [PreservesColimitsOfShape (Discrete S) Φ] :
    PreservesColimit (Discrete.functor f) Φ := by
  classical
  let c : Cofan fun s : S => f s := colimit.cocone _
  have hc : IsColimit c := colimit.isColimit _
  refine preservesColimit_of_preserves_colimit_cocone (isColimitCofanExtend f S hz hc) ?_
  refine (isColimitMapCoconeCofanMkEquiv Φ _ _).symm ?_
  have hΦc : IsColimit (Cofan.mk (Φ.obj c.pt) fun s : S => Φ.map (c.inj s)) :=
    isColimitMapCoconeCofanMkEquiv Φ _ _ (isColimitOfPreserves Φ hc)
  refine IsColimit.ofIsoColimit (isColimitCofanExtend (Φ.obj ∘ f) S
    (fun j hj => Φ.map_isZero (hz j hj)) hΦc) (Cofan.ext (Iso.refl _) fun j => ?_)
  by_cases h : j ∈ S <;> simp [cofanExtend, h]

end CategoryTheory.Limits

namespace CategoryTheory.MatrixAction

variable (A : Type w) [CommRing A]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear A C] [HasFiniteBiproducts C]

/-- **`K ↦ Tot(K ⊗_A Q)`**, the total complex of the matrix action of a complex `Q` of finite
free `A`-modules with chosen bases on a complex `K` of `C`. -/
abbrev tot [∀ (K : CochainComplex C ℤ) (Q : CochainComplex (Mat_ (SingleObj A)) ℤ),
      HomologicalComplex.HasMapBifunctor K Q (matrixAction A (C := C)) (ComplexShape.up ℤ)]
    (Q : CochainComplex (Mat_ (SingleObj A)) ℤ) :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  ((matrixAction A).map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).flip.obj Q

end CategoryTheory.MatrixAction

namespace CategoryTheory.MatrixAction

variable (A : Type w) [CommRing A]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts Abelian.hasFiniteBiproducts

section Exactness

variable {C : Type u} [Category.{v} C] [Abelian C] [Linear A C]
  [∀ (K : CochainComplex C ℤ) (Q : CochainComplex (Mat_ (SingleObj A)) ℤ),
      HomologicalComplex.HasMapBifunctor K Q (matrixAction A (C := C)) (ComplexShape.up ℤ)]

/-- Tensoring with one finite free module, placed in one degree, carries acyclic complexes to
acyclic complexes: it is a finite direct sum of copies of the complex. -/
lemma kFlat_single (M : Mat_ (SingleObj A)) (q : ℤ) :
    CochainComplex.KFlatBifunctor.KFlat (matrixAction A (C := C))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj M) :=
  CochainComplex.KFlatBifunctor.kFlat_single_of_exact _ M q fun _ hG =>
    HomologicalComplex.Acyclic.map ((matrixAction A (C := C)).flip.obj M) hG

/-- **A bounded complex of finite free `A`-modules is K-flat for the matrix action.** -/
theorem kFlat_of_bounded (Q : CochainComplex (Mat_ (SingleObj A)) ℤ) (a b : ℤ)
    [Q.IsStrictlyLE b] [Q.IsStrictlyGE a] :
    CochainComplex.KFlatBifunctor.KFlat (matrixAction A (C := C)) Q :=
  CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE_of_isStrictlyGE _ Q b a fun q =>
    kFlat_single A (Q.X q) q

/-- **Tensoring with a bounded complex of finite free `A`-modules preserves
quasi-isomorphisms.** -/
theorem quasiIso_tot_map (Q : CochainComplex (Mat_ (SingleObj A)) ℤ) (a b : ℤ)
    [Q.IsStrictlyLE b] [Q.IsStrictlyGE a] {K L : CochainComplex C ℤ} (f : K ⟶ L)
    [QuasiIso f] : QuasiIso ((tot A Q).map f) :=
  CochainComplex.KFlatBifunctor.quasiIso_of_kFlat _ Q (kFlat_of_bounded A Q a b) f inferInstance

end Exactness

end CategoryTheory.MatrixAction

namespace HomologicalComplex₂

variable {D : Type u} {D' : Type*} [Category.{v} D] [Category D'] [Preadditive D] [Preadditive D']
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₁₂ : ComplexShape I₁₂}
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
  (Φ : D ⥤ D') [Φ.Additive] (K : HomologicalComplex₂ D c₁ c₂)
  [K.HasTotal c₁₂] [(mapBicomplex Φ K).HasTotal c₁₂]

/-- `HomologicalComplex₂.isIso_totalMapf` with the preservation asked for only of the
coproduct which actually occurs in the given total degree. -/
lemma isIso_totalMapf_of_preservesColimit (n : I₁₂)
    [PreservesColimit (Discrete.functor
      (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c₁₂) n)) Φ] :
    IsIso (totalMapf (c₁₂ := c₁₂) Φ K n) := by
  let hc := Cofan.isColimitMapCoconeEquiv Φ _ _
    (isColimitOfPreserves Φ
      (K.toGradedObject.isColimitCofanMapObj (ComplexShape.π c₁ c₂ c₁₂) n))
  let ι' : ∀ i : ↥(ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n}),
      Φ.obj ((K.X i.1.1).X i.1.2) ⟶ ((mapBicomplex Φ K).total c₁₂).X n :=
    fun i => (mapBicomplex Φ K).ιTotal c₁₂ i.1.1 i.1.2 n i.2
  let ψ : Φ.obj ((K.total c₁₂).X n) ⟶ ((mapBicomplex Φ K).total c₁₂).X n :=
    Cofan.IsColimit.desc hc ι'
  have hψ : ∀ i : ↥(ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n}),
      Φ.map (K.ιTotal c₁₂ i.1.1 i.1.2 n i.2) ≫ ψ =
        (mapBicomplex Φ K).ιTotal c₁₂ i.1.1 i.1.2 n i.2 :=
    fun i => Cofan.IsColimit.fac hc _ i
  refine ⟨ψ, ?_, ?_⟩
  · refine HomologicalComplex₂.total.hom_ext c₁₂ (fun i₁ i₂ h => ?_)
    rw [Category.comp_id, ι_totalMapf_assoc]
    exact hψ ⟨(i₁, i₂), h⟩
  · refine Cofan.IsColimit.hom_ext hc _ _ (fun i => ?_)
    change Φ.map (K.ιTotal c₁₂ i.1.1 i.1.2 n i.2) ≫ ψ ≫ totalMapf Φ K n =
      Φ.map (K.ιTotal c₁₂ i.1.1 i.1.2 n i.2) ≫ 𝟙 _
    rw [← Category.assoc, hψ i, Category.comp_id]
    exact ι_totalMapf Φ K n _ _ i.2

/-- `HomologicalComplex₂.totalIso` with the preservation asked for only of the coproducts which
actually occur. -/
def totalIsoOfPreservesColimit
    [∀ n : I₁₂, PreservesColimit (Discrete.functor
      (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c₁₂) n)) Φ] :
    (mapBicomplex Φ K).total c₁₂ ≅ (Φ.mapHomologicalComplex c₁₂).obj (K.total c₁₂) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => @asIso _ _ _ _ (totalMapf (c₁₂ := c₁₂) Φ K n)
      (isIso_totalMapf_of_preservesColimit Φ K n))
    (fun n n' _ => (totalMap Φ K).comm n n')

/-- The inclusion of a summand into the total complex of the transported bicomplex, followed by
`HomologicalComplex₂.totalIsoOfPreservesColimit`, is the image under `Φ` of the inclusion of the
same summand into the total complex of `K`. -/
@[reassoc]
lemma ι_totalIsoOfPreservesColimit_hom
    [∀ n : I₁₂, PreservesColimit (Discrete.functor
      (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c₁₂) n)) Φ] (n : I₁₂) (i₁ : I₁) (i₂ : I₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = n) :
    (mapBicomplex Φ K).ιTotal c₁₂ i₁ i₂ n h ≫ (totalIsoOfPreservesColimit Φ K).hom.f n =
      Φ.map (K.ιTotal c₁₂ i₁ i₂ n h) :=
  ι_totalMapf Φ K n i₁ i₂ h

end HomologicalComplex₂

namespace CategoryTheory.MatrixAction

variable (A : Type w) [CommRing A]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear A C] [HasFiniteBiproducts C]

section Functoriality

variable {D : Type*} [Category D] [Preadditive D] [Linear A D] [HasFiniteBiproducts D]
  (G : C ⥤ D) [G.Additive] [G.Linear A]
  [∀ (K : CochainComplex C ℤ) (Q : CochainComplex (Mat_ (SingleObj A)) ℤ),
      HomologicalComplex.HasMapBifunctor K Q (matrixAction A (C := C)) (ComplexShape.up ℤ)]
  [∀ (K : CochainComplex D ℤ) (Q : CochainComplex (Mat_ (SingleObj A)) ℤ),
      HomologicalComplex.HasMapBifunctor K Q (matrixAction A (C := D)) (ComplexShape.up ℤ)]

omit [∀ (K : CochainComplex C ℤ) (Q : CochainComplex (Mat_ (SingleObj A)) ℤ),
    HomologicalComplex.HasMapBifunctor K Q (matrixAction A (C := C)) (ComplexShape.up ℤ)] in
/-- The terms of the bicomplex of the matrix action of a bounded complex vanish outside the
rows in which the bounded complex lives. -/
lemma isZero_matrixAction_X_X (K : CochainComplex C ℤ) (Q : CochainComplex (Mat_ (SingleObj A)) ℤ)
    (a b : ℤ) [Q.IsStrictlyLE b] [Q.IsStrictlyGE a] (p q : ℤ) (hq : q < a ∨ b < q) :
    IsZero ((((matrixAction A).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj K).obj Q |>.X p |>.X q) := by
  have hQ : IsZero (Q.X q) := by
    rcases hq with hq | hq
    · exact Q.isZero_of_isStrictlyGE a q hq
    · exact Q.isZero_of_isStrictlyLE b q hq
  exact ((matrixAction A).obj (K.X p)).map_isZero hQ

omit [Linear A D] [HasFiniteBiproducts D] [G.Linear A]
  [∀ (K : CochainComplex C ℤ) (Q : CochainComplex (Mat_ (SingleObj A)) ℤ),
    HomologicalComplex.HasMapBifunctor K Q (matrixAction A (C := C)) (ComplexShape.up ℤ)]
  [∀ (K : CochainComplex D ℤ) (Q : CochainComplex (Mat_ (SingleObj A)) ℤ),
    HomologicalComplex.HasMapBifunctor K Q (matrixAction A (C := D)) (ComplexShape.up ℤ)] in
variable {A} in
/-- An additive functor preserves the coproducts occurring in the total complex of the matrix
action of a bounded complex: only finitely many of their terms are nonzero. -/
lemma preservesColimit_matrixAction (K : CochainComplex C ℤ)
    (Q : CochainComplex (Mat_ (SingleObj A)) ℤ) (a b : ℤ) [Q.IsStrictlyLE b] [Q.IsStrictlyGE a]
    (n : ℤ) :
    PreservesColimit (Discrete.functor
      (((((matrixAction A).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).obj Q).toGradedObject.mapObjFun
          (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n)) G := by
  classical
  let S : Set ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹'
      {n}) := {i | a ≤ i.1.2 ∧ i.1.2 ≤ b}
  have hS : S.Finite := by
    refine ((Set.finite_Icc a b).preimage (f := fun i : ↥(ComplexShape.π (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {n}) => i.1.2) ?_).subset fun i hi => hi
    intro i _ j _ hij
    have hi : i.1.1 + i.1.2 = n := i.2
    have hj : j.1.1 + j.1.2 = n := j.2
    have hij' : i.1.2 = j.1.2 := hij
    exact Subtype.ext (Prod.ext (by omega) hij')
  have : Finite S := hS.to_subtype
  exact preservesColimit_discrete_of_isZero _ S (fun i hi => isZero_matrixAction_X_X A K Q a b
    _ _ (by simp only [S, Set.mem_ofPred_eq, not_and_or, not_le] at hi; omega)) G

omit [∀ (K : CochainComplex C ℤ) (Q : CochainComplex (Mat_ (SingleObj A)) ℤ),
    HomologicalComplex.HasMapBifunctor K Q (matrixAction A (C := C)) (ComplexShape.up ℤ)]
  [∀ (K : CochainComplex D ℤ) (Q : CochainComplex (Mat_ (SingleObj A)) ℤ),
    HomologicalComplex.HasMapBifunctor K Q (matrixAction A (C := D)) (ComplexShape.up ℤ)] in
/-- The comparison `G (⨁_ι X) ≅ ⨁_ι G X` is natural in `X`. -/
@[reassoc]
lemma realizeCompIso_hom_naturality {X X' : C} (φ : X ⟶ X') (M : Mat_ (SingleObj A)) :
    G.map ((realizeNatTrans A φ).app M) ≫ (realizeCompIso A G X').hom.app M =
      (realizeCompIso A G X).hom.app M ≫ (realizeNatTrans A (G.map φ)).app M := by
  refine biproduct.hom_ext _ _ fun j => ?_
  simp only [realizeCompIso, NatIso.ofComponents_hom_app, Category.assoc,
    Functor.mapBiproduct_hom, biproduct.lift_π, realizeNatTrans_app, biproduct.map_π,
    biproduct.lift_π_assoc, ← G.map_comp]

/-- **The bicomplex of the matrix action, transported along an additive `A`-linear functor.** -/
def bicomplexCompIso (K : CochainComplex C ℤ) (Q : CochainComplex (Mat_ (SingleObj A)) ℤ) :
    HomologicalComplex₂.mapBicomplex G
        ((((matrixAction A).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj K).obj Q) ≅
      (((matrixAction A).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).obj Q :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents
      (fun q => (realizeCompIso A G (K.X p)).app (Q.X q))
      (fun q q' _ => ((realizeCompIso A G (K.X p)).hom.naturality (Q.d q q')).symm))
    (fun p p' _ => by
      ext q
      exact (realizeCompIso_hom_naturality A G (K.d p p') (Q.X q)).symm)

/-- The bicomplex of the matrix action, transported along `G`, has a total complex: it is
isomorphic to the bicomplex of the matrix action of `G(K)`, which has one. -/
instance hasTotal_mapBicomplex (K : CochainComplex C ℤ)
    (Q : CochainComplex (Mat_ (SingleObj A)) ℤ) :
    (HomologicalComplex₂.mapBicomplex G
        ((((matrixAction A).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj K).obj Q)).HasTotal (ComplexShape.up ℤ) :=
  HomologicalComplex₂.hasTotal_of_iso (bicomplexCompIso A G K Q).symm _

/-- **An additive `A`-linear functor commutes with tensoring by a bounded complex of finite free
`A`-modules**: `G(Tot(K ⊗_A Q)) ≅ Tot(G(K) ⊗_A Q)`. -/
def totCompIso (Q : CochainComplex (Mat_ (SingleObj A)) ℤ) (a b : ℤ) [Q.IsStrictlyLE b]
    [Q.IsStrictlyGE a] (K : CochainComplex C ℤ) :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((tot A Q).obj K) ≅
      (tot A Q).obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  haveI := preservesColimit_matrixAction G K Q a b
  (HomologicalComplex₂.totalIsoOfPreservesColimit G _).symm ≪≫
    HomologicalComplex₂.total.mapIso (bicomplexCompIso A G K Q) (ComplexShape.up ℤ)

end Functoriality

end CategoryTheory.MatrixAction

end
