module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import StacksFrontier.Algebra.Homology.MatrixActionTotal
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness

/-!
# Tensoring with a bounded complex of finite free modules, on derived categories

Let `A` be a commutative ring, `C` an abelian `A`-linear category and `Q` a bounded complex of
finite free `A`-modules with chosen bases, that is a bounded cochain complex in
`Mat_ (SingleObj A)`.  The functor `K ↦ Tot(K ⊗_A Q)` (`CategoryTheory.MatrixAction.tot`)
preserves quasi-isomorphisms, so it descends to an endofunctor `- ⊗_A Q` of `D(C)`, which

* shifts bounds by the bounds of `Q`;
* commutes with every exact `A`-linear functor;
* on bounded below objects commutes with the total right derived functor of every additive
  `A`-linear functor.

## Main definitions

* `CategoryTheory.MatrixAction.derivedTot`: the functor `- ⊗_A Q` on `D(C)`.
* `CategoryTheory.MatrixAction.derivedTotFactors`: its value on a complex is the class of the
  total complex.

## Main results

* `CategoryTheory.MatrixAction.isLE_derivedTot_obj`, `isGE_derivedTot_obj`: bounds.
* `CategoryTheory.MatrixAction.derivedTotMapDerivedCategoryIso`: commutation with an exact
  `A`-linear functor.
* `CategoryTheory.MatrixAction.derivedTotTotalRightDerivedIso`: commutation with the total
  right derived functor of an additive `A`-linear functor, on bounded below objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u w₀

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A finite biproduct of injective objects is injective, with no restriction on the universe of
the index type. -/
lemma injective_biproduct {J : Type*} [Finite J] (c : J → C) [HasBiproduct c]
    [∀ j, Injective (c j)] : Injective (⨁ c) where
  factors g f mono := by
    refine ⟨biproduct.lift fun b => Injective.factorThru (g ≫ biproduct.π _ _) f, ?_⟩
    ext
    simp only [Category.assoc, biproduct.lift_π, Injective.comp_factorThru]

/-- A coproduct of a family of injective objects vanishing off a finite set is injective. -/
lemma injective_coproduct_of_isZero {J : Type*} (f : J → C) (S : Set J) [Finite S]
    (hz : ∀ j ∉ S, IsZero (f j)) [HasBiproduct fun s : S => f s] [HasCoproduct f]
    (hf : ∀ j ∈ S, Injective (f j)) : Injective (∐ f) := by
  classical
  have : ∀ s : S, Injective (f s) := fun s => hf s.1 s.2
  exact Injective.of_iso ((isColimitCofanExtend f S hz
    (biproduct.isBilimit _).isColimit).coconePointUniqueUpToIso (colimit.isColimit _))
    (injective_biproduct fun s : S => f s)

end CategoryTheory.Limits

namespace CategoryTheory.MatrixAction

variable (A : Type w) [CommRing A]

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [Linear A C]
  [∀ (K : CochainComplex C ℤ) (Q : CochainComplex (Mat_ (SingleObj A)) ℤ),
      HomologicalComplex.HasMapBifunctor K Q (matrixAction A (C := C)) (ComplexShape.up ℤ)]
  (Q : CochainComplex (Mat_ (SingleObj A)) ℤ)

/-- The total complex in degree `n` is zero as soon as every summand of total degree `n` is. -/
lemma isZero_tot_X (K : CochainComplex C ℤ) (n : ℤ)
    (h : ∀ p q : ℤ, p + q = n → IsZero (((matrixAction A).obj (K.X p)).obj (Q.X q))) :
    IsZero (((tot A Q).obj K).X n) := by
  rw [IsZero.iff_id_eq_zero]
  refine HomologicalComplex₂.total.hom_ext _ fun p q hpq => ?_
  exact (h p q hpq).eq_of_src _ _

/-- If `Q` is strictly `≤ b` and `K` is strictly `≤ c`, the total complex is strictly
`≤ c + b`. -/
instance isStrictlyLE_tot (b : ℤ) [Q.IsStrictlyLE b] (K : CochainComplex C ℤ) (c : ℤ)
    [K.IsStrictlyLE c] :
    ((tot A Q).obj K).IsStrictlyLE (c + b) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  refine isZero_tot_X A Q K n fun p q hpq => ?_
  by_cases hp : c < p
  · exact ((matrixAction A).flip.obj (Q.X q)).map_isZero (K.isZero_of_isStrictlyLE c p hp)
  · exact ((matrixAction A).obj (K.X p)).map_isZero (Q.isZero_of_isStrictlyLE b q (by omega))

/-- If `Q` is strictly `≥ a` and `K` is strictly `≥ c`, the total complex is strictly
`≥ c + a`. -/
instance isStrictlyGE_tot (a : ℤ) [Q.IsStrictlyGE a] (K : CochainComplex C ℤ) (c : ℤ)
    [K.IsStrictlyGE c] :
    ((tot A Q).obj K).IsStrictlyGE (c + a) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  refine isZero_tot_X A Q K n fun p q hpq => ?_
  by_cases hp : p < c
  · exact ((matrixAction A).flip.obj (Q.X q)).map_isZero (K.isZero_of_isStrictlyGE c p hp)
  · exact ((matrixAction A).obj (K.X p)).map_isZero (Q.isZero_of_isStrictlyGE a q (by omega))

/-- The total complex of a bounded below complex of injective objects is a bounded below
complex of injective objects. -/
lemma injective_tot_X (a b : ℤ) [Q.IsStrictlyLE b] [Q.IsStrictlyGE a] (K : CochainComplex C ℤ)
    (hK : ∀ p, Injective (K.X p)) (n : ℤ) :
    Injective (((tot A Q).obj K).X n) := by
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
  exact injective_coproduct_of_isZero
    (((((matrixAction A).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj K).obj Q).toGradedObject.mapObjFun
        (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n) S
    (fun i hi => isZero_matrixAction_X_X A K Q a b _ _
      (by simp only [S, Set.mem_ofPred_eq, not_and_or, not_le] at hi; omega))
    fun i _ => injective_biproduct _

section Derived

variable [HasDerivedCategory C]

/-- The composite of the total complex functor with the localization functor to `D(C)` inverts
quasi-isomorphisms. -/
lemma tot_comp_Q_inverts (a b : ℤ) [Q.IsStrictlyLE b] [Q.IsStrictlyGE a] :
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).IsInvertedBy
      (tot A Q ⋙ DerivedCategory.Q) := fun _ _ f hf => by
  have : QuasiIso f := hf
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_tot_map A Q a b f)

/-- **Tensoring with a bounded complex of finite free `A`-modules on `D(C)`.** -/
def derivedTot (a b : ℤ) [Q.IsStrictlyLE b] [Q.IsStrictlyGE a] :
    DerivedCategory C ⥤ DerivedCategory C :=
  Localization.lift _ (tot_comp_Q_inverts A Q a b) DerivedCategory.Q

/-- `- ⊗_A Q` on `D(C)` is computed by the total complex. -/
def derivedTotFactors (a b : ℤ) [Q.IsStrictlyLE b] [Q.IsStrictlyGE a] :
    DerivedCategory.Q ⋙ derivedTot A Q a b ≅ tot A (C := C) Q ⋙ DerivedCategory.Q :=
  Localization.fac _ _ _

/-- The value of `- ⊗_A Q` at an object is the class of the total complex of any representing
complex. -/
def derivedTotObjIso (a b : ℤ) [Q.IsStrictlyLE b] [Q.IsStrictlyGE a] {K : DerivedCategory C}
    {X : CochainComplex C ℤ} (e : DerivedCategory.Q.obj X ≅ K) :
    (derivedTot A Q a b).obj K ≅ DerivedCategory.Q.obj ((tot A Q).obj X) :=
  (derivedTot A Q a b).mapIso e.symm ≪≫ (derivedTotFactors A Q a b).app X

/-- `- ⊗_A Q` raises an upper bound by the upper bound of `Q`. -/
lemma isLE_derivedTot_obj (a b : ℤ) [Q.IsStrictlyLE b] [Q.IsStrictlyGE a] (K : DerivedCategory C)
    (c : ℤ) [K.IsLE c] :
    ((derivedTot A Q a b).obj K).IsLE (c + b) := by
  obtain ⟨X, hX, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE K c
  exact DerivedCategory.TStructure.t.isLE_of_iso (derivedTotObjIso A Q a b e.symm).symm (c + b)

/-- `- ⊗_A Q` raises a lower bound by the lower bound of `Q`. -/
lemma isGE_derivedTot_obj (a b : ℤ) [Q.IsStrictlyLE b] [Q.IsStrictlyGE a] (K : DerivedCategory C)
    (c : ℤ) [K.IsGE c] :
    ((derivedTot A Q a b).obj K).IsGE (c + a) := by
  obtain ⟨X, hX, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K c
  exact DerivedCategory.TStructure.t.isGE_of_iso (derivedTotObjIso A Q a b e.symm).symm (c + a)

section ExactFunctor

variable {D : Type*} [Category D] [Abelian D] [Linear A D] [HasDerivedCategory D]
  [∀ (K : CochainComplex D ℤ) (Q : CochainComplex (Mat_ (SingleObj A)) ℤ),
      HomologicalComplex.HasMapBifunctor K Q (matrixAction A (C := D)) (ComplexShape.up ℤ)]
  (G : C ⥤ D) [G.Additive] [G.Linear A] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **`- ⊗_A Q` commutes with an exact `A`-linear functor**, on objects of `D(C)`. -/
def derivedTotMapDerivedCategoryIso (a b : ℤ) [Q.IsStrictlyLE b] [Q.IsStrictlyGE a]
    (K : DerivedCategory C) :
    G.mapDerivedCategory.obj ((derivedTot A Q a b).obj K) ≅
      (derivedTot A Q a b).obj (G.mapDerivedCategory.obj K) :=
  let X := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj X ≅ K := DerivedCategory.Q.objObjPreimageIso K
  G.mapDerivedCategory.mapIso (derivedTotObjIso A Q a b e) ≪≫
    G.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso (totCompIso A G Q a b X) ≪≫
    (derivedTotObjIso A Q a b
      ((G.mapDerivedCategoryFactors.app X).symm ≪≫ G.mapDerivedCategory.mapIso e)).symm

end ExactFunctor

section RightDerived

variable [IsGrothendieckAbelian.{w₀} C] [EnoughInjectives C]
  {D : Type*} [Category D] [Abelian D] [Linear A D] [HasDerivedCategory D]
  [∀ (K : CochainComplex D ℤ) (Q : CochainComplex (Mat_ (SingleObj A)) ℤ),
      HomologicalComplex.HasMapBifunctor K Q (matrixAction A (C := D)) (ComplexShape.up ℤ)]
  (F : C ⥤ D) [F.Additive] [F.Linear A]

/-- The total right derived functor of `F` at the class of a K-injective complex is `F` applied
degreewise. -/
def totalRightDerivedObjIsoOfIsKInjective (I : CochainComplex C ℤ) [I.IsKInjective] :
    (Stacks.DerivedFunctor.totalRightDerived F).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have hunit := Stacks.DerivedFunctor.isIso_totalRightDerivedUnit_app_of_isKInjective F I
  (Stacks.DerivedFunctor.totalRightDerived F).mapIso
      ((DerivedCategory.quotientCompQhIso C).app I).symm ≪≫
    (@asIso _ _ _ _ _ hunit).symm ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I) ≪≫
    (DerivedCategory.quotientCompQhIso D).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)

/-- **`- ⊗_A Q` commutes with the total right derived functor of an additive `A`-linear
functor**, on bounded below objects of `D(C)`. -/
def derivedTotTotalRightDerivedIso (a b : ℤ) [Q.IsStrictlyLE b] [Q.IsStrictlyGE a]
    (L : DerivedCategory C) (n : ℤ) [L.IsGE n] :
    (derivedTot A Q a b).obj ((Stacks.DerivedFunctor.totalRightDerived F).obj L) ≅
      (Stacks.DerivedFunctor.totalRightDerived F).obj ((derivedTot A Q a b).obj L) := by
  classical
  let X : CochainComplex C ℤ := DerivedCategory.Q.objPreimage L
  have eX : DerivedCategory.Q.obj X ≅ L := DerivedCategory.Q.objObjPreimageIso L
  have hXGE : X.IsGE n := by
    rw [← DerivedCategory.isGE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isGE_of_iso eX.symm n
  let R := (CochainComplex.exists_injectiveResolution_isStrictlyGE n X).choose
  have hRGE : R.cocomplex.IsStrictlyGE n :=
    (CochainComplex.exists_injectiveResolution_isStrictlyGE n X).choose_spec.2
  have hKI : R.cocomplex.IsKInjective := CochainComplex.isKInjective_of_injective R.cocomplex n
  have : QuasiIso R.ι := R.quasiIso
  have eL : DerivedCategory.Q.obj R.cocomplex ≅ L :=
    (asIso (DerivedCategory.Q.map R.ι)).symm ≪≫ eX
  have hTinj := injective_tot_X A Q a b R.cocomplex R.injective
  have hTKI : ((tot A Q).obj R.cocomplex).IsKInjective :=
    CochainComplex.isKInjective_of_injective _ (n + a)
  exact (derivedTot A Q a b).mapIso
      ((Stacks.DerivedFunctor.totalRightDerived F).mapIso eL.symm ≪≫
        totalRightDerivedObjIsoOfIsKInjective F R.cocomplex) ≪≫
    (derivedTotFactors A Q a b).app _ ≪≫
    DerivedCategory.Q.mapIso (totCompIso A F Q a b R.cocomplex).symm ≪≫
    (totalRightDerivedObjIsoOfIsKInjective F ((tot A Q).obj R.cocomplex)).symm ≪≫
    (Stacks.DerivedFunctor.totalRightDerived F).mapIso
      (((derivedTotFactors A Q a b).app R.cocomplex).symm ≪≫ (derivedTot A Q a b).mapIso eL)

end RightDerived

end Derived

end CategoryTheory.MatrixAction

end
