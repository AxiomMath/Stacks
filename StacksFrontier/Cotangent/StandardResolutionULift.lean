module

public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageStandardResolutionComparison
public import StacksFrontier.Cotangent.PolynomialAlgebra
public import StacksFrontier.Cotangent.StandardResolution

/-!
# The standard resolution and the universe lift of the base and of the algebra

Let `A` be a commutative ring and `B` a commutative `A`-algebra, both in `Type u`. Lifting both
into `Type (u + 1)` by `ULift` gives the `ULift A`-algebra `ULift B`. The standard resolution of
Tag 08PM commutes with this lift: the lift of the standard resolution `P_•` of `B` over `A` is the
standard resolution of `ULift B` over `ULift A`, as augmented simplicial `ULift A`-algebras,
naturally in `B`.

## Main definitions

* `CommAlgCat.uliftBase`: the `ULift A`-algebra `ULift B`, and `CommAlgCat.uliftBaseFunctor` the
  functor `B ↦ ULift B`.
* `CommAlgCat.polynomialComonadULiftIso`: the comparison `ULift (A[B]) ≅ (ULift A)[ULift B]` of the
  two polynomial-algebra comonads.
* `CommAlgCat.standardResolutionULiftTermIso`: `ULift P_n ≅ P_n(ULift B / ULift A)` in each
  simplicial degree, and `CommAlgCat.standardResolutionULiftIso` the isomorphism of simplicial
  objects it assembles to.

## Main results

* `CommAlgCat.standardResolutionULiftTermIso_delta` and
  `CommAlgCat.standardResolutionULiftTermIso_sigma`: the comparison commutes with the faces and
  degeneracies.
* `CommAlgCat.standardResolutionULiftIso_hom_app_comp_augmentation`: it lies over the identity of
  `ULift B`.
* `CommAlgCat.standardResolutionULiftTermIso_naturality`: it is natural in `B`.

## References

* [Stacks Project, Tag 08PM](https://stacks.math.columbia.edu/tag/08PM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A]

/-- The algebra structure of the universe lift `ULift B` of a commutative `A`-algebra `B` over
the universe lift `ULift A` of the base: `a ↦ ULift.up (algebraMap A B a.down)`. -/
@[implicit_reducible]
def uliftBaseAlgebra (B : Type u) [CommRing B] [Algebra A B] :
    Algebra (ULift.{u + 1} A) (ULift.{u + 1} B) :=
  ((ULift.ringEquiv.symm : B ≃+* ULift.{u + 1} B).toRingHom.comp
    ((algebraMap A B).comp ULift.ringEquiv.toRingHom)).toAlgebra

/-- The universe lift `ULift B` of a commutative `A`-algebra `B`, as an algebra over the universe
lift `ULift A` of the base. -/
def uliftBase (B : CommAlgCat.{u} A) : CommAlgCat.{u + 1} (ULift.{u + 1} A) :=
  letI := uliftBaseAlgebra A B
  CommAlgCat.of (ULift.{u + 1} A) (ULift.{u + 1} B)

/-- The universe lift of a map of commutative `A`-algebras, as a map of `ULift A`-algebras. -/
def uliftBaseMap {B C : CommAlgCat.{u} A} (f : B ⟶ C) : uliftBase A B ⟶ uliftBase A C :=
  letI := uliftBaseAlgebra A B
  letI := uliftBaseAlgebra A C
  CommAlgCat.ofHom (X := ULift.{u + 1} B) (Y := ULift.{u + 1} C)
    { toRingHom := (ULift.ringEquiv.symm : C ≃+* ULift.{u + 1} C).toRingHom.comp
        (f.hom.toRingHom.comp ULift.ringEquiv.toRingHom)
      commutes' r := by
        change ULift.up (f.hom (algebraMap A B r.down)) = ULift.up (algebraMap A C r.down)
        exact congrArg ULift.up (f.hom.commutes r.down) }

/-- The universe lift of commutative `A`-algebras to commutative `ULift A`-algebras. -/
def uliftBaseFunctor : CommAlgCat.{u} A ⥤ CommAlgCat.{u + 1} (ULift.{u + 1} A) where
  obj B := uliftBase A B
  map f := uliftBaseMap A f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The universe lift of a polynomial algebra, `ULift (A[S]) ≃ (ULift A)[ULift S]`, as an
equivalence of `ULift A`-algebras: variables go to variables and coefficients to their lifts. -/
def uliftMvPolynomialAlgEquiv (S : Type u) :
    uliftBase A (CommAlgCat.of A (MvPolynomial S A)) ≃ₐ[ULift.{u + 1} A]
      MvPolynomial (ULift.{u + 1} S) (ULift.{u + 1} A) :=
  AlgEquiv.ofRingEquiv
    (f := (ULift.ringEquiv : ULift.{u + 1} (MvPolynomial S A) ≃+* MvPolynomial S A).trans
      ((MvPolynomial.renameEquiv A (Equiv.ulift.{u + 1, u} (α := S)).symm).toRingEquiv.trans
        (MvPolynomial.mapEquiv (ULift.{u + 1} S) (ULift.ringEquiv.symm : A ≃+* ULift.{u + 1} A))))
    (fun r => by
      change MvPolynomial.map (ULift.ringEquiv.symm : A ≃+* ULift.{u + 1} A).toRingHom
          (MvPolynomial.rename Equiv.ulift.symm (MvPolynomial.C r.down)) = MvPolynomial.C r
      rw [MvPolynomial.rename_C, MvPolynomial.map_C]
      rfl)

/-- `uliftMvPolynomialAlgEquiv` on a lifted polynomial renames the variables, then lifts the
coefficients. -/
private theorem uliftMvPolynomialAlgEquiv_up (S : Type u) (p : MvPolynomial S A) :
    uliftMvPolynomialAlgEquiv A S (ULift.up p) =
      MvPolynomial.map (ULift.ringEquiv.symm : A ≃+* ULift.{u + 1} A).toRingHom
        (MvPolynomial.rename Equiv.ulift.symm p) :=
  rfl

/-- `uliftMvPolynomialAlgEquiv` on the lift of a variable is the lifted variable. -/
theorem uliftMvPolynomialAlgEquiv_X (S : Type u) (s : S) :
    uliftMvPolynomialAlgEquiv A S (ULift.up (MvPolynomial.X s)) = MvPolynomial.X (ULift.up s) := by
  rw [uliftMvPolynomialAlgEquiv_up, MvPolynomial.rename_X, MvPolynomial.map_X]
  rfl

/-- `uliftMvPolynomialAlgEquiv` on the lift of a constant is the lifted constant. -/
theorem uliftMvPolynomialAlgEquiv_C (S : Type u) (a : A) :
    uliftMvPolynomialAlgEquiv A S (ULift.up (MvPolynomial.C a)) = MvPolynomial.C (ULift.up a) := by
  rw [uliftMvPolynomialAlgEquiv_up, MvPolynomial.rename_C, MvPolynomial.map_C]
  rfl

/-- The comparison of the free algebra functors, `ULift (A[S]) ≅ (ULift A)[ULift S]`, natural in
the set of variables. -/
def freeULiftIso :
    free.{u, u} A ⋙ uliftBaseFunctor A ≅
      CategoryTheory.uliftFunctor.{u + 1, u} ⋙ free.{u + 1, u + 1} (ULift A) :=
  NatIso.ofComponents (fun S => CommAlgCat.isoMk (uliftMvPolynomialAlgEquiv A S)) (fun {S T} f => by
    apply CommAlgCat.hom_ext
    refine AlgHom.ext fun x => ?_
    obtain ⟨x⟩ := x
    change uliftMvPolynomialAlgEquiv A T (ULift.up (MvPolynomial.rename f x)) =
      MvPolynomial.rename (ULift.map f) (uliftMvPolynomialAlgEquiv A S (ULift.up x))
    have h : (uliftMvPolynomialAlgEquiv A T).toRingEquiv.toRingHom.comp
        ((ULift.ringEquiv.symm :
            MvPolynomial T A ≃+* ULift.{u + 1} (MvPolynomial T A)).toRingHom.comp
          (MvPolynomial.rename f).toRingHom) =
      (MvPolynomial.rename (R := ULift.{u + 1} A) (ULift.map f)).toRingHom.comp
        ((uliftMvPolynomialAlgEquiv A S).toRingEquiv.toRingHom.comp
          (ULift.ringEquiv.symm :
            MvPolynomial S A ≃+* ULift.{u + 1} (MvPolynomial S A)).toRingHom) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        change uliftMvPolynomialAlgEquiv A T (ULift.up (MvPolynomial.rename f (MvPolynomial.C a))) =
          MvPolynomial.rename (ULift.map f) (uliftMvPolynomialAlgEquiv A S
            (ULift.up (MvPolynomial.C a)))
        rw [MvPolynomial.rename_C, uliftMvPolynomialAlgEquiv_C, uliftMvPolynomialAlgEquiv_C,
          MvPolynomial.rename_C]
      · intro s
        change uliftMvPolynomialAlgEquiv A T (ULift.up (MvPolynomial.rename f (MvPolynomial.X s))) =
          MvPolynomial.rename (ULift.map f) (uliftMvPolynomialAlgEquiv A S
            (ULift.up (MvPolynomial.X s)))
        rw [MvPolynomial.rename_X, uliftMvPolynomialAlgEquiv_X, uliftMvPolynomialAlgEquiv_X,
          MvPolynomial.rename_X]
        rfl
    exact RingHom.congr_fun h x)

/-- The underlying type of the lift of an algebra is the lift of its underlying type. -/
def forgetULiftIso :
    uliftBaseFunctor A ⋙ forget (CommAlgCat.{u + 1} (ULift.{u + 1} A)) ≅
      forget (CommAlgCat.{u} A) ⋙ CategoryTheory.uliftFunctor.{u + 1, u} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The two free–forgetful adjunctions and the universe lifts form a commuting square of
adjunctions: the comparison of the free functors carries the lift of the unit to the unit. -/
theorem freeULiftIso_unit (S : Type u) :
    CategoryTheory.uliftFunctor.{u + 1, u}.map ((adj.{u, u} A).unit.app S) ≫
        (forgetULiftIso A).inv.app ((free.{u, u} A).obj S) ≫
        (forget (CommAlgCat.{u + 1} (ULift.{u + 1} A))).map ((freeULiftIso A).hom.app S) =
      (adj.{u + 1, u + 1} (ULift.{u + 1} A)).unit.app
        (CategoryTheory.uliftFunctor.{u + 1, u}.obj S) := by
  ext s
  exact uliftMvPolynomialAlgEquiv_X A S s.down

/-- **The comparison of the polynomial-algebra comonads**, `ULift (A[B]) ≅ (ULift A)[ULift B]`. -/
def polynomialComonadULiftIso :
    (polynomialComonad.{u, u} A).toFunctor ⋙ uliftBaseFunctor A ≅
      uliftBaseFunctor A ⋙ (polynomialComonad.{u + 1, u + 1} (ULift.{u + 1} A)).toFunctor :=
  Adjunction.comonadSquareIso (freeULiftIso A) (forgetULiftIso A)

/-- The comparison of the comonads commutes with their counits. -/
theorem polynomialComonadULiftIso_counit (B : CommAlgCat.{u} A) :
    (polynomialComonadULiftIso A).hom.app B ≫
        (polynomialComonad.{u + 1, u + 1} (ULift.{u + 1} A)).ε.app ((uliftBaseFunctor A).obj B) =
      (uliftBaseFunctor A).map ((polynomialComonad.{u, u} A).ε.app B) :=
  Adjunction.comonadSquareIso_counit (adj.{u, u} A) (adj.{u + 1, u + 1} (ULift.{u + 1} A))
    (freeULiftIso A) (forgetULiftIso A) (freeULiftIso_unit A) B

/-- The comparison of the comonads commutes with their comultiplications. -/
theorem polynomialComonadULiftIso_comul (B : CommAlgCat.{u} A) :
    (uliftBaseFunctor A).map ((polynomialComonad.{u, u} A).δ.app B) ≫
        (polynomialComonadULiftIso A).hom.app ((polynomialComonad.{u, u} A).toFunctor.obj B) ≫
        (polynomialComonad.{u + 1, u + 1} (ULift.{u + 1} A)).toFunctor.map
          ((polynomialComonadULiftIso A).hom.app B) =
      (polynomialComonadULiftIso A).hom.app B ≫
        (polynomialComonad.{u + 1, u + 1} (ULift.{u + 1} A)).δ.app ((uliftBaseFunctor A).obj B) :=
  Adjunction.comonadSquareIso_comul (adj.{u, u} A) (adj.{u + 1, u + 1} (ULift.{u + 1} A))
    (freeULiftIso A) (forgetULiftIso A) (freeULiftIso_unit A) B

/-! ### The lift of the standard resolution -/

variable (B : CommAlgCat.{u} A)

/-- **The lift of a term of the standard resolution.** The universe lift of the degree-`n` term
`P_n` of the standard resolution of `B` over `A` is the degree-`n` term of the standard resolution
of `ULift B` over `ULift A`. -/
@[implicit_reducible]
def standardResolutionULiftTermIso (n : ℕ) :
    (uliftBaseFunctor A).obj ((standardResolution.{u, u} A B).left.obj (op ⦋n⦌)) ≅
      (standardResolution.{u + 1, u + 1} (ULift.{u + 1} A)
        ((uliftBaseFunctor A).obj B)).left.obj (op ⦋n⦌) :=
  Functor.transportObjIso (uliftBaseFunctor A) (standardResolution_obj.{u, u} A B n)
    (standardResolution_obj.{u + 1, u + 1} (ULift.{u + 1} A) ((uliftBaseFunctor A).obj B) n)
    (Functor.iterateCompIsoObj (polynomialComonadULiftIso A) (n + 1) rfl)

/-- The termwise comparison commutes with the face maps. -/
theorem standardResolutionULiftTermIso_delta (n : ℕ) (j : Fin (n + 2)) :
    (uliftBaseFunctor A).map ((standardResolution.{u, u} A B).left.δ j) ≫
        (standardResolutionULiftTermIso A B n).hom =
      (standardResolutionULiftTermIso A B (n + 1)).hom ≫
        (standardResolution.{u + 1, u + 1} (ULift.{u + 1} A)
          ((uliftBaseFunctor A).obj B)).left.δ j :=
  Functor.transportObjIso_naturality (uliftBaseFunctor A)
    (standardResolution_obj.{u, u} A B (n + 1)) (standardResolution_obj.{u, u} A B n)
    (standardResolution_obj.{u + 1, u + 1} (ULift.{u + 1} A) ((uliftBaseFunctor A).obj B) (n + 1))
    (standardResolution_obj.{u + 1, u + 1} (ULift.{u + 1} A) ((uliftBaseFunctor A).obj B) n)
    (Functor.iterateCompIsoObj (polynomialComonadULiftIso A) (n + 2) rfl)
    (Functor.iterateCompIsoObj (polynomialComonadULiftIso A) (n + 1) rfl)
    (standardResolution_face.{u, u} A B n j)
    (standardResolution_face.{u + 1, u + 1} (ULift.{u + 1} A) ((uliftBaseFunctor A).obj B) n j)
    (Functor.iterateCompIsoObj_godementFace (polynomialComonadULiftIso A)
      (polynomialComonad.{u, u} A).ε (polynomialComonad.{u + 1, u + 1} (ULift.{u + 1} A)).ε
      (polynomialComonadULiftIso_counit A) (n + 1) j rfl)

/-- The termwise comparison commutes with the degeneracy maps. -/
theorem standardResolutionULiftTermIso_sigma (n : ℕ) (j : Fin (n + 1)) :
    (uliftBaseFunctor A).map ((standardResolution.{u, u} A B).left.σ j) ≫
        (standardResolutionULiftTermIso A B (n + 1)).hom =
      (standardResolutionULiftTermIso A B n).hom ≫
        (standardResolution.{u + 1, u + 1} (ULift.{u + 1} A)
          ((uliftBaseFunctor A).obj B)).left.σ j :=
  Functor.transportObjIso_naturality (uliftBaseFunctor A)
    (standardResolution_obj.{u, u} A B n) (standardResolution_obj.{u, u} A B (n + 1))
    (standardResolution_obj.{u + 1, u + 1} (ULift.{u + 1} A) ((uliftBaseFunctor A).obj B) n)
    (standardResolution_obj.{u + 1, u + 1} (ULift.{u + 1} A) ((uliftBaseFunctor A).obj B) (n + 1))
    (Functor.iterateCompIsoObj (polynomialComonadULiftIso A) (n + 1) rfl)
    (Functor.iterateCompIsoObj (polynomialComonadULiftIso A) (n + 2) rfl)
    (standardResolution_degeneracy.{u, u} A B n j)
    (standardResolution_degeneracy.{u + 1, u + 1} (ULift.{u + 1} A)
      ((uliftBaseFunctor A).obj B) n j)
    (Functor.iterateCompIsoObj_godementDegeneracy (polynomialComonadULiftIso A)
      (polynomialComonad.{u, u} A).δ (polynomialComonad.{u + 1, u + 1} (ULift.{u + 1} A)).δ
      (polynomialComonadULiftIso_comul A) n j rfl)

/-- **The lift of the standard resolution of `B` over `A` is the standard resolution of `ULift B`
over `ULift A`**, as simplicial `ULift A`-algebras. -/
def standardResolutionULiftIso :
    (standardResolution.{u, u} A B).left ⋙ uliftBaseFunctor A ≅
      (standardResolution.{u + 1, u + 1} (ULift.{u + 1} A) ((uliftBaseFunctor A).obj B)).left :=
  SimplicialObject.isoCompOfFacesAndDegeneracies (uliftBaseFunctor A)
    (standardResolution.{u, u} A B).left
    (standardResolution.{u + 1, u + 1} (ULift.{u + 1} A) ((uliftBaseFunctor A).obj B)).left
    (standardResolutionULiftTermIso A B) (standardResolutionULiftTermIso_delta A B)
    (standardResolutionULiftTermIso_sigma A B)

/-- The components of the simplicial comparison are the termwise comparisons. -/
theorem standardResolutionULiftIso_hom_app (n : ℕ) :
    (standardResolutionULiftIso A B).hom.app (op ⦋n⦌) =
      (standardResolutionULiftTermIso A B n).hom :=
  rfl

/-- In degree zero the comparison lies over the identity of `ULift B`. -/
theorem standardResolutionULiftTermIso_augmentation_zero :
    (standardResolutionULiftTermIso A B 0).hom ≫
        (standardResolution.{u + 1, u + 1} (ULift.{u + 1} A)
          ((uliftBaseFunctor A).obj B)).hom.app (op ⦋0⦌) =
      (uliftBaseFunctor A).map ((standardResolution.{u, u} A B).hom.app (op ⦋0⦌)) ≫ 𝟙 _ :=
  Functor.transportObjIso_hom_comp_counit (polynomialComonadULiftIso A)
    (polynomialComonad.{u, u} A).ε (polynomialComonad.{u + 1, u + 1} (ULift.{u + 1} A)).ε
    (polynomialComonadULiftIso_counit A) (standardResolution_obj.{u, u} A B 0)
    (standardResolution_obj.{u + 1, u + 1} (ULift.{u + 1} A) ((uliftBaseFunctor A).obj B) 0) rfl
    (standardResolution_augmentation_eq_counit.{u, u} A B)
    (standardResolution_augmentation_eq_counit.{u + 1, u + 1} (ULift.{u + 1} A)
      ((uliftBaseFunctor A).obj B)) rfl

/-- **The comparison lies over the identity of `ULift B`**: in every degree it carries the
augmentation of the standard resolution of `ULift B` to the lift of the augmentation. -/
theorem standardResolutionULiftIso_hom_app_comp_augmentation (n : ℕ) :
    (standardResolutionULiftIso A B).hom.app (op ⦋n⦌) ≫
        (standardResolution.{u + 1, u + 1} (ULift.{u + 1} A)
          ((uliftBaseFunctor A).obj B)).hom.app (op ⦋n⦌) =
      (uliftBaseFunctor A).map ((standardResolution.{u, u} A B).hom.app (op ⦋n⦌)) := by
  refine (SimplicialObject.hom_comp_toConst_of_zero
    (SimplicialObject.mapToConst (uliftBaseFunctor A) (standardResolution.{u, u} A B).hom)
    (standardResolution.{u + 1, u + 1} (ULift.{u + 1} A) ((uliftBaseFunctor A).obj B)).hom
    (standardResolutionULiftIso A B) (𝟙 _) ?_ n).trans (Category.comp_id _)
  exact standardResolutionULiftTermIso_augmentation_zero A B

/-- **The comparison is natural in the algebra**: for a map `f : B ⟶ C` of `A`-algebras it
intertwines the lift of the induced map of standard resolutions with the map of standard
resolutions induced by the lift of `f`. -/
theorem standardResolutionULiftTermIso_naturality {B C : CommAlgCat.{u} A} (f : B ⟶ C) (n : ℕ) :
    (uliftBaseFunctor A).map (((standardResolutionFunctor.{u, u} A).map f).left.app (op ⦋n⦌)) ≫
        (standardResolutionULiftTermIso A C n).hom =
      (standardResolutionULiftTermIso A B n).hom ≫
        ((standardResolutionFunctor.{u + 1, u + 1} (ULift.{u + 1} A)).map
          ((uliftBaseFunctor A).map f)).left.app (op ⦋n⦌) :=
  Functor.transportObjIso_naturality (uliftBaseFunctor A)
    (standardResolution_obj.{u, u} A B n) (standardResolution_obj.{u, u} A C n)
    (standardResolution_obj.{u + 1, u + 1} (ULift.{u + 1} A) ((uliftBaseFunctor A).obj B) n)
    (standardResolution_obj.{u + 1, u + 1} (ULift.{u + 1} A) ((uliftBaseFunctor A).obj C) n)
    (Functor.iterateCompIsoObj (polynomialComonadULiftIso A) (n + 1) rfl)
    (Functor.iterateCompIsoObj (polynomialComonadULiftIso A) (n + 1) rfl)
    (Functor.congr_hom (standardEndofunctor_obj.{u, u} A n) f)
    (Functor.congr_hom (standardEndofunctor_obj.{u + 1, u + 1} (ULift.{u + 1} A) n)
      ((uliftBaseFunctor A).map f))
    (by simpa [Functor.iterateCompIsoObj] using
      ((Functor.iterateCompIso (polynomialComonadULiftIso A) (n + 1)).hom.naturality f))

end CommAlgCat
