module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatBaseChange

/-!
# Tor-independent base change for the algebraic upper shriek functor

Let `φ : R → A` be of finite type, let `R → R'` be arbitrary and let `A` and `R'` be Tor
independent over `R`.  This file constructs the natural transformation
`φ^!(K) ⊗_A^L A' ⟶ (φ')^!(K ⊗_R^L R')` for `φ' : R' → A' = R' ⊗_R A`, where the two derived
tensor products are read at arbitrary left-derived models of extension of scalars, and proves it
invertible when `φ` is perfect, given the projection-formula compatibility of [stacks 0E2A].

## Main results

* `Dualizing.torIndependent_mvPolynomialBaseChange` — Tor independence of `A` and `R'` over `R`
  lifts to Tor independence of `A` and `R'[x_1, …, x_n]` over `R[x_1, …, x_n]`.
* `Dualizing.PolynomialPresentation.upperShriekTorIndependentBaseChange` — the base-change map.
* `Dualizing.PolynomialPresentation.isIso_upperShriekTorIndependentBaseChange` — that map is an
  isomorphism of functors when `A` is a perfect module over the polynomial algebra of the
  presentation, given the projection-formula compatibility `Dualizing.KFlatAlgebraActionEq` of
  [stacks 0E2A].

## Implementation notes

The construction follows [stacks 0BZN] with flatness of `R → R'` removed: the base-change map for
derived Hom of [stacks 0E29] is applied to the square `P, A, P', A'` of a presentation
`P = R[x_1, …, x_n] ↠ A`, and the identification `(K ⊗_R^L P) ⊗_P^L P' = (K ⊗_R^L R') ⊗_{R'}^L P'`
of [stacks 08YU] is obtained from uniqueness of left adjoints.  Without flatness the three derived
tensor products are no longer computed degreewise, so `Dualizing.flatDerivedExtension` is replaced
by arbitrary models: the two occurring in the statement are arguments, and the two internal ones
are `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral`.  Tor independence of
the square `P, A, P'` is no longer automatic either, and is supplied by
`Dualizing.torIndependent_mvPolynomialBaseChange`.

Transporting the base-change map along the ring isomorphism `A ⊗_P P' ≅ R' ⊗_R A` is done by
uniqueness of adjoints, using `StacksDraft.DerivedRingIso.adjRestrictScalarsOfInv` and
`StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp`.

`ModuleCat.extendScalars` and the comparison target of a total derived extension of scalars are
made `implicit_reducible` where they are unfolded, the first to compare the two module structures
on `P ⊗_R M`, the second because `TotalDerivedExtensionScalars.comparison` is typed by
`extensionOfScalarsComplexGeneral` while [stacks 0E29] expects it unfolded.

Everything is stated for an arbitrary presentation rather than for one chosen by
`Classical.choice`, so nothing here depends on [stacks 0BZJ]; the Noetherian hypotheses of the
source are not needed for the map and are omitted.  Perfectness of `φ` is omitted from the map,
which the source uses it only for, and appears on the invertibility statement, where it is read
at the presentation: `A` is asked to be a perfect module over the polynomial algebra `P` of `p`.
The module universe is the ring universe.

Invertibility is reduced, as in the source, to [stacks 0BZP] at the square `P, A, P', A ⊗_P P'`
of the presentation: the base-change map is that morphism of [stacks 0E29] conjugated by
isomorphisms of functors and whiskered, so it is invertible as soon as that morphism is.  The
same reduction at the flat square is
`Dualizing.PolynomialPresentation.isIso_upperShriekFlatBaseChange_app` of [stacks 0BZN], and the
two differ only in which case of the invertibility criterion they appeal to — the perfect case
here, which has no boundedness hypothesis on `K`, so the conclusion is an isomorphism of functors
rather than one object at a time.

### The statement of [stacks 0BZR]

The invertibility statement here is read at the module universe of the rings and carries the
hypothesis `Dualizing.KFlatAlgebraActionEq`, the form of the projection-formula compatibility of
[stacks 0E2A] it was first proved under.  [stacks 0BZR] itself, at every module universe and with
no such hypothesis, is
`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_comp_iso_of_torIndependent` in
`StacksFrontier.RingTheory.Dualizing.UpperShriek.TorIndependentBaseChangeIso`.

## References

* [Stacks Project, Tag 0BZR](https://stacks.math.columbia.edu/tag/0BZR)
* [Stacks Project, Tag 0BZP](https://stacks.math.columbia.edu/tag/0BZP)
* [Stacks Project, Tag 0E29](https://stacks.math.columbia.edu/tag/0E29)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars
open RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

section TorIndependence

attribute [local implicit_reducible] ModuleCat.ExtendScalars.obj' ModuleCat.extendScalars

/-- Extension of scalars along `R → P` of an `R`-module, as a `P`-module tensor product. -/
def extendScalarsObjIso
    {R P : Type u} [CommRing R] [CommRing P] [Algebra R P] (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R P)).obj M ≅
      ModuleCat.of P (TensorProduct R P M) := by
  have : SMulCommClass R P ((ModuleCat.restrictScalars (algebraMap R P)).obj
      (ModuleCat.of P P)) := ⟨fun r p q ↦ mul_left_comm (algebraMap R P r) p q⟩
  let e : (ModuleCat.restrictScalars (algebraMap R P)).obj (ModuleCat.of P P) ≃ₗ[R] P :=
    { AddEquiv.refl P with
      map_smul' := fun r p ↦ (Algebra.smul_def (R := R) (A := P) r p).symm }
  let e' : (ModuleCat.extendScalars (algebraMap R P)).obj M ≃+ TensorProduct R P M :=
    (TensorProduct.congr e (LinearEquiv.refl R M)).toAddEquiv
  let l : (ModuleCat.extendScalars (algebraMap R P)).obj M ≃ₗ[P] TensorProduct R P M :=
    { e' with
      map_smul' := by
        intro p z
        induction z using TensorProduct.induction_on with
        | zero =>
            calc
              e' (p • 0) = e' 0 := congrArg e' (smul_zero p)
              _ = 0 := e'.map_zero
              _ = p • e' 0 := by rw [e'.map_zero, smul_zero]
        | tmul q m => rfl
        | add x y hx hy =>
            calc
              e' (p • (x + y)) = e' (p • x + p • y) := congrArg e' (smul_add p x y)
              _ = e' (p • x) + e' (p • y) := e'.map_add _ _
              _ = p • e' x + p • e' y := congrArg₂ (· + ·) hx hy
              _ = p • (e' x + e' y) := (smul_add p (e' x) (e' y)).symm
              _ = p • e' (x + y) := congrArg (p • ·) (e'.map_add x y).symm }
  exact l.toModuleIso

/-- Extension of scalars along `R → R[x_1, …, x_n]` carries an `R`-algebra `S` to
`S[x_1, …, x_n]`. -/
private def polynomialBaseChangeModuleIso
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (n : ℕ) : letI :=
      (MvPolynomial.map (σ := Fin n) (algebraMap R S)).toAlgebra
      (ModuleCat.extendScalars (algebraMap R (MvPolynomial (Fin n) R))).obj
        (ModuleCat.of R S) ≅
      ModuleCat.of (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) S) := by
  letI := (MvPolynomial.map (σ := Fin n) (algebraMap R S)).toAlgebra
  let P := MvPolynomial (Fin n) R
  let e := (Algebra.TensorProduct.comm R P S).toRingEquiv.trans
    (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R S).toRingEquiv
  let le : P ⊗[R] S ≃ₗ[P] MvPolynomial (Fin n) S :=
    { e.toAddEquiv with
      map_smul' := by
        intro p z
        induction z using TensorProduct.induction_on with
        | zero =>
            calc
              e (p • 0) = e 0 := congrArg e (smul_zero p)
              _ = 0 := e.map_zero
              _ = p • e 0 := by rw [e.map_zero, smul_zero]
        | tmul q s =>
            change e ((p * q) ⊗ₜ[R] s) = _
            have hp : algebraMap P (MvPolynomial (Fin n) S) p =
                MvPolynomial.map (algebraMap R S) p := rfl
            dsimp [e]
            rw [MvPolynomial.algebraTensorAlgEquiv_tmul,
              MvPolynomial.algebraTensorAlgEquiv_tmul, map_mul]
            simp only [Algebra.smul_def]
            ac_rfl
        | add x y hx hy =>
            calc
              e (p • (x + y)) = e (p • x + p • y) := congrArg e (smul_add p x y)
              _ = e (p • x) + e (p • y) := e.map_add _ _
              _ = p • e x + p • e y := congrArg₂ (· + ·) hx hy
              _ = p • (e x + e y) := (smul_add p (e x) (e y)).symm
              _ = p • e (x + y) := congrArg (p • ·) (e.map_add x y).symm }
  exact extendScalarsObjIso (ModuleCat.of R S) ≪≫ le.toModuleIso

/-- Restricting `A ⊗_R M` from `P` to `R` is tensoring the restriction of `A` with `M`. -/
private def restrictTensorObjIso
    {R P A : Type u} [CommRing R] [CommRing P] [CommRing A]
    [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A]
    (M : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars (algebraMap R P)).obj (ModuleCat.of P (A ⊗[R] M)) ≅
      (tensorLeft ((ModuleCat.restrictScalars (algebraMap R P)).obj
        (ModuleCat.of P A))).obj M := by
  let eA : (ModuleCat.restrictScalars (algebraMap R P)).obj (ModuleCat.of P A) ≃ₗ[R] A :=
    { toFun := fun a => (a : A)
      invFun := fun a => (a : (ModuleCat.restrictScalars (algebraMap R P)).obj
        (ModuleCat.of P A))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r a
        exact IsScalarTower.algebraMap_smul P r (show A from a) }
  let X := (ModuleCat.restrictScalars (algebraMap R P)).obj
    (ModuleCat.of P (A ⊗[R] M))
  let e₀ : X ≃ₗ[R] ModuleCat.of R (A ⊗[R] M) :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r z
        induction z using TensorProduct.induction_on with
        | zero =>
            change (algebraMap R P r) • (0 : A ⊗[R] M) = r • (0 : A ⊗[R] M)
            rw [smul_zero, smul_zero]
        | tmul a m =>
            change ((algebraMap R P r) • a) ⊗ₜ[R] m = (r • a) ⊗ₜ[R] m
            rw [IsScalarTower.algebraMap_smul P r a]
        | add x y hx hy =>
            change (algebraMap R P r) • (x + y) = r • (x + y)
            rw [smul_add, smul_add]
            exact congrArg₂ (fun x y => x + y) hx hy }
  let e₁ : ModuleCat.of R (A ⊗[R] M) ≃ₗ[R]
      (tensorLeft ((ModuleCat.restrictScalars (algebraMap R P)).obj
        (ModuleCat.of P A))).obj M :=
    (TensorProduct.congr eA.symm (LinearEquiv.refl R M))
  exact (e₀.trans e₁).toModuleIso

/-- Cancelling the polynomial factor: `A ⊗_P (P ⊗_R M)`, restricted to `R`, is `A ⊗_R M`,
naturally in the `R`-module `M`. -/
private def cancelPolynomialBaseChangeNatIso
    {R P A : Type u} [CommRing R] [CommRing P] [CommRing A]
    [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A] :
    ModuleCat.extendScalars (algebraMap R P) ⋙ tensorLeft (ModuleCat.of P A) ⋙
      ModuleCat.restrictScalars (algebraMap R P) ≅
      tensorLeft ((ModuleCat.restrictScalars (algebraMap R P)).obj (ModuleCat.of P A)) := by
  refine NatIso.ofComponents (fun M ↦ ((ModuleCat.restrictScalars (algebraMap R P)).mapIso
      ((tensorLeft (ModuleCat.of P A)).mapIso (extendScalarsObjIso M))) ≪≫
    ((ModuleCat.restrictScalars (algebraMap R P)).mapIso
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R P P A M).toModuleIso) ≪≫
    restrictTensorObjIso M) ?_
  intro M N f
  apply ModuleCat.hom_ext
  ext z
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul a m =>
      induction m using TensorProduct.induction_on with
      | zero => rfl
      | tmul p x => rfl
      | add x y hx hy =>
          rw [TensorProduct.tmul_add]
          exact (map_add _ _ _).trans
            ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
  | add x y hx hy =>
      exact (map_add _ x y).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

/-- Tor independence of `A` and `S` over `R` lifts along a polynomial extension: `A`, made an
algebra over `P = R[x_1, …, x_n]` by any `R`-algebra map `α`, is Tor independent from
`S[x_1, …, x_n]` over `P`.  Extending a projective resolution of `S` along the flat map `R → P`
resolves `S[x_1, …, x_n]`, and tensoring with `A` over `P` cancels the polynomial factor. -/
theorem torIndependent_mvPolynomialBaseChange
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] (n : ℕ)
    (α : MvPolynomial (Fin n) R →ₐ[R] A)
    (h : TorIndependent R A S) :
    letI : Algebra (MvPolynomial (Fin n) R) A := α.toRingHom.toAlgebra
    letI : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) S) :=
      (MvPolynomial.map (algebraMap R S)).toAlgebra
    TorIndependent (MvPolynomial (Fin n) R) A (MvPolynomial (Fin n) S) := by
  let : Algebra (MvPolynomial (Fin n) R) A := α.toRingHom.toAlgebra
  let : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) S) :=
    (MvPolynomial.map (algebraMap R S)).toAlgebra
  rw [torIndependent_iff_isZero_tor] at h ⊢
  intro i hi
  let P := MvPolynomial (Fin n) R
  let P' := MvPolynomial (Fin n) S
  let F := ModuleCat.extendScalars (algebraMap R P)
  let : PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u}
      (algebraMap R P) (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let : F.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (ModuleCat.extendRestrictScalarsAdj (algebraMap R P))
  let Q₀ := projectiveResolution (ModuleCat.of R S)
  let Q := F.mapProjectiveResolution Q₀
  let eS : F.obj (ModuleCat.of R S) ≅ ModuleCat.of P P' :=
    polynomialBaseChangeModuleIso n
  let eTor := ((Tor (ModuleCat P) i).obj (ModuleCat.of P A)).mapIso eS
  refine IsZero.of_iso ?_ eTor.symm
  let eQ := Q.isoLeftDerivedObj (tensorLeft (ModuleCat.of P A)) i
  refine IsZero.of_iso ?_ eQ
  rw [ModuleCat.isZero_iff_subsingleton]
  let eA : (ModuleCat.restrictScalars (algebraMap R P)).obj (ModuleCat.of P A) ≅
      ModuleCat.of R A := ({
        toFun := id
        invFun := id
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r a ↦
          IsScalarTower.algebraMap_smul P r (show A from a) } :
          ((ModuleCat.restrictScalars (algebraMap R P)).obj
            (ModuleCat.of P A)) ≃ₗ[R] A).toModuleIso
  have hz : IsZero (((tensorLeft ((ModuleCat.restrictScalars (algebraMap R P)).obj
      (ModuleCat.of P A))).leftDerived i).obj (ModuleCat.of R S)) :=
    IsZero.of_iso (h i hi) (((Tor (ModuleCat R) i).mapIso eA).app (ModuleCat.of R S))
  have hz₀ : IsZero
      ((((tensorLeft ((ModuleCat.restrictScalars (algebraMap R P)).obj
        (ModuleCat.of P A))).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          Q₀.complex).homology i) :=
    hz.of_iso (Q₀.isoLeftDerivedObj
      (tensorLeft ((ModuleCat.restrictScalars (algebraMap R P)).obj (ModuleCat.of P A))) i).symm
  let G := ModuleCat.restrictScalars (algebraMap R P)
  let C := ((tensorLeft (ModuleCat.of P A)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj Q.complex
  have e₀ : G.obj (C.homology i) ≅
      (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj C).homology i) :=
    (ShortComplex.mapHomologyIso (C.sc i) G).symm ≪≫
      HomologicalComplex.homologyMapIso
        (Iso.refl ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj C)) i
  let e₁ := HomologicalComplex.homologyMapIso
    ((NatIso.mapHomologicalComplex
      (cancelPolynomialBaseChangeNatIso (R := R) (P := P) (A := A))
      (ComplexShape.down ℕ)).app Q₀.complex) i
  show Subsingleton (G.obj (C.homology i))
  exact ModuleCat.isZero_iff_subsingleton.mp ((hz₀.of_iso e₁).of_iso e₀)

end TorIndependence

section Construction

variable {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}

/-- The comparison exhibiting the derived base change along the polynomial algebra of a
presentation as a left derived functor of extension of scalars. -/
private def presentationComparison (p : PolynomialPresentation f) :
    DerivedCategory.Q ⋙ p.derivedExtension.{u, 0} ⟶
      (ModuleCat.extendScalars.{u, u, u}
        (MvPolynomial.C : R →+* p.Poly)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := by
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (MvPolynomial.C : R →+* p.Poly)) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, 0} _ p.flat_C
  exact (ModuleCat.extendScalars.{u, u, u}
    (MvPolynomial.C : R →+* p.Poly)).mapDerivedCategoryFactors.hom

/-- A polynomial algebra is flat over its coefficient ring, so the derived base change of a
presentation is its own left derived functor. -/
private theorem presentation_isLeftDerivedFunctor (p : PolynomialPresentation f) :
    (p.derivedExtension.{u, 0}).IsLeftDerivedFunctor (presentationComparison p)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  let : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (MvPolynomial.C : R →+* p.Poly)) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, 0} _ p.flat_C
  exact Functor.isLeftDerivedFunctor_of_inverts _ _
    (ModuleCat.extendScalars.{u, u, u} (MvPolynomial.C : R →+* p.Poly)).mapDerivedCategoryFactors

/-- Derived base change along the polynomial algebra of a presentation is left adjoint to
derived restriction of scalars along it. -/
private def presentationAdjunction (p : PolynomialPresentation f) :
    p.derivedExtension.{u, 0} ⊣
      (ModuleCat.restrictScalars.{u} (MvPolynomial.C : R →+* p.Poly)).mapDerivedCategory :=
  letI := presentation_isLeftDerivedFunctor p
  derivedExtensionScalarsAdjunction (MvPolynomial.C : R →+* p.Poly)
    p.derivedExtension.{u, 0} (presentationComparison p)

variable {R' : Type u} [CommRing R'] [Algebra R A] [Algebra R R']

attribute [local implicit_reducible] extensionOfScalarsComplexGeneral
  extensionOfScalarsComplex

/-- Derived extension of scalars along `e ∘ g` for `e` a ring isomorphism of the target: it is
derived extension along `g` followed by derived restriction along `e⁻¹`.  Both are left adjoint
to derived restriction along `e ∘ g`. -/
def derivedExtensionRingEquivRight
    {B C C' : Type u} [CommRing B] [CommRing C] [CommRing C']
    (g : B →+* C) (e : C ≃+* C')
    (F : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} C))
    (cmpF : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldF : F.IsLeftDerivedFunctor cmpF
      (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)))
    {g' : B →+* C'} (w : e.toRingHom.comp g = g')
    (G : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} C'))
    (cmpG : DerivedCategory.Q ⋙ G ⟶
      (ModuleCat.extendScalars.{u, u, u} g').mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldG : G.IsLeftDerivedFunctor cmpG
      (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ))) :
    G ≅ F ⋙ (ModuleCat.restrictScalars.{u} e.symm.toRingHom).mapDerivedCategory := by
  subst w
  have := ldF
  have := ldG
  let adjF := derivedExtensionScalarsAdjunction g F cmpF
  let adjG := derivedExtensionScalarsAdjunction (e.toRingHom.comp g) G cmpG
  let adjE := CategoryTheory.Adjunction.mapDerivedCategory
    (StacksDraft.DerivedRingIso.adjRestrictScalarsOfInv e.toRingHom e.symm.toRingHom
      e.left_inv e.right_inv)
  exact adjG.leftAdjointUniq ((adjF.comp adjE).ofNatIsoRight
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
      g e.toRingHom (e.toRingHom.comp g) rfl))

/-- Derived Hom along `e ∘ g` for `e` a ring isomorphism of the target: it is derived Hom along
`g` followed by derived restriction along `e⁻¹`.  Both are right adjoint to derived restriction
along `e ∘ g`. -/
def derivedHomRingEquivRight
    {B C C' : Type u} [CommRing B] [CommRing C] [CommRing C']
    (g : B →+* C) (e : C ≃+* C') :
    derivedHom.{u, 0} (e.toRingHom.comp g) ≅
      derivedHom.{u, 0} g ⋙
        (ModuleCat.restrictScalars.{u} e.symm.toRingHom).mapDerivedCategory := by
  let adjE := CategoryTheory.Adjunction.mapDerivedCategory
    (StacksDraft.DerivedRingIso.adjRestrictScalarsOfInv e.symm.toRingHom e.toRingHom
      e.right_inv e.left_inv)
  exact (derivedHomAdjunction.{u, u, 0} (e.toRingHom.comp g)).rightAdjointUniq
    ((adjE.comp (derivedHomAdjunction.{u, u, 0} g)).ofNatIsoLeft
      (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
        g e.toRingHom (e.toRingHom.comp g) rfl))

/-- **The base-change map of [stacks 0BZR], at the module universe of the rings.**  Let
`φ : R → A` admit the polynomial presentation `p` and let `A` and `R'` be Tor independent over
`R`.  The base-change map `φ^!(K) ⊗_A^L A' ⟶ (φ')^!(K ⊗_R^L R')`, natural in `K` in `D(R)`, for
`φ' : R' → A' = R' ⊗_R A`; here `φ^!` is read at `p` and `(φ')^!` at the base-changed
presentation, and the two derived tensor products are read at the given left-derived models of
extension of scalars. -/
@[no_expose]
def PolynomialPresentation.upperShriekTorIndependentBaseChange
    (p : PolynomialPresentation (algebraMap R A))
    (hTor : TorIndependent R A R')
    (bcR : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R'))
    (cmpR : DerivedCategory.Q ⋙ bcR ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldR : bcR.IsLeftDerivedFunctor cmpR
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (bcT : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (TensorProduct R R' A)))
    (cmpT : DerivedCategory.Q ⋙ bcT ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldT : bcT.IsLeftDerivedFunctor cmpT
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))) :
    p.upperShriekFunctor.{u, 0} ⋙ bcT ⟶
      bcR ⋙ (p.baseChange (R' := R')).upperShriekFunctor.{u, 0} := by
  let P := MvPolynomial (Fin p.variableCount) R
  let P' := MvPolynomial (Fin p.variableCount) R'
  let p' := p.baseChange (R' := R')
  let : Algebra P A := p.toRingHom.toAlgebra
  let : Algebra P P' := MvPolynomial.algebraMvPolynomial
  let : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq' p.commutes.symm
  let : IsScalarTower R P P' := inferInstance
  let : IsScalarTower R R' P' := inferInstance
  let : Algebra.IsPushout R R' P P' := inferInstance
  have hmap : algebraMap P P' = MvPolynomial.map (algebraMap R R') :=
    MvPolynomial.algebraMap_def
  let α : P →ₐ[R] A := p.toAlgHom
  have hTorP : TorIndependent P A P' :=
    torIndependent_mvPolynomialBaseChange p.variableCount α hTor
  let A0 := TensorProduct P A P'
  let T := TensorProduct R R' A
  let fA0 := (Algebra.TensorProduct.includeLeft : A →ₐ[P] A0).toRingHom
  let f0 := (Algebra.TensorProduct.includeRight : P' →ₐ[P] A0).toRingHom
  let fT := (Algebra.TensorProduct.includeRight : A →ₐ[R] T).toRingHom
  let DP := derivedExtensionScalarsGeneral.{u, u, u} (algebraMap P P')
  let DA := derivedExtensionScalarsGeneral.{u, u, u} fA0
  let bcP := DP.functor
  let bcA := DA.functor
  let δ := derivedHomBaseChange.{u, u, u, 0} hTorP bcP DP.comparison DP.isLeftDerived
    bcA DA.comparison DA.isLeftDerived
  let e : A0 ≃+* T := pushoutEquiv p
  let EC := (ModuleCat.restrictScalars.{u} e.symm.toRingHom).mapDerivedCategory
  have heA : e.toRingHom.comp fA0 = fT := by
    let : Algebra P' A0 := Algebra.TensorProduct.rightAlgebra
    ext a
    change Algebra.IsPushout.cancelBaseChangeAlg R R' P P' A
      ((Algebra.TensorProduct.commRight P P' A).symm (a ⊗ₜ[P] 1)) = 1 ⊗ₜ[R] a
    rw [Algebra.TensorProduct.commRight_symm_tmul,
      Algebra.IsPushout.cancelBaseChangeAlg_tmul]
  have heP : e.toRingHom.comp f0 = p'.toRingHom :=
    (baseChange_toRingHom_eq p rfl hmap).symm
  let eA : bcT ≅ bcA ⋙ EC :=
    derivedExtensionRingEquivRight fA0 e bcA DA.comparison DA.isLeftDerived heA bcT cmpT ldT
  let n : ℤ := p.variableCount
  let S0 := shiftFunctor (DerivedCategory (ModuleCat.{u} A0)) n
  let ST := shiftFunctor (DerivedCategory (ModuleCat.{u} T)) n
  let H := derivedHom.{u, 0} p.toRingHom
  let H0 := derivedHom.{u, 0} f0
  let HT : DerivedCategory (ModuleCat.{u} P') ⥤ DerivedCategory (ModuleCat.{u} T) :=
    derivedHom.{u, 0} p'.toRingHom
  let eH : HT ⋙ ST ≅ H0 ⋙ S0 ⋙ EC := by
    have h : HT ≅ H0 ⋙ EC := by
      have h0 := derivedHomRingEquivRight f0 e
      rw [heP] at h0
      exact h0
    exact Functor.isoWhiskerRight h ST ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft H0 (Functor.CommShift.commShiftIso EC n).symm
  let E := PolynomialPresentation.derivedExtension.{u, 0} p
  let E' := PolynomialPresentation.derivedExtension.{u, 0} p'
  let cP : R →+* P' := (MvPolynomial.C : R' →+* P').comp (algebraMap R R')
  have hsquare : cP = (algebraMap P P').comp (MvPolynomial.C : R →+* P) := by
    ext r
    rw [RingHom.comp_apply, RingHom.comp_apply, hmap, MvPolynomial.map_C]
  let eE : E ⋙ bcP ≅ bcR ⋙ E' := by
    have := DP.isLeftDerived
    have := ldR
    let adjE := presentationAdjunction p
    let adjP := derivedExtensionScalarsAdjunction (algebraMap P P') bcP DP.comparison
    let adjR := derivedExtensionScalarsAdjunction (algebraMap R R') bcR cmpR
    let adjE' := presentationAdjunction p'
    exact ((adjE.comp adjP).ofNatIsoRight
        (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
          (MvPolynomial.C : R →+* P) (algebraMap P P') cP hsquare)).leftAdjointUniq
      ((adjR.comp adjE').ofNatIsoRight
        (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
          (algebraMap R R') (MvPolynomial.C : R' →+* P') cP rfl))
  let eSource :
      p.upperShriekFunctor.{u, 0} ⋙ bcT ≅
        E ⋙ (H ⋙ bcA) ⋙ (S0 ⋙ EC) :=
    Functor.isoWhiskerLeft (E ⋙ H ⋙
        shiftFunctor (DerivedCategory (ModuleCat.{u} A)) n) eA ≪≫
      Functor.isoWhiskerLeft E (Functor.isoWhiskerLeft H
        (Functor.isoWhiskerRight (Functor.CommShift.commShiftIso bcA n) EC))
  let eTarget :
      E ⋙ (bcP ⋙ H0) ⋙ (S0 ⋙ EC) ≅ bcR ⋙ p'.upperShriekFunctor.{u, 0} :=
    Functor.isoWhiskerLeft (E ⋙ bcP) eH.symm ≪≫
      Functor.isoWhiskerRight eE (HT ⋙ ST)
  exact eSource.hom ≫
    Functor.whiskerLeft E (Functor.whiskerRight δ (S0 ⋙ EC)) ≫ eTarget.hom

/-- **Invertibility of the base-change map of [stacks 0BZR], given the compatibility of
[stacks 0E2A].**  Let `φ : R → A` admit the polynomial presentation `p`, let `A` and `R'` be
Tor independent over `R`, and let `A` be a perfect module over the polynomial algebra `P` of
`p` — which is the perfectness of `φ` that the source asks for, read at `p`.  Then the
base-change map `φ^!(K) ⊗_A^L A' ⟶ (φ')^!(K ⊗_R^L R')` of
`Dualizing.PolynomialPresentation.upperShriekTorIndependentBaseChange` is an isomorphism of
functors, hence invertible at every object of `D(R)` at once.

The proof is the source's.  The map is the base-change morphism for derived Hom of [stacks 0E29]
at the square `P, A, P', A ⊗_P P'` of the presentation, conjugated by isomorphisms of functors
and whiskered; that morphism is invertible by [stacks 0BZP], whose finiteness hypothesis at this
square is exactly perfectness of `A` over `P` and whose Tor independence is
`Dualizing.torIndependent_mvPolynomialBaseChange`.  No boundedness hypothesis on `K` appears,
because [stacks 0BZP] has none.

The hypothesis `hAct` is `Dualizing.KFlatAlgebraActionEq`, a form of the projection-formula
compatibility of [stacks 0E2A], quantified over all squares so that it can be read at the square
of the presentation; it is passed to
`Dualizing.isIso_derivedHomBaseChange_of_isPerfect_of_kFlatAlgebraActionEq`.  The same statement
with no such hypothesis, at every module universe, is
`Dualizing.PolynomialPresentation.isIso_upperShriekTorIndependentBaseChangeLarge`. -/
theorem PolynomialPresentation.isIso_upperShriekTorIndependentBaseChange
    (hAct : KFlatAlgebraActionEq.{u})
    (p : PolynomialPresentation (algebraMap R A))
    (hTor : TorIndependent R A R')
    (hperf : letI : Module p.Poly A := Module.compHom A p.toRingHom
      StacksDraft.Perfect.IsPerfectModule (R := p.Poly) A)
    (bcR : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R'))
    (cmpR : DerivedCategory.Q ⋙ bcR ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldR : bcR.IsLeftDerivedFunctor cmpR
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (bcT : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (TensorProduct R R' A)))
    (cmpT : DerivedCategory.Q ⋙ bcT ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldT : bcT.IsLeftDerivedFunctor cmpT
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))) :
    IsIso (p.upperShriekTorIndependentBaseChange hTor bcR cmpR ldR bcT cmpT ldT) := by
  let : Algebra p.Poly A := p.toRingHom.toAlgebra
  let : Algebra p.Poly (MvPolynomial (Fin p.variableCount) R') := MvPolynomial.algebraMvPolynomial
  delta PolynomialPresentation.upperShriekTorIndependentBaseChange
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ ?_)
  · infer_instance
  · refine @Functor.map_isIso _ _ _ _ _ _ _ _ ?_
    refine @Functor.map_isIso _ _ _ _ _ _ _ _ ?_
    refine @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ ?_ _
    exact isIso_derivedHomBaseChange_of_isPerfect_of_kFlatAlgebraActionEq.{u, u, u, 0} _ _ _ _ _ _ _
      (hAct _ _ _ _ _ _ _) hperf
  · refine @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) _

end Construction

end Dualizing

end
