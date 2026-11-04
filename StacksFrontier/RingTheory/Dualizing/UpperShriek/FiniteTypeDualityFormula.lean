module

public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsModelComp
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.HomShift.DerivedShift
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Dualizing
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialDualityBaseChange
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialExtension
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.SurjectiveAnyPresentation

/-!
# Algebraic upper shriek as the dual of the base change of the dual, in general

[Stacks, Tag 0E9L] for an **arbitrary finite-type** homomorphism `φ : A →+* B` of Noetherian
rings.  This file assembles the general case out of the two halves the source uses.

## Main results

* `Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_natIso_dualizingDerivedHom` —
  **[Stacks, Tag 0E9L] in general**.

## Implementation notes

The hypothesis of surjectivity is removed, not weakened.  A presentation `p` of `φ` factors it as
`A → P = A[x_1, …, x_n] ↠ B`, and each half of that factorization is available unconditionally:

* the surjection `q : P ↠ B` is handled by `Dualizing.derivedHomNatIsoDualizingDerivedHom`, the
  engine of `StacksFrontier.RingTheory.Dualizing.UpperShriek.DualityFormula`, which is the tag for
  derived coextension of scalars `RHom_P(B, -)` along an *arbitrary* ring homomorphism and which
  carries no hypothesis beyond `P` Noetherian — a surjection has no variables, so no base-change
  comparison enters it;
* the polynomial extension `c : A → P` is handled by
  `Dualizing.mvPolynomialDualityBaseChangeNatIso`, flat base change of derived Hom along `A → P`,
  which is the *degenerate* square of [Stacks, Tag 0E29] and is the unconditional [Stacks,
  Tag 0A6A], not the Tor-independent square of [Stacks, Tag 0BZM].

That is why nothing here carries `Dualizing.KFlatAlgebraActionEq`.  The source's own reduction
composes upper shriek along the two halves by [Stacks, Tag 0BZT], which this library has in
general only modulo that keystone; the composition is **avoided** by reading the surjective half
at the object `K ⊗_A^L P` instead, so that upper shriek never has to be composed:
`p.upperShriekFunctor` is by definition `RHom_P(B, - ⊗_A^L P)[n]`, and the two halves apply to the
outer `RHom_P(B, -)` and to the inner `- ⊗_A^L P` separately.

The chain, for `K` in `D_Coh(A)`, is

`φ^!(K) = RHom_P(B, K ⊗_A^L P)[n]`
`      ≅ RHom_B(RHom_P(K ⊗_A^L P, ω_P) ⊗_P^L B, RHom_P(B, ω_P))[n]`  (the surjective half at
`K ⊗_A^L P`, which lies in `D_Coh(P)`)
`      ≅ RHom_B(RHom_A(K, ω) ⊗_A^L P ⊗_P^L B, RHom_P(B, ω_P))[n]`  (the polynomial half)
`      ≅ RHom_B(RHom_A(K, ω) ⊗_A^L B, RHom_P(B, ω_P)[n]) = D_B(D_A(K) ⊗_A^L B)`

the last step moving the shift into the second argument of `RHom_B` by
`Dualizing.dualizingDerivedHomShiftIso` and composing the two base changes by
`StacksDraft.DerivedExtensionScalarsModelComp.compModelIso`.  Note that `ω_P = ω ⊗_A^L P` is a
dualizing complex for `P` by [Stacks, Tag 0A7J], and that `ω_B = φ^!(ω)` is literally
`RHom_P(B, ω_P)[n]`, which is what makes the last line the statement of the tag.

`K ⊗_A^L P` lies in `D_Coh(P)`: base change of a finite module is finite, which is
`Dualizing.PolynomialPresentation.derivedExtension_derivedCategoryB`.  The resulting functor into
`D_Coh(P)` is `CategoryTheory.ObjectProperty.lift`, whose composite with the inclusion is the
original functor *definitionally*, so no transport is needed to feed the surjective half.

The two models of derived extension of scalars are taken to be the chosen ones,
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral`, rather than arbitrary: the
composition isomorphism `Ec ⋙ Eq ≅ Eφ` is what identifies the two inner base changes, and it is
available at the chosen model of the composite.  An arbitrary model of the composite is recovered
from it by uniqueness of left derived functors, which is
`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_natIso_dualizingDerivedHom_model`.

## References

* [Stacks Project, Tag 0E9L](https://stacks.math.columbia.edu/tag/0E9L)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A7J](https://stacks.math.columbia.edu/tag/0A7J)
* [Stacks Project, Tag 0BZJ](https://stacks.math.columbia.edu/tag/0BZJ)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

/-! ### Transporting the outer dual along an isomorphism of the inner functor -/

/-- The isomorphism of `CategoryTheory.Functor.rightOp`s induced by an isomorphism of
contravariant functors.  Mathlib has `CategoryTheory.NatTrans.rightOp` but no `NatIso` form. -/
def rightOpIso {J : Type*} [Category J] {D : Type*} [Category D] {F G : Jᵒᵖ ⥤ D} (e : F ≅ G) :
    G.rightOp ≅ F.rightOp where
  hom := NatTrans.rightOp e.hom
  inv := NatTrans.rightOp e.inv
  hom_inv_id := by rw [← NatTrans.rightOp_comp, e.inv_hom_id, NatTrans.rightOp_id]
  inv_hom_id := by rw [← NatTrans.rightOp_comp, e.hom_inv_id, NatTrans.rightOp_id]

/-- Changing the inner functor of `K ↦ RHom_B(H(K), Ω)` along an isomorphism of `H`. -/
def dualizingDerivedHomRightOpIso {J : Type*} [Category J] {B : Type u} [CommRing B]
    {F G : Jᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} B)} (e : F ≅ G)
    (Ω : DerivedCategory (ModuleCat.{u} B)) :
    G.rightOp ⋙ dualizingDerivedHomFunctor.{u, u} B Ω ≅
      F.rightOp ⋙ dualizingDerivedHomFunctor.{u, u} B Ω :=
  Functor.isoWhiskerRight (rightOpIso e) (dualizingDerivedHomFunctor.{u, u} B Ω)

/-! ### The two base changes of a presentation compose -/

namespace PolynomialPresentation

variable {A B : Type u} [CommRing A] [CommRing B] {φ : A →+* B}

/-- The chosen model of derived extension of scalars along the surjection of a presentation. -/
abbrev surjectionDerivedExtension (p : PolynomialPresentation φ) :
    CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, u, u, u + 1, u + 1}
      p.toRingHom :=
  CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u, u + 1, u + 1}
    p.toRingHom

/-- The chosen model of derived extension of scalars along the presented homomorphism. -/
abbrev totalDerivedExtension (φ : A →+* B) :
    CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, u, u, u + 1, u + 1}
      φ :=
  CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u, u + 1, u + 1} φ

/-- **The two derived base changes of a presentation compose to the derived base change along the
presented homomorphism**: `(- ⊗_A^L P) ⊗_P^L B ≅ - ⊗_A^L B`.  Both factors are models of derived
extension of scalars, the first the degreewise one available because `P` is free over `A`, so the
composite is a model of derived extension of scalars along `q ∘ c = φ`; this is
`StacksDraft.DerivedExtensionScalarsModelComp.compModelIso`. -/
def derivedExtensionCompIso (p : PolynomialPresentation φ) :
    p.derivedExtension.{u, u} ⋙ p.surjectionDerivedExtension.functor ≅
      (totalDerivedExtension φ).functor :=
  StacksDraft.DerivedExtensionScalarsModelComp.compModelIso.{u, u, u, u, u + 1, u + 1, u + 1}
    (MvPolynomial.C : A →+* p.Poly) p.toRingHom (mvPolynomialExtension A p.variableCount)
    (mvPolynomialExtensionFactors A p.variableCount).hom
    p.surjectionDerivedExtension.functor p.surjectionDerivedExtension.comparison
    (hFld := mvPolynomialExtension_isLeftDerivedFunctor A p.variableCount)
    (hGld := p.surjectionDerivedExtension.isLeftDerived) φ p.commutes

/-! ### The base change of a presentation on the coherent derived category -/

/-- Derived base change along the polynomial algebra of a presentation keeps the cohomology
modules finite: base change of a finite module is finite.  This is
`Dualizing.PolynomialPresentation.derivedExtension_derivedCategoryB` read at the predicate
`Dualizing.hasFiniteCohomology`. -/
theorem derivedExtension_hasFiniteCohomology (p : PolynomialPresentation φ)
    {K : DerivedCategory (ModuleCat.{u} A)} (hK : hasFiniteCohomology.{u, u} A K) :
    hasFiniteCohomology.{u, u} p.Poly (p.derivedExtension.{u, u}.obj K) :=
  p.derivedExtension_derivedCategoryB hK

/-- Derived base change along the polynomial algebra of a presentation, as a functor
`D_Coh(A) ⥤ D_Coh(P)`.  Its composite with the inclusion of `D_Coh(P)` is the inclusion of
`D_Coh(A)` followed by base change, *definitionally*, by
`CategoryTheory.ObjectProperty.liftCompιIso`. -/
def coherentDerivedExtension (p : PolynomialPresentation φ) :
    (hasFiniteCohomology.{u, u} A).FullSubcategory ⥤
      (hasFiniteCohomology.{u, u} p.Poly).FullSubcategory :=
  (hasFiniteCohomology.{u, u} p.Poly).lift
    ((hasFiniteCohomology.{u, u} A).ι ⋙ p.derivedExtension.{u, u})
    (fun X => p.derivedExtension_hasFiniteCohomology X.property)

/-! ### Tag 0E9L in general -/

/-- **[Stacks, Tag 0E9L] for an arbitrary finite-type `φ`, as an isomorphism of functors on
`D_Coh(A)`.**  Let `φ : A →+* B` be a homomorphism of finite type with `A` Noetherian, let `p` be
any polynomial presentation of `φ` and let `ω` be a dualizing complex for `A`.  Write `φ^!` for
the algebraic upper shriek functor of `p`, put `ω_B = φ^!(ω)`, `D_A(-) = RHom_A(-, ω)` and
`D_B(-) = RHom_B(-, ω_B)`.  Then

`φ^!(K) ≅ D_B(D_A(K) ⊗_A^L B)`

as an isomorphism of functors on `D_Coh(A)`.

**No surjectivity, and no projection-formula keystone.**  The surjective case is
`Dualizing.upperShriekFunctor_natIso_dualizingDerivedHom_of_surjective`; the passage to a general
finite-type `φ` is made here by reading that statement's engine — the tag for derived coextension
of scalars along an arbitrary ring homomorphism — at the object `K ⊗_A^L P` over the polynomial
algebra of the presentation, and feeding it the flat base change of derived Hom along `A → P`.
That base change is the unconditional [Stacks, Tag 0A6A], not the Tor-independent square of
[Stacks, Tag 0BZM]; so unlike [Stacks, Tag 0BZT] in general
(`Dualizing.PolynomialPresentation.exists_upperShriekComp_of_finiteType`) this carries no
`Dualizing.KFlatAlgebraActionEq`.  See the module documentation for the chain.

The derived base change `- ⊗_A^L B` is the chosen model; for an arbitrary model see
`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_natIso_dualizingDerivedHom_model`.
The statement is a `Nonempty` because the adjunction of [Stacks, Tag 0A70] that the engine
consumes is itself only known to exist. -/
@[stacks 0E9L "in general: an arbitrary finite-type φ of Noetherian rings at an arbitrary \
polynomial presentation, as an isomorphism of functors on D_Coh(A), with no surjectivity and no \
projection-formula keystone"]
theorem nonempty_upperShriekFunctor_natIso_dualizingDerivedHom [IsNoetherianRing A]
    (p : PolynomialPresentation φ) (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : IsDualizingComplex ω) :
    Nonempty ((hasFiniteCohomology.{u, u} A).ι ⋙ p.upperShriekFunctor.{u, u} ≅
      (hasFiniteCohomology.{u, u} A).ι ⋙ dualizingBaseChangeFunctor.{u, u} φ
        (totalDerivedExtension φ) ω (p.upperShriekFunctor.{u, u}.obj ω)) := by
  obtain ⟨adj⟩ := restrictScalarsDerived_adj_derivedHom.{u, u, u} p.toRingHom
  have hωP : IsDualizingComplex (p.derivedExtension.{u, u}.obj ω) :=
    mvPolynomialBaseChange_isDualizingComplex p.variableCount ω hω
  let ι := (hasFiniteCohomology.{u, u} A).ι
  let Eq := p.surjectionDerivedExtension
  let iStar := (ModuleCat.restrictScalars.{u, u, u} p.toRingHom).mapDerivedCategory
  let Ω₀ := (derivedHom.{u, u, u} p.toRingHom).obj (p.derivedExtension.{u, u}.obj ω)
  -- the surjective half, read at `K ⊗_A^L P`
  let e₁ := derivedHomNatIsoDualizingDerivedHom.{u, u} p.toRingHom Eq iStar adj
    (fun N F => (ProjectionFormula.derivedProjNatIso.{u, u} p.toRingHom Eq iStar adj N).app F)
    (fun N {_ _} f =>
      (ProjectionFormula.derivedProjNatIso.{u, u} p.toRingHom Eq iStar adj N).hom.naturality f)
    (fun {_ _} m F => NatTrans.congr_app
      ((ProjectionFormula.derivedProjBifunctorNatIso.{u, u} p.toRingHom Eq iStar
        adj).hom.naturality m) F)
    (p.derivedExtension.{u, u}.obj ω) hωP
  -- the polynomial half
  let ν := mvPolynomialDualityBaseChangeNatIso A p.variableCount ι
    (fun X => X.property) ω hω
  let e₂ : ι.op ⋙ dualizingDerivedHomFunctor.{u, u} A ω ⋙ (totalDerivedExtension φ).functor ≅
      (ι ⋙ p.derivedExtension.{u, u}).op ⋙
        dualizingDerivedHomFunctor.{u, u} p.Poly (p.derivedExtension.{u, u}.obj ω) ⋙
          Eq.functor :=
    (Functor.isoWhiskerLeft (ι.op ⋙ dualizingDerivedHomFunctor.{u, u} A ω)
        p.derivedExtensionCompIso).symm ≪≫
      Functor.isoWhiskerRight ν Eq.functor
  let e₃ := Functor.isoWhiskerLeft p.coherentDerivedExtension e₁ ≪≫
    dualizingDerivedHomRightOpIso e₂ Ω₀
  exact ⟨Functor.isoWhiskerRight e₃
      (shiftFunctor (DerivedCategory (ModuleCat.{u} B)) (p.variableCount : ℤ)) ≪≫
    Functor.isoWhiskerLeft ι (Functor.isoWhiskerLeft
      (dualizingDerivedHomFunctor.{u, u} A ω ⋙ (totalDerivedExtension φ).functor).rightOp
      (dualizingDerivedHomShiftIso.{u, u} B Ω₀ (p.variableCount : ℤ)).symm)⟩

/-- Changing the model of derived base change in `Dualizing.dualizingBaseChangeFunctor` along an
isomorphism of the two base-change functors. -/
def dualizingBaseChangeFunctorIsoOfModelIso (φ : A →+* B)
    (E E' : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, u, u,
      u + 1, u + 1} φ)
    (e : E.functor ≅ E'.functor) (ωA : DerivedCategory (ModuleCat.{u} A))
    (ωB : DerivedCategory (ModuleCat.{u} B)) :
    dualizingBaseChangeFunctor.{u, u} φ E' ωA ωB ≅
      dualizingBaseChangeFunctor.{u, u} φ E ωA ωB :=
  dualizingDerivedHomRightOpIso
    (Functor.isoWhiskerLeft (dualizingDerivedHomFunctor.{u, u} A ωA) e) ωB

/-- **[Stacks, Tag 0E9L] in general, at an arbitrary model of derived base change.**  This is
`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_natIso_dualizingDerivedHom` with the
chosen model of `- ⊗_A^L B` replaced by an arbitrary one.  Two models of derived extension of
scalars along `φ` are isomorphic by uniqueness of the total left derived functor,
`CategoryTheory.Functor.leftDerivedNatIso`, and
`Dualizing.PolynomialPresentation.dualizingBaseChangeFunctorIsoOfModelIso` carries that
isomorphism into the right-hand side of the tag. -/
@[stacks 0E9L "in general, at an arbitrary model of derived base change as well as an arbitrary \
polynomial presentation"]
theorem nonempty_upperShriekFunctor_natIso_dualizingDerivedHom_model [IsNoetherianRing A]
    (p : PolynomialPresentation φ)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, u, u,
      u + 1, u + 1} φ)
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : IsDualizingComplex ω) :
    Nonempty ((hasFiniteCohomology.{u, u} A).ι ⋙ p.upperShriekFunctor.{u, u} ≅
      (hasFiniteCohomology.{u, u} A).ι ⋙ dualizingBaseChangeFunctor.{u, u} φ E ω
        (p.upperShriekFunctor.{u, u}.obj ω)) := by
  obtain ⟨e⟩ := p.nonempty_upperShriekFunctor_natIso_dualizingDerivedHom ω hω
  let eModel : E.functor ≅ (totalDerivedExtension φ).functor :=
    Functor.leftDerivedNatIso E.functor (totalDerivedExtension φ).functor E.comparison
      (totalDerivedExtension φ).comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) (Iso.refl _)
  exact ⟨e ≪≫ Functor.isoWhiskerLeft (hasFiniteCohomology.{u, u} A).ι
    (dualizingBaseChangeFunctorIsoOfModelIso φ E (totalDerivedExtension φ) eModel ω
      (p.upperShriekFunctor.{u, u}.obj ω))⟩

end PolynomialPresentation

end Dualizing

end
