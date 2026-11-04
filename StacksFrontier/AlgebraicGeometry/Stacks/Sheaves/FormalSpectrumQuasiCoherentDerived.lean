module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFormalSpectrumStages
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FormalSpectrumQuasiCoherentTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalQCDerivedComplete
public import StacksFrontier.RingTheory.Koszul.DerivedCompleteModelTransport
public import StacksFrontier.RingTheory.Koszul.NoetherianDerivedCompleteEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticRestrictionEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticDegreeZeroRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticDegreeZeroQuasiCoherent

/-!
# Quasi-coherent objects in the derived category of an affine formal spectrum (Stacks 0H0L)

Let `S` be a scheme, `A` an adic Noetherian topological `S`-algebra with ideal of definition `I`,
`X = Spf(A)` and `p : 𝒳 ⥤ (Sch/S)_{fppf}` the category fibred in sets associated to `X`.
Proposition 0H0L: `QC(𝒳)` is canonically equivalent to the category `D_comp(A, I)` of objects of
`D(A)` which are derived complete with respect to `I`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.quasiCoherentDerivedEquivalenceDerivedComplete`: **Stacks 0H0L**,
  the equivalence `QC(𝒳) ≌ D_comp(A, I)`.
* `AlgebraicGeometry.FormalSpace.qcEquivalenceOfStrict`: the case in which the powers of `I` never
  stabilize, following the source's proof (restriction to the stages via Lemma 0GZE, the ringed
  site `(ℕ, (A/I^{n+1}))` of Tag 0GZG, and Proposition 0GZK).
* `AlgebraicGeometry.FormalSpace.qcEquivalenceOfPowEqPowSucc`: the case in which the powers of
  `I` stabilize, `I^{N+1} = I^{N+2}`. Then `I^{N+1} = 0`, the stage `Spec(A/I^{N+1}) = Spec(A)` is
  a final object of `𝒳_{affine}`, `QC(𝒳) = D(A)` (Stacks 0H0R), and every object of `D(A)` is
  derived complete.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w' t u

namespace AlgebraicGeometry.FormalSpace

attribute [-instance] CategoryTheory.catToReflQuiver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {A : Type u} [CommRing A]
  [TopologicalSpace A] [IsTopologicalRing A] {I : Ideal A} (D : QuotientSystem B S hS A)
  (hA : TopologicalRing.IsAdic A) (hI : TopologicalRing.IsIdealOfDefinition I)
  [HasDerivedCategory.{w'} (ModuleCat.{max (u + 1) t} A)]

omit [HasDerivedCategory.{w'} (ModuleCat.{max (u + 1) t} A)] in
include hA hI in
/-- If `I^{N+1} = I^{N+2}`, then `I` is nilpotent. -/
theorem isNilpotent_of_pow_eq_pow_succ {N : ℕ} (hN : I ^ (N + 1) = I ^ (N + 2)) :
    IsNilpotent I :=
  ⟨N + 1, by rw [pow_eq_bot_of_pow_eq_pow_succ hA hI hN]; rfl⟩

/-- **Stacks 0H0L when the powers of `I` stabilize**: if `I^{N+1} = I^{N+2}`, then `I^{N+1} = 0`,
`Spec(A/I^{N+1}) = Spec(A)` is a final object of `𝒳_{affine}`, so `QC(𝒳) ≌ D(A)` by Stacks 0H0R,
and every object of `D(A)` is derived complete with respect to the nilpotent ideal `I`. -/
def qcEquivalenceOfPowEqPowSucc {N : ℕ} (hN : I ^ (N + 1) = I ^ (N + 2)) :
    Stack.quasiCoherentDerived.{u, u + 1, u, t} B S hS (formalSpectrumProjection D) ≌
      ObjectProperty.FullSubcategory
        (fun K : DerivedCategory (ModuleCat.{max (u + 1) t} A) => IsDerivedComplete I K) :=
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.qcEquivalenceDerivedCompleteOfTerminal.{t}
    (isTerminalStage D hA hI hN)
    (Stack.affineStructurePresheaf_comm B S hS (formalSpectrumProjection D))
    ((stageRingEquiv D hA hI N).trans
      ((Ideal.quotEquivOfEq (pow_eq_bot_of_pow_eq_pow_succ hA hI hN)).trans
        (RingEquiv.quotientBot A)))
    (isNilpotent_of_pow_eq_pow_succ hA hI hN)

/-! ### The ringed site `(ℕ, (A/I^{n+1}))` and Proposition 0GZK -/

section Koszul

variable {R : Type u} [CommRing R]

/-- The sheaf `𝒜 = (R/I^{n+1})` of Proposition 0GZK is concentrated in degree zero, with
presheaf of rings `n ↦ R/I^{n+1}`. -/
def liftedIdealPowData (J : Ideal R) :
    SheafOfModules.DifferentialGradedModule.DegreeZero.Data
      (Koszul.liftedIdealPowSheafAlgebra.{u} J)
      (Stacks.ChaoticSite.systemRing (Stacks.LiftedNat.liftDiagram
        (Koszul.idealPowQuotientAlgebraDiagram J))) :=
  Stacks.ChaoticSite.systemDegreeZeroData _
    (fun n => DifferentialGradedAlgebra.degreeZeroGrading_zero R (R ⧸ J ^ (n.unop.down + 1)))
    (fun n _ hk => DifferentialGradedAlgebra.degreeZeroGrading_eq_bot R
      (R ⧸ J ^ (n.unop.down + 1)) hk)
    (fun n x y => mul_comm (G := R ⧸ J ^ (n.unop.down + 1)) x y)

/-- The number of elements in a chosen finite generating family of an ideal of a Noetherian
ring. -/
def generatorsCount [IsNoetherianRing R] (J : Ideal R) : ℕ :=
  ((Submodule.fg_iff_exists_fin_generating_family).1 (IsNoetherian.noetherian J)).choose

/-- A finite family of generators of an ideal of a Noetherian ring. -/
def generators [IsNoetherianRing R] (J : Ideal R) : Fin (generatorsCount J) → R :=
  ((Submodule.fg_iff_exists_fin_generating_family).1 (IsNoetherian.noetherian J)).choose_spec.choose

/-- The ideal generated by `generators J` is `J`. -/
theorem span_generators [IsNoetherianRing R] (J : Ideal R) :
    Ideal.span (Set.range (generators J)) = J :=
  ((Submodule.fg_iff_exists_fin_generating_family).1
    (IsNoetherian.noetherian J)).choose_spec.choose_spec

end Koszul

section Lifted

variable [IsNoetherianRing A]

/-- The universe lift `ULift A` of a Noetherian ring `A` is Noetherian. -/
instance isNoetherianRing_ulift : IsNoetherianRing (ULift.{max (u + 1) t} A) :=
  isNoetherianRing_of_ringEquiv A (ULift.ringEquiv.{u, max (u + 1) t} (R := A)).symm

omit [HasDerivedCategory.{w'} (ModuleCat.{max (u + 1) t} A)] [TopologicalSpace A]
  [IsTopologicalRing A] [IsNoetherianRing A] in
/-- The image of `liftedIdeal I` under the ring isomorphism `ULift A ≃+* A` is `I`. -/
theorem map_liftedIdeal :
    (liftedIdeal.{t} I).map (ULift.ringEquiv.{u, max (u + 1) t} (R := A)) = I := by
  simpa using map_liftedIdeal_pow.{t} (I := I) 1

/-- **Proposition 0GZK for `(ℕ, (A/I^{n+1}))`**, read in `D(A)`: the quasi-coherent objects for
the sheaf `𝒜 = (A/I^{n+1})` on the chaotic site `ℕ` are the derived complete objects of `D(A)`.
The ring is lifted to the universe of the modules, `ULift A`, as Proposition 0GZK requires, and
then transported back to `A`. -/
def koszulDerivedCompleteEquivalence :
    (SheafOfModules.DifferentialGradedModule.Chaotic.QC
        (Koszul.liftedIdealPowSheafAlgebra.{max (u + 1) t} (liftedIdeal.{t} I))).FullSubcategory ≌
      ObjectProperty.FullSubcategory
        (fun K : DerivedCategory (ModuleCat.{max (u + 1) t} A) => IsDerivedComplete I K) :=
  let e := Koszul.idealPowKoszulDerivedCompleteEquivalences (liftedIdeal.{t} I)
    (generators (liftedIdeal.{t} I)) (span_generators _)
  (e.1.trans e.2).trans
    ((Koszul.derivedCompleteObjectsEquivalenceOfRingEquiv
      (ULift.ringEquiv.{u, max (u + 1) t} (R := A)) (liftedIdeal.{t} I)).trans
      (ObjectProperty.fullSubcategoryCongr (by rw [map_liftedIdeal])))

end Lifted

/-! ### Restriction to the stages (Differential Graded Sheaves, Lemma 0GZE) -/

section Restriction

/-- The sheaf of differential graded algebras on the small model of `𝒳_{affine}`: its structure
sheaf, placed in degree zero. -/
abbrev smallAlgebra :
    SheafOfModules.DifferentialGradedAlgebra.{max (u + 1) t, max (u + 1) t}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.PresheafOfModules.constCommRingSheaf
          (C := AsSmall.{max (u + 1) t} (formalSpectrumAffine D)) (ULift.{max (u + 1) t, 0} ℤ))) :=
  Stacks.ChaoticSite.systemAlgebra (Stacks.ChaoticSite.degreeZeroDiagram (smallStructure.{t} D))

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective in
/-- **Restriction to the stages is an equivalence on quasi-coherent objects**: Differential
Graded Sheaves, Lemma 0GZE, for the full subcategory of stages of the small model, every object of
which has a cofiltered category of arrows to the stages. -/
def smallRestrictionEquivalence :
    (SheafOfModules.DifferentialGradedModule.Chaotic.QC (smallAlgebra.{t} D)).FullSubcategory ≌
      (SheafOfModules.DifferentialGradedModule.Chaotic.QC
        ((smallAlgebra.{t} D).restrict (SmallIsStage.{t} D hA hI).ι)).FullSubcategory :=
  SheafOfModules.DifferentialGradedModule.ChaoticExtension.qcEquivalence
    (SmallIsStage.{t} D hA hI).ι (smallAlgebra.{t} D)

end Restriction

/-! ### The case of non-stabilizing powers, and Proposition 0H0L -/

section Main

open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)

omit [HasDerivedCategory.{w'} (ModuleCat.{max (u + 1) t} A)] [IsTopologicalRing A] in
/-- The ring of sections over `U` of the degree-zero system attached to the structure sheaf of the
small model is commutative. -/
theorem smallRing_comm (U) (x y : (Stacks.ChaoticSite.systemRing
    (Stacks.ChaoticSite.degreeZeroDiagram (smallStructure.{t} D))).obj U) : x * y = y * x :=
  mul_comm (G := (smallStructure.{t} D).obj U) x y

omit [HasDerivedCategory.{w'} (ModuleCat.{max (u + 1) t} A)] [TopologicalSpace A]
  [IsTopologicalRing A] in
/-- The ring of sections over `U` of the system `(ULift A ⧸ (liftedIdeal I) ^ (n + 1))` on `ℕ` is
commutative. -/
theorem natRing_comm (U) (x y : (Stacks.ChaoticSite.systemRing (Stacks.LiftedNat.liftDiagram
    (Koszul.idealPowQuotientAlgebraDiagram (liftedIdeal.{t} I)))).obj U) : x * y = y * x :=
  mul_comm (G := ULift.{max (u + 1) t} A ⧸ liftedIdeal.{t} I ^ (U.unop.down + 1)) x y

variable [IsNoetherianRing A]

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective in
/-- **Stacks 0H0L when the powers of `I` never stabilize.** Following the source's proof:
`QC(𝒳)` is read on the small model of `𝒳_{affine}` (a ring transport), and there, through the
identification `QC(O) = QC(O, 0)` of an algebra concentrated in degree zero, restriction to the
full subcategory `𝒞` of the stages `Spec(A/I^{n+1}) → X` is an equivalence (Differential Graded
Sheaves, Lemma 0GZE, every object of `𝒳_{affine}` mapping to some stage by Formal Spaces,
Lemma 0AIA); `(𝒞, O|_𝒞)` is the ringed site `(ℕ, (A/I^{n+1}))` of Section 24.35 (Tag 0GZG), and
Proposition 0GZK identifies its quasi-coherent objects with `D_comp(A, I)`. -/
def qcEquivalenceOfStrict (hstrict : ∀ n : ℕ, I ^ (n + 1) ≠ I ^ (n + 2)) :
    Stack.quasiCoherentDerived.{u, u + 1, u, t} B S hS (formalSpectrumProjection D) ≌
      ObjectProperty.FullSubcategory
        (fun K : DerivedCategory (ModuleCat.{max (u + 1) t} A) => IsDerivedComplete I K) :=
  let bcU := baseChangeDataOfComm.{max (u + 1) t, max (u + 1) t, max (u + 1) t, max (u + 1) t} _
    (smallRing_comm.{t} D)
  let bcC := baseChangeDataOfComm.{max (u + 1) t, max (u + 1) t, max (u + 1) t, max (u + 1) t}
    ((SmallIsStage.{t} D hA hI).ι.op ⋙ Stacks.ChaoticSite.systemRing
      (Stacks.ChaoticSite.degreeZeroDiagram (smallStructure.{t} D)))
    (fun _ => smallRing_comm.{t} D _)
  let bcN := baseChangeDataOfComm.{max (u + 1) t, max (u + 1) t, max (u + 1) t, max (u + 1) t} _
    (natRing_comm.{t} (I := I))
  (BaseChangeData.qcToMaxEquivalence (Stack.affineBaseChangeData.{u, u + 1, u, t} B S hS
      (formalSpectrumProjection D))).trans <|
  ((smallTransport.{t} D).qcEquivalence.{t} _ bcU).trans <|
  (SheafOfModules.DifferentialGradedModule.DegreeZero.qcEquivalence
    (Stacks.ChaoticSite.degreeZeroDiagramData (smallStructure.{t} D)) bcU).symm.trans <|
  (smallRestrictionEquivalence.{t} D hA hI).trans <|
  (SheafOfModules.DifferentialGradedModule.DegreeZero.qcEquivalence
    ((Stacks.ChaoticSite.degreeZeroDiagramData (smallStructure.{t} D)).restrict
      (SmallIsStage.{t} D hA hI).ι) bcC).trans <|
  ((stageNatTransport.{t} D hstrict).qcEquivalence.{max (u + 1) t} bcC bcN).trans <|
  (SheafOfModules.DifferentialGradedModule.DegreeZero.qcEquivalence
    (liftedIdealPowData (liftedIdeal.{t} I)) bcN).symm.trans <|
  koszulDerivedCompleteEquivalence.{w', t}

open Classical in
/-- **Stacks 0H0L.** Let `S` be a scheme and `X = Spf(A)`, where `A` is an adic Noetherian
topological `S`-algebra with ideal of definition `I` (More on Algebra, Definition 07E8; Formal
Spaces, Definition 0AIF). Let `p : 𝒳 → (Sch/S)_{fppf}` be the category fibred in sets associated
to the functor `X` (Categories, Example 04TM). Then `QC(𝒳)` (Definition 0H0H) is equivalent to the
category `D_comp(A, I)` of objects of `D(A)` which are derived complete with respect to `I`.

The equivalence is constructed: if the powers of `I` stabilize, `I^{N+1} = I^{N+2}`, then
`I^{N+1} = 0`, `Spec(A) = Spec(A/I^{N+1})` is a final object of `𝒳_{affine}` and the equivalence
is `RΓ(Spec(A), -)` (Stacks 0H0R), every object of `D(A)` being derived complete; otherwise it is
the composite of the source's proof, `qcEquivalenceOfStrict`. Here `D(A)` is the derived category
of `A`-modules in the universe `max (u + 1) t` of the modules of `QC(𝒳)`, in any model. -/
@[stacks 0H0L "QC(𝒳) ≌ D_comp(A, I) for 𝒳 the category fibred in sets of Spf(A), A an adic \
Noetherian topological S-algebra with ideal of definition I"]
def quasiCoherentDerivedEquivalenceDerivedComplete :
    Stack.quasiCoherentDerived.{u, u + 1, u, t} B S hS (formalSpectrumProjection D) ≌
      ObjectProperty.FullSubcategory
        (fun K : DerivedCategory (ModuleCat.{max (u + 1) t} A) => IsDerivedComplete I K) :=
  if h : ∃ N : ℕ, I ^ (N + 1) = I ^ (N + 2) then
    qcEquivalenceOfPowEqPowSucc D hA hI (Nat.find_spec h)
  else
    qcEquivalenceOfStrict D hA hI (fun n hn => h ⟨n, hn⟩)

end Main

end AlgebraicGeometry.FormalSpace

end
