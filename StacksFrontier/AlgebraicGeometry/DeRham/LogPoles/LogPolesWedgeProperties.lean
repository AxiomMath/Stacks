module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogDifferentialGradedAlgebra
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogExteriorPower
public import StacksCore.Tactic.StacksAttribute

/-!
# The multiplicative structure of the de Rham complex of log poles

Let `f : X ⟶ S` be a morphism of schemes and let `Y ⊆ X` be an effective Cartier divisor, cut out
by `I`, for which the de Rham complex of log poles is defined ([Stacks, Tag 0FMV]). This file
records [Stacks, Tag 0FUP] for the de Rham complex of log poles
`AlgebraicGeometry.Scheme.Hom.deRhamComplexLogPoles` of [Stacks, Tag 0FUA], one statement for
each of its four clauses.

* Clause (1): `AlgebraicGeometry.Scheme.Hom.logFormsWedgeMap_spec`. The wedge product of forms
  extends uniquely to `𝒪_X`-bilinear maps
  `Ω^p_{X/S}(log Y) × Ω^q_{X/S}(log Y) → Ω^{p+q}_{X/S}(log Y)`,
  and the extension satisfies the Leibniz rule.
* Clause (2): `AlgebraicGeometry.Scheme.Hom.logPolesDifferentialGradedAlgebra_spec`. With this
  multiplication `Ω^•_{X/S}(log Y)` is a sheaf of differential graded `f⁻¹𝒪_S`-algebras, and the
  inclusion `Ω^•_{X/S} ⟶ Ω^•_{X/S}(log Y)` is a homomorphism of them.
* Clause (3): `AlgebraicGeometry.Scheme.Hom.logExteriorDesc_spec`. Via the multiplication of (1),
  `Ω^p_{X/S}(log Y) = ⋀^p Ω^1_{X/S}(log Y)`: the unital homomorphism of sheaves of graded
  `𝒪_X`-algebras from the exterior algebra of `Ω^1_{X/S}(log Y)` to `Ω^•_{X/S}(log Y)` which is
  the identity in degree one is an isomorphism in every degree.
* Clause (4): `AlgebraicGeometry.Scheme.Hom.logRes_logFormsWedge_spec`. `Res(ω ∧ η) = Res(ω) ∧
η|_Y`.

## Implementation notes

The degree-`n` sheaf `Ω^n_{X/S}(log Y)` is `AlgebraicGeometry.Scheme.Hom.logPolesForms`, its
differential is `AlgebraicGeometry.Scheme.Hom.logD` and its residue
`AlgebraicGeometry.Scheme.Hom.logRes`, the terms, differential and residue of the complex and the
sequence of Tags 0FUA and 0FMW. Degrees are natural numbers, so the two sides of an identity may
live in degrees which agree only up to the arithmetic of `ℕ` (`(p + 1) + q` and `(p + q) + 1`);
the transport between them is `AlgebraicGeometry.Scheme.Hom.logFormsCast`.

The differential graded algebra of clause (2) is indexed by `ℤ`, as
`SheafOfModules.DifferentialGradedAlgebra` requires, on the extension by zero
`AlgebraicGeometry.Scheme.Hom.deRhamComplexLogPolesInt` of the complex of Tag 0FUA; its source is
the relative de Rham complex as the differential graded algebra of [Stacks, Tag 0FU6],
`AlgebraicGeometry.SheafOfModules.relativeDeRhamDifferentialGradedAlgebra`.

In clause (4) the residue of a form of degree `0` is zero, its target `Ω^{-1}_{Y/S}` being zero;
the second conjunct records the corresponding statement, that `Res(ω ∧ η)` vanishes for `ω` of
degree `0`.

## References

* [Stacks Project, Tag 0FUP](https://stacks.math.columbia.edu/tag/0FUP)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

/-- **Stacks Project, Tag 0FUP, clause (1).** The wedge products
`Ω^p_{X/S} × Ω^q_{X/S} → Ω^{p+q}_{X/S}` extend to `𝒪_X`-bilinear maps
`Ω^p_{X/S}(log Y) × Ω^q_{X/S}(log Y) → Ω^{p+q}_{X/S}(log Y)`, namely
`AlgebraicGeometry.Scheme.Hom.logFormsWedgeMap`; the extension is unique among all `𝒪_X`-bilinear
maps extending the wedge product; and it satisfies the Leibniz rule
`d(ω ∧ η) = d(ω) ∧ η + (-1)^{deg ω} ω ∧ d(η)`. -/
@[stacks 0FUP "clause (1): existence, uniqueness among all O_X-bilinear extensions (the Leibniz \
rule is not needed for uniqueness), and the Leibniz rule"]
theorem logFormsWedgeMap_spec :
    (∀ (p q : ℕ) (W : X.Opens) (ω : Γ(relativeDifferentialForms f (p : ℤ), W))
      (η : Γ(relativeDifferentialForms f (q : ℤ), W)),
      (logFormsWedgeMap hI hlog p q).app (op W) ((logPolesFormsInclusion f I p).val.app (op W) ω)
          ((logPolesFormsInclusion f I q).val.app (op W) η) =
        (logPolesFormsInclusion f I (p + q)).val.app (op W) (formWedge f p q W ω η)) ∧
    (∀ (p q : ℕ) (m : _root_.SheafOfModules.BilinearMap (logPolesForms f I p)
        (logPolesForms f I q) (logPolesForms f I (p + q))),
      (∀ (W : X.Opens) (ω : Γ(relativeDifferentialForms f (p : ℤ), W))
        (η : Γ(relativeDifferentialForms f (q : ℤ), W)),
        m.app (op W) ((logPolesFormsInclusion f I p).val.app (op W) ω)
            ((logPolesFormsInclusion f I q).val.app (op W) η) =
          (logPolesFormsInclusion f I (p + q)).val.app (op W) (formWedge f p q W ω η)) →
      m = logFormsWedgeMap hI hlog p q) ∧
    (∀ (p q : ℕ) (W : X.Opens) (φ : (logPolesForms f I p).val.obj (op W))
      (ψ : (logPolesForms f I q).val.obj (op W)),
      logD hI hlog ((logFormsWedgeMap hI hlog p q).app (op W) φ ψ) =
        logFormsCast (Nat.add_right_comm p 1 q)
            ((logFormsWedgeMap hI hlog (p + 1) q).app (op W) (logD hI hlog φ) ψ) +
          ((-1 : ℤ) ^ p) • (logFormsWedgeMap hI hlog p (q + 1)).app (op W) φ (logD hI hlog ψ)) :=
  ⟨fun _ _ _ ω η => logFormsWedge_logPolesFormsInclusion hI hlog ω η,
    fun _ _ m hm => eq_logFormsWedgeMap hI hlog m hm,
    fun _ _ _ φ ψ => logD_logFormsWedge hI hlog φ ψ⟩

/-- **Stacks Project, Tag 0FUP, clause (2).** With the multiplication of clause (1), the de Rham
complex of log poles `Ω^•_{X/S}(log Y)` of Tag 0FUA is a sheaf of differential graded
`f⁻¹𝒪_S`-algebras `A`, and the inclusion `Ω^•_{X/S} ⟶ Ω^•_{X/S}(log Y)` underlies a
homomorphism of sheaves of differential graded algebras from the relative de Rham complex of
Tag 0FU6 to `A`. -/
@[stacks 0FUP "clause (2): the sheaf of differential graded f⁻¹O_S-algebras on the complex of \
0FUA, with the multiplication of clause (1), and the inclusion as a homomorphism"]
theorem logPolesDifferentialGradedAlgebra_spec :
    ∃ (A : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (baseRingSheaf f))
      (φ : _root_.SheafOfModules.DifferentialGradedAlgebra.Hom
        (AlgebraicGeometry.SheafOfModules.relativeDeRhamDifferentialGradedAlgebra
          (inverseImageStructureMap f)) A),
      A.complex = deRhamComplexLogPolesInt f I hI hlog ∧
      (∀ (p q : ℕ) (U : X.Opensᵒᵖ) (x : (A.complex.X (p : ℤ)).val.obj U)
        (y : (A.complex.X (q : ℤ)).val.obj U) (x' : (logPolesForms f I p).val.obj U)
        (y' : (logPolesForms f I q).val.obj U), HEq x x' → HEq y y' →
          HEq ((A.mul (p : ℤ) (q : ℤ)).app U x y)
            ((logFormsWedgeMap hI hlog p q).app U x' y')) ∧
      (∀ U : X.Opensᵒᵖ, HEq (A.one.eval U)
        ((logPolesFormsInclusion f I 0).val.app U (formOne U.unop))) ∧
      HEq φ.toHomologicalComplex (deRhamComplexLogPolesIntInclusion f I hI hlog) :=
  ⟨logPolesDifferentialGradedAlgebra f I hI hlog,
    logPolesDifferentialGradedAlgebraInclusion f I hI hlog, rfl,
    fun p q U x y x' y' hx hy =>
      logPolesDifferentialGradedAlgebra_mul f I hI hlog p q U x y x' y' hx hy,
    logPolesDifferentialGradedAlgebra_one f I hI hlog, HEq.rfl⟩

/-- **Stacks Project, Tag 0FUP, clause (3).** Via the maps of clause (1),
`Ω^p_{X/S}(log Y) = ⋀^p(Ω^1_{X/S}(log Y))`. The forms with logarithmic poles form a sheaf of graded
`𝒪_X`-algebras `AlgebraicGeometry.Scheme.Hom.logGradedAlgebra` under the wedge product of
clause (1); the unital homomorphism `AlgebraicGeometry.Scheme.Hom.logExteriorDesc` to it from the
exterior algebra of `Ω^1_{X/S}(log Y)` is the identity of `Ω^1_{X/S}(log Y)` in degree one, so in
degree `p` it sends `φ₁ ∧ ⋯ ∧ φ_p` to the wedge product of the `φᵢ`, and it is an isomorphism in
every degree `p`. -/
@[stacks 0FUP "clause (3): the map from the p-th exterior power of Ω¹(log Y) induced by the \
wedge product of clause (1) is an isomorphism onto Ω^p(log Y), for every p"]
theorem logExteriorDesc_spec :
    (∀ (p q : ℕ) (U : X.Opensᵒᵖ) (x : (logPolesForms f I p).val.obj U)
      (y : (logPolesForms f I q).val.obj U),
      ((logGradedAlgebra f I hI hlog).mul (p : ℤ) (q : ℤ)).app U x y =
        (logFormsWedgeMap hI hlog p q).app U x y) ∧
    Scheme.Modules.exteriorGenerator (logPolesForms f I 1) ≫ (logExteriorDesc f I hI hlog).app 1 =
      logGenerator f I hI hlog ∧
    ∀ p : ℕ, IsIso ((logExteriorDesc f I hI hlog).app (p : ℤ)) :=
  ⟨fun _ _ _ _ _ => rfl, logExteriorDesc_generator f I hI hlog,
    isIso_logExteriorDesc_app f I hI hlog⟩

/-- **Stacks Project, Tag 0FUP, clause (4).** The residue
`Res : Ω^•_{X/S}(log Y) → Ω^•_{Y/S}[-1]` satisfies `Res(ω ∧ η) = Res(ω) ∧ η|_Y` for a local
section `ω` of `Ω^p_{X/S}(log Y)` and a local section `η` of `Ω^q_{X/S}`: in degree `p + 1` this
is the first conjunct; in degree `0` the residue vanishes, and so does `Res(ω ∧ η)`, the second
conjunct. -/
@[stacks 0FUP "clause (4), in every degree of ω: the formula in degree p + 1, and the vanishing \
of Res(ω ∧ η) for ω of degree 0, where Res(ω) = 0"]
theorem logRes_logFormsWedge_spec :
    (∀ (p q : ℕ) (W : X.Opens) (ω : (logPolesForms f I (p + 1)).val.obj (op W))
      (η : Γ(relativeDifferentialForms f (q : ℤ), W)),
      logRes hI hlog (logFormsCast (Nat.add_right_comm p 1 q)
          (logFormsWedge hI hlog ω ((logPolesFormsInclusion f I q).val.app (op W) η))) =
        formWedge (I.subschemeι ≫ f) p q (I.subschemeι ⁻¹ᵁ W) (logRes hI hlog ω)
          (formRes I.subschemeι (q : ℤ) W η)) ∧
    (∀ (q : ℕ) (W : X.Opens) (ω : (logPolesForms f I 0).val.obj (op W))
      (η : Γ(relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), W)),
      logRes hI hlog (logFormsCast (Nat.zero_add (q + 1))
          (logFormsWedge hI hlog ω ((logPolesFormsInclusion f I (q + 1)).val.app (op W) η))) = 0) :=
  ⟨fun _ _ _ ω η => logRes_logFormsWedge_logPolesFormsInclusion hI hlog ω η,
    fun _ _ ω η => logRes_logFormsWedge_logPolesFormsInclusion_zero hI hlog ω η⟩

end AlgebraicGeometry.Scheme.Hom
