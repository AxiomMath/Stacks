module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.FiniteType
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.LocalEquation
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceHomEquivId
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ZeroSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.Representability
public import StacksFrontier.AlgebraicGeometry.SectionIdeal.Basic

/-!
# The local form of the fibre coordinate of a line bundle

Let `M` be an invertible module on a scheme `Y` and let `q : L(M) ⟶ Y` be the line bundle of
[Stacks, Tag 01M2], the relative spectrum of `Sym(M^{⊗ -1})`. Over an affine open `V = Spec B` of
`Y` trivializing `M^{⊗ -1}` by a basis `w` of `Γ(M^{⊗ -1}, V)` one has
`Γ(Sym(M^{⊗ -1}), V) = B[z]` with `w ↦ z`, hence `q^{-1}V = Spec B[z]`, and **the fibre coordinate
`Stacks.LineBundle.fibreCoordinate` — a global section of `q^* M` — is `z` times a basis of
`Γ(q^* M, q^{-1}V)`.** That identification is what this file proves, as
`Stacks.LineBundle.exists_fibreCoordinateChart`.

It is the comparison the local presentation in [Stacks, Tag 0F97] rests on: the fibre
coordinate matched with the polynomial generator `MvPolynomial.X 0` under the trivialization
`Stacks.SymAlgSections.ungradedSymSectionsMvPolynomialEquiv`.

## Main definitions

* `Stacks.LineBundle.Situation.chartRingEquiv`: the chart `Γ(Sym(L), V) ≃+* Γ(Tot(L), p^{-1}V)`
  over an affine open `V` of the base, which is the universal algebra map of the relative
  spectrum read on sections.
* `Stacks.LineBundle.Situation.chartEquiv`: **`Γ(Tot(L), p^{-1}V)` is a polynomial ring in `r`
  variables over `Γ(X, V)`** for an affine open `V` carrying a basis of `Γ(L, V)` indexed by
  `Fin r`.
* `Stacks.LineBundle.Situation.zeroSectionChartMap`: the comorphism
  `Γ(Tot(L), p^{-1}V) ⟶ Γ(X, V)` of the zero section, read on the chart.

## Main results

* `Stacks.LineBundle.exists_fibreCoordinateChart`: **the local form of the fibre coordinate.**
  Every point of `Y` has an affine open neighbourhood `V` carrying a ring isomorphism
  `ψ : Γ(L(M), q^{-1}V) ≃+* Γ(Y, V)[z]` taking the comorphism of `q` to the inclusion of
  constants, such that the zero scheme of the fibre coordinate is cut out on that chart by `z`,
  and such that some trivialization of `Γ(q^* M, q^{-1}V)` takes the fibre coordinate to `z`.
* `Stacks.LineBundle.Situation.chartEquiv_app` and
  `Stacks.LineBundle.Situation.chartEquiv_genToPushforward`: the polynomial chart takes the
  comorphism of the structure morphism to `MvPolynomial.C` and the degree-one section attached
  to the `i`-th basis vector to `MvPolynomial.X i`.
* `Stacks.LineBundle.Situation.ker_zeroSectionChartMap`: **the image of the zero section is cut
  out on the chart by the variable.**
* `Stacks.SymAlgSections.ungradedSymSectionsRingEquiv_ι` and
  `Stacks.SymAlgSections.ungradedSymSectionsMvPolynomialEquiv_incl_gen`: the identification of
  the sections of `Sym(ℰ)` over an affine open **in degree one** — it carries
  `SymmetricAlgebra.ι` to the degree-one generator of the algebra sheaf, hence a basis vector to
  a variable. The degree-zero statement is the existing
  `Stacks.SymAlgSections.ungradedSymSectionsRingEquiv_algebraMap`.
* `Stacks.Modules.nonempty_linearEquiv_sections_pullback`: free rank-one sections over an affine
  open whose preimage is affine pull back to free rank-one sections.

## The route, and why no dualization isomorphism appears

The fibre coordinate is `Stacks.LineBundle.Situation.tautologicalSection` carried across the two
dualization isomorphisms `Stacks.ProjBundleInverseBaseChange.pullbackTensorPowerNegOneIso` and
`Stacks.PullbackTensorIso.tensorPowerNegOneNegOneIso`, which one might expect to have to
compute on sections. **They do not.** The argument here never
touches either, because it goes through the *zero scheme* and then back:

1. `Stacks.LineBundle.zeroScheme_fibreCoordinate` discharges both dualization isomorphisms at
   once — a zero scheme is insensitive to an isomorphism of the ambient module — leaving the zero
   scheme of the tautological section, and
   `Stacks.LineBundle.Situation.zeroScheme_tautologicalSectionBase_eq_ker_zeroSection`, which is
   clause (1) of [Stacks, Tag 0F96], identifies that with the kernel ideal sheaf of the zero
   section.
2. On the chart the zero section's comorphism is the constant coefficient: it fixes the constants
   because `o ≫ p = 𝟙`, and it kills the variable because the module component of the zero
   section under the functor of points vanishes
   (`Stacks.LineBundle.Situation.factorsThrough_zeroSection_iff` together with
   `Stacks.LineBundle.Situation.totalSpaceHomEquiv_snd`); a ring map out of a polynomial ring is
   determined by those two, which is `MvPolynomial.ringHom_ext`. So the ideal is `(z)`.
3. The step back is the local equation of a zero scheme: under *any* trivialization `e` of
   `Γ(q^* M, q^{-1}V)` the ideal is generated by `e(fibreCoordinate)`
   (`Stacks.Divisors.zeroScheme_ideal_of_trivialization`), so `e(fibreCoordinate)` and `z`
   generate the same ideal; `z` is not a zero divisor in a polynomial ring, so they differ by a
   unit, and rescaling `e` by that unit gives a trivialization carrying the fibre coordinate to
   `z` exactly. **This recovers the section itself, not merely its zero scheme** — it is the
   reverse implication of the local-equation lemma, and it is what makes the detour through the
   zero scheme lossless.

The one trivialization that has to exist for step 3 is supplied by
`Stacks.Modules.nonempty_linearEquiv_sections_pullback`: `q^{-1}V` is affine because `q` is an
affine morphism, so the affine base-change description of the sections of a pullback
(`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`) presents `Γ(q^* M, q^{-1}V)` as
`Γ(Y, V) ⊗ Γ(M, V)` over `Γ(Y, V)`, and a basis base-changes to a basis.

## Implementation notes

**The chart is the universal algebra map, not a glueing comparison.**
`Stacks.RelativeSpec.universalAlgebraMap` is an isomorphism on sections over an affine open
(`Stacks.RelativeSpec.isIso_universalAlgebraMap_app`) and `Stacks.RelativeSpec.toBase_app`
factors the comorphism of the structure morphism through it, so both halves of the chart come
from one map and no `Stacks.RelativeSpec.GluedSpectrum.chartIsoPreimage` transport is needed. Its
compatibility with the degree-one inclusion `L ⟶ p_* 𝒪` is
`Stacks.LineBundle.Situation.underlyingModuleIsoPushforward_hom_val_app`, because
`universalAlgebraMap` is by definition the inverse of Tag 01LX(3).

**`Stacks.LineBundle.Situation.exists_chartEquiv` exists to keep a basis away from a concrete
situation.** The type of a `Module.Basis (Fin 1) Γ(D.X, V) Γ(D.L, V)` mentions the sections of
the line bundle as a module over the sections of the structure sheaf, and at
`D = inverseSituation Y M` instance search does not find that module structure:
`(inverseSituation Y M).L` reduces to the tensor power at the
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` spelling, which is the spelling issue
the implementation notes of `StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Basic`
record. Bundling the three conclusions into an existential proved for a situation *variable*
means the basis is built where the instance is available, and the caller only ever supplies a
`≃ₗ`.

**The transports along `o^{-1}p^{-1}V = V` are written with `eqToHom` and discharged by
`congrArg`.** `rw` builds its motive at a transparency at which the subtype of affine opens and
the restriction along an equality of opens are not interchangeable — the same obstruction
`StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeBaseChange.PullbackSections` documents — so the
identity of the zero scheme's ideal with the kernel of the chart comorphism is assembled from
`Eq.trans` and `congrArg`, whose types are checked at default transparency.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite PresheafOfModules
open Stacks.RelativeSpec (universalAlgebraMap)

universe u

/-! ### The degree-one part of the sections of a symmetric algebra -/

namespace Stacks.SymAlgSections

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] {V : X.Opens}
  (hV : IsAffineOpen V)

/-- The image of a section of `ℰ` in the degree-one symmetric power of the sections. -/
def symGen (x : Γ(E, V)) : SymPow.symmetricPower 1 Γ(X, V) Γ(E, V) :=
  ⟨SymmetricAlgebra.ι Γ(X, V) Γ(E, V) x, SymPow.ι_mem_symmetricPowerInt_one _ _ x⟩

omit [E.IsQuasicoherent] in
/-- The inverse of the sheafification isomorphism is the sheafification unit. -/
theorem sheafificationIso_inv_apply (x : Γ(E, V)) :
    (Scheme.Modules.sheafificationIso X E).inv.val.app (op V) x =
      Hom.app (sheafifyUnit (𝟙 X.ringCatSheaf.obj) E.val) (op V) x :=
  PresheafOfModules.sheafifyCounitIso_inv_apply (𝟙 X.ringCatSheaf.obj) E (op V) x

/-- **The degree-one sheafification unit is the degree-one generator of `Sym(ℰ)`.** -/
theorem pieceUnit_one_symGen (x : Γ(E, V)) :
    pieceUnit E hV 1 (symGen E x) =
      (Scheme.Modules.symmetricAlgebraGen X E).val.app (op V) x :=
  Eq.trans ((symPowIntGradedAlgebra E.val).sheafifyGen_unit
      (𝟙 X.ringCatSheaf.obj) (symPowIntGen E.val) (op V) x).symm
    (congrArg (fun t => ((symPowIntGradedAlgebra E.val).sheafifyGen
        (𝟙 X.ringCatSheaf.obj) (symPowIntGen E.val)).val.app (op V) t)
      (sheafificationIso_inv_apply E x).symm)

omit [E.IsQuasicoherent] in
/-- The graded decomposition of `ι x` is concentrated in degree one. -/
theorem decompose_ι (x : Γ(E, V)) :
    DirectSum.decompose (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V))
        (SymmetricAlgebra.ι Γ(X, V) Γ(E, V) x) =
      DirectSum.of (fun m : ℕ => (SymPow.symmetricPower m Γ(X, V) Γ(E, V) : Type u)) 1
        (symGen E x) :=
  DirectSum.decompose_of_mem (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V))
    (symGen E x).2

/-- **The identification of the sections of `Sym(ℰ)` over an affine open carries
`SymmetricAlgebra.ι` to the degree-one generator of the algebra sheaf.** -/
theorem ungradedSymSectionsRingEquiv_ι (x : Γ(E, V)) :
    ungradedSymSectionsRingEquiv E hV (SymmetricAlgebra.ι Γ(X, V) Γ(E, V) x) =
      Stacks.RelativeSpec.ungradedAlgebraSheafIncl X (Scheme.Modules.symmetricAlgebra X E)
        (Scheme.Modules.symmetricAlgebra_mul_comm X E) 1 V
        ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op V) x) := by
  have h : symPowersRingEquiv E hV (DirectSum.decomposeRingEquiv
        (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V))
        (SymmetricAlgebra.ι Γ(X, V) Γ(E, V) x)) =
      (symPresheafAlgebra E).incl 1
        ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op V) x) := by
    refine Eq.trans (congrArg (symPowersRingEquiv E hV) (decompose_ι E x)) ?_
    refine Eq.trans (ofSymPowers_of E hV 1 (symGen E x)) ?_
    exact congrArg (DirectSum.of (fun m : ℤ => ((symPiece E m).obj (op V) : Type u)) 1)
      (pieceUnit_one_symGen E hV x)
  exact congrArg
    (Stacks.RelativeSpec.ungradedCommUnit X (Scheme.Modules.symmetricAlgebra X E)
      (Scheme.Modules.symmetricAlgebra_mul_comm X E) V).hom h

/-- **The polynomial presentation carries the degree-one generator of a basis vector to the
corresponding variable.** -/
theorem ungradedSymSectionsMvPolynomialEquiv_incl_gen {r : ℕ}
    (b : Module.Basis (Fin r) Γ(X, V) Γ(E, V)) (i : Fin r) :
    ungradedSymSectionsMvPolynomialEquiv E hV b
        (Stacks.RelativeSpec.ungradedAlgebraSheafIncl X (Scheme.Modules.symmetricAlgebra X E)
          (Scheme.Modules.symmetricAlgebra_mul_comm X E) 1 V
          ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op V) (b i))) =
      MvPolynomial.X i := by
  rw [← ungradedSymSectionsRingEquiv_ι E hV (b i)]
  show (SymmetricAlgebra.equivMvPolynomial b)
      ((ungradedSymSectionsRingEquiv E hV).symm
        (ungradedSymSectionsRingEquiv E hV
          (SymmetricAlgebra.ι Γ(X, V) Γ(E, V) (b i)))) = _
  rw [RingEquiv.symm_apply_apply, SymmetricAlgebra.equivMvPolynomial_ι_apply]

end Stacks.SymAlgSections

/-! ### Free rank-one sections pull back -/

namespace Stacks.Modules

/-- **Free rank-one sections pull back.** If `M` is a quasi-coherent module on `Y` whose sections
over an affine open `V` are a free `Γ(Y, V)`-module of rank one, and the preimage `f ⁻¹ᵁ V` is an
affine open of `X`, then the sections of the pullback `f^* M` over `f ⁻¹ᵁ V` are a free
`Γ(X, f ⁻¹ᵁ V)`-module of rank one.

The proof is the affine base-change description of the sections of a pullback,
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`, which for a compatible pair of affine
opens identifies `Γ(f^* M, f ⁻¹ᵁ V)` with `Γ(X, f ⁻¹ᵁ V) ⊗_{Γ(Y, V)} Γ(M, V)`; a basis of
`Γ(M, V)` base-changes to a basis of the tensor product. -/
theorem nonempty_linearEquiv_sections_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsQuasicoherent] {V : Y.Opens} (hV : IsAffineOpen V)
    (hW : IsAffineOpen (f ⁻¹ᵁ V)) (he : Nonempty (Γ(M, V) ≃ₗ[Γ(Y, V)] Γ(Y, V))) :
    Nonempty (Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ V)
      ≃ₗ[Γ(X, f ⁻¹ᵁ V)] Γ(X, f ⁻¹ᵁ V)) := by
  obtain ⟨b⟩ := (Stacks.SheafOfModules.Invertible.nonempty_basis_iff_nonempty_linearEquiv
    Γ(Y, V) Γ(M, V)).mpr he
  let : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.toAlgebra
  have e : TensorProduct Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(M, V) ≃ₗ[Γ(X, f ⁻¹ᵁ V)]
      Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ V) :=
    (affinePullbackSectionsBaseChangeIso f M hV hW le_rfl).toLinearEquiv
  exact (Stacks.SheafOfModules.Invertible.nonempty_basis_iff_nonempty_linearEquiv
    Γ(X, f ⁻¹ᵁ V) Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ V)).mp
      ⟨(b.baseChange Γ(X, f ⁻¹ᵁ V)).map e⟩

end Stacks.Modules

/-! ### The variable in a polynomial ring in one variable -/

namespace Stacks.LineBundle

/-- The kernel of the constant coefficient of a polynomial ring in one variable is generated by
the variable. -/
theorem ker_constantCoeff_fin_one (B : Type u) [CommRing B] :
    RingHom.ker (MvPolynomial.constantCoeff (σ := Fin 1) (R := B)) =
      Ideal.span {MvPolynomial.X 0} := by
  refine le_antisymm (fun p hp => ?_) (Ideal.span_le.mpr ?_)
  · have key : ∀ q : MvPolynomial (Fin 1) B,
        q - MvPolynomial.C (MvPolynomial.constantCoeff q) ∈
          Ideal.span ({MvPolynomial.X 0} : Set (MvPolynomial (Fin 1) B)) := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq =>
          have h : p + q - MvPolynomial.C (MvPolynomial.constantCoeff (p + q)) =
              (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) +
                (q - MvPolynomial.C (MvPolynomial.constantCoeff q)) := by
            rw [map_add, map_add]; ring
          rw [h]
          exact Ideal.add_mem _ hp hq
      | mul_X p i hp =>
          have h0 : MvPolynomial.constantCoeff (p * MvPolynomial.X i) = 0 := by simp
          rw [h0, map_zero, sub_zero]
          refine Ideal.mul_mem_left _ _ ?_
          have hi : i = 0 := Subsingleton.elim _ _
          rw [hi]
          exact Ideal.subset_span rfl
    have hc : MvPolynomial.constantCoeff p = 0 := hp
    have h := key p
    rwa [hc, map_zero, sub_zero] at h
  · intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    simp [RingHom.mem_ker]

/-- The variable of a polynomial ring in one variable is not a zero divisor. -/
theorem eq_zero_of_X_mul_eq_zero (B : Type u) [CommRing B] (p : MvPolynomial (Fin 1) B)
    (h : MvPolynomial.X 0 * p = 0) : p = 0 := by
  refine MvPolynomial.ext _ _ fun m => ?_
  have hc := congrArg (fun q : MvPolynomial (Fin 1) B => q.coeff (Finsupp.single 0 1 + m)) h
  simp only [MvPolynomial.coeff_X_mul, AddMonoidAlgebra.coeff_zero, Pi.zero_apply] at hc
  exact hc

/-- Two elements of a commutative ring generating the same principal ideal differ by a unit,
provided one of them is not a zero divisor. -/
theorem exists_unit_of_span_eq {R : Type u} [CommRing R] (a z : R)
    (hz : ∀ t : R, z * t = 0 → t = 0)
    (h : Ideal.span ({a} : Set R) = Ideal.span ({z} : Set R)) :
    ∃ c : Rˣ, a = (c : R) * z := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
    (h ▸ Ideal.subset_span (Set.mem_singleton a) : a ∈ Ideal.span ({z} : Set R))
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp
    (h ▸ Ideal.subset_span (Set.mem_singleton z) : z ∈ Ideal.span ({a} : Set R))
  have hdc : d * c = 1 := by
    have h1 : z * (d * c - 1) = 0 := by
      have h2 : d * c * z = z := by rw [mul_assoc, hc, hd]
      linear_combination h2
    have h3 := hz _ h1
    linear_combination h3
  exact ⟨⟨c, d, by rw [mul_comm]; exact hdc, hdc⟩, hc.symm⟩

/-! ### The chart of a total space over a trivializing affine open -/

section Chart

variable (D : Situation.{u}) (V : D.X.affineOpens)

/-- **The structure morphism of a total space is an affine morphism**: the total space is a
relative spectrum. -/
instance Situation.isAffineHom_totalSpaceToBase : IsAffineHom D.totalSpaceToBase :=
  inferInstanceAs (IsAffineHom
    (Stacks.RelativeSpec.gluedSpectrum D.relativeSpecSituation).toBase)

/-- **The preimage of an affine open under the structure morphism of a total space is affine.** -/
theorem Situation.isAffineOpen_preimage_totalSpaceToBase :
    IsAffineOpen (D.totalSpaceToBase ⁻¹ᵁ (V.1 : D.X.Opens)) :=
  V.2.preimage D.totalSpaceToBase

/-- **The chart of the total space over an affine open `V` of the base**: the universal algebra
map of the relative spectrum identifies the sections of `Sym(L)` over `V` with the sections of
the structure sheaf of the total space over `p^{-1}V`. -/
def Situation.chartRingEquiv :
    Stacks.RelativeSpec.AlgebraSheaf.sections D.algebraSheaf V.1 ≃+*
      Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ (V.1 : D.X.Opens)) :=
  haveI := Stacks.RelativeSpec.isIso_universalAlgebraMap_app D.relativeSpecSituation V
  (asIso ((universalAlgebraMap D.relativeSpecSituation).right.app
    (op (V.1 : D.X.Opens)))).commRingCatIsoToRingEquiv

/-- The chart is the universal algebra map on sections. -/
theorem Situation.chartRingEquiv_apply
    (x : Stacks.RelativeSpec.AlgebraSheaf.sections D.algebraSheaf V.1) :
    D.chartRingEquiv V x =
      ((universalAlgebraMap D.relativeSpecSituation).right.app
        (op (V.1 : D.X.Opens))).hom x :=
  rfl

/-- **The chart carries the structure map of `Sym(L)` to the comorphism of the structure
morphism of the total space.** -/
theorem Situation.chartRingEquiv_structureMap (b : Γ(D.X, (V.1 : D.X.Opens))) :
    D.chartRingEquiv V ((D.algebraSheaf.hom.hom.app (op (V.1 : D.X.Opens))).hom b) =
      (D.totalSpaceToBase.app (V.1 : D.X.Opens)).hom b :=
  (congrArg
    (fun φ : Γ(D.X, (V.1 : D.X.Opens)) ⟶
        Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ (V.1 : D.X.Opens)) => φ.hom b)
    (Stacks.RelativeSpec.toBase_app D.relativeSpecSituation (V.1 : D.X.Opens))).symm

/-- **The chart carries the degree-one section attached to a local section of `L` to the value
of the degree-one inclusion `L ⟶ p_* 𝒪` on it.** -/
theorem Situation.chartRingEquiv_algebraSheafIncl (x : Γ(D.L, (V.1 : D.X.Opens))) :
    D.chartRingEquiv V (D.algebraSheafIncl 1 (V.1 : D.X.Opens)
        (Hom.app D.symmetricAlgebraGen.val (op (V.1 : D.X.Opens)) x)) =
      Hom.app D.genToPushforward.val (op (V.1 : D.X.Opens)) x :=
  ((congrArg (fun z => (D.underlyingModuleIsoPushforward.hom.val.app
          (op (V.1 : D.X.Opens))).hom z)
        (D.algebraSheafGen_val_app (V.1 : D.X.Opens) x)).trans
      (D.underlyingModuleIsoPushforward_hom_val_app (V.1 : D.X.Opens)
        (D.algebraSheafIncl 1 (V.1 : D.X.Opens)
          (Hom.app D.symmetricAlgebraGen.val (op (V.1 : D.X.Opens)) x)))).symm

variable {r : ℕ}
  (b : Module.Basis (Fin r) Γ(D.X, (V.1 : D.X.Opens)) Γ(D.L, (V.1 : D.X.Opens)))

/-- **The polynomial chart of the total space**: over an affine open `V` of the base on which
`Γ(L, V)` is free with a basis indexed by `Fin r`, the sections of the structure sheaf of the
total space over `p^{-1}V` form a polynomial ring in `r` variables over `Γ(X, V)`. -/
def Situation.chartEquiv :
    Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ (V.1 : D.X.Opens)) ≃+*
      MvPolynomial (Fin r) Γ(D.X, (V.1 : D.X.Opens)) :=
  (D.chartRingEquiv V).symm.trans
    (Stacks.SymAlgSections.ungradedSymSectionsMvPolynomialEquiv D.L V.2 b)

/-- **The polynomial chart carries the comorphism of the structure morphism to the constants.**
So it is an isomorphism of `Γ(X, V)`-algebras. -/
theorem Situation.chartEquiv_app (s : Γ(D.X, (V.1 : D.X.Opens))) :
    D.chartEquiv V b ((D.totalSpaceToBase.app (V.1 : D.X.Opens)).hom s) = MvPolynomial.C s := by
  refine Eq.trans (congrArg (Stacks.SymAlgSections.ungradedSymSectionsMvPolynomialEquiv
      D.L V.2 b) ?_) (Stacks.SymAlgSections.ungradedSymSectionsMvPolynomialEquiv_app
        D.L V.2 b s)
  exact (D.chartRingEquiv V).symm_apply_eq.mpr (D.chartRingEquiv_structureMap V s).symm

/-- **The polynomial chart carries the value of the degree-one inclusion on the `i`-th basis
vector to the `i`-th variable.** This is the fibre coordinate in the chart, before it is read as
a section of `p^* L` rather than of the structure sheaf. -/
theorem Situation.chartEquiv_genToPushforward (i : Fin r) :
    D.chartEquiv V b (Hom.app D.genToPushforward.val (op (V.1 : D.X.Opens)) (b i)) =
      MvPolynomial.X i := by
  refine Eq.trans (congrArg (Stacks.SymAlgSections.ungradedSymSectionsMvPolynomialEquiv
      D.L V.2 b) ?_)
    (Stacks.SymAlgSections.ungradedSymSectionsMvPolynomialEquiv_incl_gen D.L V.2 b i)
  exact (D.chartRingEquiv V).symm_apply_eq.mpr (D.chartRingEquiv_algebraSheafIncl V (b i)).symm

end Chart

/-! ### The zero section in the chart -/

section ZeroSection

variable (D : Situation.{u}) (V : D.X.affineOpens)

/-- The zero section pulls the chart back to the affine open it sits over: `o^{-1}p^{-1}V = V`,
because `o` is a section of `p`. -/
theorem Situation.zeroSection_preimage :
    D.zeroSection ⁻¹ᵁ (D.totalSpaceToBase ⁻¹ᵁ (V.1 : D.X.Opens)) = (V.1 : D.X.Opens) := by
  rw [← Scheme.Hom.comp_preimage, D.zeroSection_comp_totalSpaceToBase, Scheme.Hom.id_preimage]

/-- **The comorphism of the zero section, read on the chart**: the ring map
`Γ(Tot(L), p^{-1}V) ⟶ Γ(X, V)` cutting out the image of the zero section. -/
def Situation.zeroSectionChartMap :
    Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ (V.1 : D.X.Opens)) ⟶ Γ(D.X, (V.1 : D.X.Opens)) :=
  D.zeroSection.app (D.totalSpaceToBase ⁻¹ᵁ (V.1 : D.X.Opens)) ≫
    D.X.presheaf.map (eqToHom (D.zeroSection_preimage V).symm).op

/-- **The comorphism of the zero section is a retraction of the comorphism of the structure
morphism**, because `o ≫ p = 𝟙`. -/
theorem Situation.app_comp_zeroSectionChartMap :
    D.totalSpaceToBase.app (V.1 : D.X.Opens) ≫ D.zeroSectionChartMap V =
      𝟙 Γ(D.X, (V.1 : D.X.Opens)) := by
  have h1 : (𝟙 Γ(D.X, (V.1 : D.X.Opens)) ≫
        D.X.presheaf.map (eqToHom (D.zeroSection_preimage V)).op) ≫
      D.X.presheaf.map (eqToHom (D.zeroSection_preimage V).symm).op =
      𝟙 Γ(D.X, (V.1 : D.X.Opens)) := by
    rw [Category.id_comp, ← Functor.map_comp]
    simp
  rw [Situation.zeroSectionChartMap, ← Category.assoc, ← Scheme.Hom.comp_app,
    Scheme.Hom.congr_app D.zeroSection_comp_totalSpaceToBase (V.1 : D.X.Opens)]
  exact h1

/-- **The comorphism of the zero section kills the degree-one part**: the augmentation of the
symmetric algebra vanishes in positive degrees, so the module component of the zero section
under the functor of points is zero. -/
theorem Situation.zeroSectionChartMap_genToPushforward (x : Γ(D.L, (V.1 : D.X.Opens))) :
    (D.zeroSectionChartMap V).hom
        (Hom.app D.genToPushforward.val (op (V.1 : D.X.Opens)) x) = 0 := by
  have h0 : (D.totalSpaceHomEquiv D.X D.zeroSection).2 = 0 :=
    (D.factorsThrough_zeroSection_iff D.zeroSection).mp ⟨𝟙 D.X, Category.id_comp _⟩
  have h2 : D.genToPushforward ≫ Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap
      (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMapAux D.totalSpaceToBase
        D.zeroSection) = 0 :=
    (D.totalSpaceHomEquiv_snd D.zeroSection).symm.trans h0
  have h3 : (D.zeroSection.app (D.totalSpaceToBase ⁻¹ᵁ (V.1 : D.X.Opens))).hom
      (Hom.app D.genToPushforward.val (op (V.1 : D.X.Opens)) x) = 0 :=
    congrArg
      (fun φ : D.L ⟶ (Scheme.Modules.pushforward
          (D.zeroSection ≫ D.totalSpaceToBase)).obj (SheafOfModules.unit D.X.ringCatSheaf) =>
        Hom.app φ.val (op (V.1 : D.X.Opens)) x) h2
  show (D.X.presheaf.map (eqToHom (D.zeroSection_preimage V).symm).op).hom
    ((D.zeroSection.app (D.totalSpaceToBase ⁻¹ᵁ (V.1 : D.X.Opens))).hom _) = 0
  rw [h3, map_zero]

/-- The comorphism of the zero section on the chart has the same kernel as the comorphism at the
chart's open: the two differ by the restriction along an equality of opens, which is an
isomorphism. -/
theorem Situation.ker_zeroSectionChartMap_eq :
    RingHom.ker (D.zeroSectionChartMap V).hom =
      RingHom.ker (D.zeroSection.app (D.totalSpaceToBase ⁻¹ᵁ (V.1 : D.X.Opens))).hom := by
  exact RingHom.ker_comp_of_injective _
    (ConcreteCategory.bijective_of_isIso
      (D.X.presheaf.map (eqToHom (D.zeroSection_preimage V).symm).op)).1

variable (b : Module.Basis (Fin 1) Γ(D.X, (V.1 : D.X.Opens)) Γ(D.L, (V.1 : D.X.Opens)))

/-- **The comorphism of the zero section is the constant coefficient in the polynomial chart.**
It kills the variable, by the vanishing of the augmentation in positive degrees, and fixes the
constants, because it is a retraction of the structure morphism; a ring map out of a polynomial
ring is determined by those two. -/
theorem Situation.zeroSectionChartMap_chartEquiv_symm
    (p : MvPolynomial (Fin 1) Γ(D.X, (V.1 : D.X.Opens))) :
    (D.zeroSectionChartMap V).hom ((D.chartEquiv V b).symm p) =
      MvPolynomial.constantCoeff p := by
  have key : RingHom.comp (D.zeroSectionChartMap V).hom
      (D.chartEquiv V b).symm.toRingHom = MvPolynomial.constantCoeff := by
    refine MvPolynomial.ringHom_ext (fun s => ?_) (fun i => ?_)
    · have h : (D.chartEquiv V b).symm (MvPolynomial.C s) =
          (D.totalSpaceToBase.app (V.1 : D.X.Opens)).hom s :=
        (D.chartEquiv V b).symm_apply_eq.mpr (D.chartEquiv_app V b s).symm
      show (D.zeroSectionChartMap V).hom ((D.chartEquiv V b).symm (MvPolynomial.C s)) = _
      rw [h, MvPolynomial.constantCoeff_C]
      exact congrArg (fun φ : Γ(D.X, (V.1 : D.X.Opens)) ⟶ Γ(D.X, (V.1 : D.X.Opens)) => φ.hom s)
        (D.app_comp_zeroSectionChartMap V)
    · have h : (D.chartEquiv V b).symm (MvPolynomial.X i) =
          Hom.app D.genToPushforward.val (op (V.1 : D.X.Opens)) (b i) :=
        (D.chartEquiv V b).symm_apply_eq.mpr (D.chartEquiv_genToPushforward V b i).symm
      show (D.zeroSectionChartMap V).hom ((D.chartEquiv V b).symm (MvPolynomial.X i)) = _
      rw [h, MvPolynomial.constantCoeff_X]
      exact D.zeroSectionChartMap_genToPushforward V (b i)
  exact congrArg (fun φ : MvPolynomial (Fin 1) Γ(D.X, (V.1 : D.X.Opens)) →+*
    Γ(D.X, (V.1 : D.X.Opens)) => φ p) key

/-- **The variable of the chart is not a zero divisor.** -/
theorem Situation.eq_zero_of_chartEquiv_symm_X_mul_eq_zero
    (t : Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ (V.1 : D.X.Opens)))
    (h : (D.chartEquiv V b).symm (MvPolynomial.X 0) * t = 0) : t = 0 := by
  have h1 : MvPolynomial.X (0 : Fin 1) * D.chartEquiv V b t = 0 := by
    have h2 := congrArg (D.chartEquiv V b) h
    rw [map_mul, map_zero, RingEquiv.apply_symm_apply] at h2
    exact h2
  have h3 := eq_zero_of_X_mul_eq_zero _ _ h1
  have h4 := congrArg (D.chartEquiv V b).symm h3
  rwa [RingEquiv.symm_apply_apply, map_zero] at h4

/-- **The kernel of the comorphism of the zero section is generated by the variable of the
chart.** -/
theorem Situation.ker_zeroSectionChartMap :
    RingHom.ker (D.zeroSectionChartMap V).hom =
      Ideal.span {(D.chartEquiv V b).symm (MvPolynomial.X 0)} := by
  have hker : ∀ x, (D.zeroSectionChartMap V).hom x =
      MvPolynomial.constantCoeff (D.chartEquiv V b x) := fun x => by
    rw [← D.zeroSectionChartMap_chartEquiv_symm V b (D.chartEquiv V b x),
      RingEquiv.symm_apply_apply]
  rw [show (D.zeroSectionChartMap V).hom =
      MvPolynomial.constantCoeff.comp (D.chartEquiv V b : _ →+* MvPolynomial (Fin 1) _) from
        RingHom.ext fun x => hker x,
    ← RingHom.comap_ker, ker_constantCoeff_fin_one]
  refine (Ideal.map_symm (D.chartEquiv V b)).symm.trans ?_
  rw [Ideal.map_span, Set.image_singleton]

end ZeroSection

/-! ### The chart from a trivialization of the line bundle -/

/-- **The chart of the total space over a trivializing affine open, from a trivialization of the
sections rather than from a basis.** Over an affine open `V` of the base on which the sections of
`L` are free of rank one, the sections of the structure sheaf of the total space over `p^{-1}V`
form a polynomial ring in one variable over `Γ(X, V)`, the comorphism of `p` is the inclusion of
constants, the comorphism of the zero section has the variable as the generator of its kernel,
and the variable is not a zero divisor.

This is the form the construction is consumed in: a trivialization is what
`AlgebraicGeometry.exists_affineOpens_linearEquiv_le` produces, and bundling the three
conclusions here keeps the basis — whose type mentions the sections of `L` as a module over the
sections of the structure sheaf, a spelling instance search does not reach at a *concrete*
situation — inside a statement proved for a situation variable. -/
theorem Situation.exists_chartEquiv (D : Situation.{u}) (V : D.X.affineOpens)
    (e : Γ(D.L, (V.1 : D.X.Opens)) ≃ₗ[Γ(D.X, (V.1 : D.X.Opens))]
      Γ(D.X, (V.1 : D.X.Opens))) :
    ∃ ψ : Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ (V.1 : D.X.Opens)) ≃+*
        MvPolynomial (Fin 1) Γ(D.X, (V.1 : D.X.Opens)),
      (∀ s : Γ(D.X, (V.1 : D.X.Opens)),
          ψ ((D.totalSpaceToBase.app (V.1 : D.X.Opens)).hom s) = MvPolynomial.C s) ∧
      RingHom.ker (D.zeroSectionChartMap V).hom =
        Ideal.span {ψ.symm (MvPolynomial.X 0)} ∧
      ∀ t : Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ (V.1 : D.X.Opens)),
        ψ.symm (MvPolynomial.X 0) * t = 0 → t = 0 :=
  ⟨D.chartEquiv V (Module.Basis.ofEquivFun
      (e.trans (LinearEquiv.funUnique (Fin 1) _ _).symm)),
    D.chartEquiv_app V _, D.ker_zeroSectionChartMap V _,
    D.eq_zero_of_chartEquiv_symm_X_mul_eq_zero V _⟩

/-! ### The fibre coordinate in the chart -/

section FibreCoordinate

variable (Y : Scheme.{u}) (M : Y.Modules)
  [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]

include hM in
/-- **The preimage of an affine open under the structure morphism of the line bundle of an
invertible module is affine.** -/
theorem isAffineOpen_preimage_lineBundleProj (V : Y.affineOpens) :
    IsAffineOpen (lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)) :=
  (inverseSituation Y M).isAffineOpen_preimage_totalSpaceToBase V

include hM in
/-- **The local form of the fibre coordinate of a line bundle.** Every point `y` of `Y` has an
affine open neighbourhood `V` carrying

* a ring isomorphism `ψ : Γ(L(M), q^{-1}V) ≃+* Γ(Y, V)[z]` taking the comorphism of `q` to the
  inclusion of constants, so that `q^{-1}V` is the affine line over `V`; and
* a trivialization `e` of the sections of `q^* M` over `q^{-1}V` taking the fibre coordinate to
  the variable `z`,

and on that chart the zero scheme of the fibre coordinate is cut out by `z`.

This is what an equation in the fibre coordinates is read by: the third clause exhibits
`Z(fibreCoordinate)` as the principal closed subscheme `(z)` of `Spec Γ(Y, V)[z]`, and the
second says the fibre coordinate itself — not merely its zero scheme — is the variable. -/
theorem exists_fibreCoordinateChart (y : Y) :
    ∃ V : Y.affineOpens, y ∈ V.1 ∧
      ∃ ψ : Γ(lineBundleSpace Y M, lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)) ≃+*
          MvPolynomial (Fin 1) Γ(Y, (V.1 : Y.Opens)),
        (∀ s : Γ(Y, (V.1 : Y.Opens)),
            ψ (((lineBundleProj Y M).app (V.1 : Y.Opens)).hom s) = MvPolynomial.C s) ∧
        (AlgebraicGeometry.zeroScheme (lineBundleSpace Y M) (lineBundlePullback Y M)
              (fibreCoordinate Y M)).ideal
            ⟨lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens),
              isAffineOpen_preimage_lineBundleProj Y M V⟩ =
          Ideal.span {ψ.symm (MvPolynomial.X 0)} ∧
        ∃ e : Γ(lineBundlePullback Y M, lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)) ≃ₗ[
              Γ(lineBundleSpace Y M, lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens))]
            Γ(lineBundleSpace Y M, lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)),
          e ((lineBundlePullback Y M).presheaf.map (homOfLE le_top).op (fibreCoordinate Y M)) =
            ψ.symm (MvPolynomial.X 0) := by
  have hqc : M.IsQuasicoherent := Stacks.Divisors.isQuasicoherent_of_isInvertible M
  obtain ⟨W, hyW, hWtriv⟩ := Stacks.Tag0C6KZeroSchemeAnnihilation.exists_local_section_linearEquiv
    (inverseSituation Y M).X (inverseSituation Y M).L y
  obtain ⟨V, hyV, hVW, heM⟩ := AlgebraicGeometry.exists_affineOpens_linearEquiv_le Y M y W hyW
  obtain ⟨eN⟩ := hWtriv (V.1 : (inverseSituation Y M).X.Opens) hVW
  obtain ⟨ψ, hψC, hψker, hψreg⟩ := (inverseSituation Y M).exists_chartEquiv V eN
  have hzs : AlgebraicGeometry.zeroScheme (lineBundleSpace Y M) (lineBundlePullback Y M)
        (fibreCoordinate Y M) = (inverseSituation Y M).zeroSection.ker :=
    (zeroScheme_fibreCoordinate Y M).trans
      ((zeroScheme_tautologicalSectionBase (inverseSituation Y M)).trans
        (inverseSituation Y M).zeroScheme_tautologicalSectionBase_eq_ker_zeroSection)
  let W : (lineBundleSpace Y M).affineOpens :=
    ⟨lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens), isAffineOpen_preimage_lineBundleProj Y M V⟩
  let s : Γ(lineBundlePullback Y M, lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)) :=
    (lineBundlePullback Y M).presheaf.map (homOfLE le_top).op (fibreCoordinate Y M)
  have hideal : (AlgebraicGeometry.zeroScheme (lineBundleSpace Y M) (lineBundlePullback Y M)
      (fibreCoordinate Y M)).ideal W = Ideal.span {ψ.symm (MvPolynomial.X 0)} :=
    Eq.trans
      (congrArg (fun I : AlgebraicGeometry.Scheme.IdealSheafData (lineBundleSpace Y M) =>
          I.ideal W) hzs)
      ((((inverseSituation Y M).zeroSection.ker_apply W).trans
          ((inverseSituation Y M).ker_zeroSectionChartMap_eq V).symm).trans hψker)
  refine ⟨V, hyV, ψ, hψC, hideal, ?_⟩
  -- the fibre coordinate itself is the variable, in a suitable trivialization
  obtain ⟨e₀⟩ := Stacks.Modules.nonempty_linearEquiv_sections_pullback (lineBundleProj Y M) M
    V.2 W.2 heM
  have hA : (AlgebraicGeometry.zeroScheme (lineBundleSpace Y M) (lineBundlePullback Y M)
      (fibreCoordinate Y M)).ideal W = Ideal.span {e₀ s} :=
    Stacks.Divisors.zeroScheme_ideal_of_trivialization (lineBundleSpace Y M)
      (lineBundlePullback Y M) (fibreCoordinate Y M) W e₀ _ rfl
  obtain ⟨c, hc⟩ := exists_unit_of_span_eq (e₀ s) (ψ.symm (MvPolynomial.X 0)) hψreg
    (hA.symm.trans hideal)
  refine ⟨e₀.trans (LinearEquiv.smulOfUnit c⁻¹), ?_⟩
  show ((c⁻¹ : _ˣ) : Γ(lineBundleSpace Y M, lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens))) • e₀ s = _
  rw [smul_eq_mul, hc]
  exact Units.inv_mul_cancel_left c _

end FibreCoordinate

end Stacks.LineBundle

end
