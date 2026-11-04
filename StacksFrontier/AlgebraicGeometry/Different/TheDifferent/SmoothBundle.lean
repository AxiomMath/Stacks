module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFactorizationInvertible
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenFormsMapSections
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemePower
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChangeSections
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorSections
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.TensorOfGeneratorTorsors

/-!
# The bundle identity for the different of a quasi-finite morphism of smooth schemes

Let `X` and `Y` be smooth of relative dimension `n` over `S` and let `f : Y ⟶ X` be a morphism
over `S`.  The canonical map `∧ⁿ(df) : f^*Ω^n_{X/S} ⟶ Ω^n_{Y/S}` is a morphism of invertible
modules.  **On a small enough affine chart both are trivialized and `∧ⁿ(df)` becomes
multiplication by a local generator of the Kähler different of `f`**, and from that the last
assertion of [Stacks, Tag 0BWJ],

`f^*Ω^n_{X/S} ⊗_{𝒪_Y} 𝒪_Y(R) = Ω^n_{Y/S}`,

follows once `∧ⁿ(df)` is written as a tensor product with an invertible module carrying a global
section, which it always can be
(`Stacks.SheafOfModules.TensorFactorization.exists_tensorFactorization`).

## Main definitions

* `Stacks.Discriminant.topFormsMap`: `∧ⁿ(df)`, the canonical map on relative differential
  `n`-forms.
* `Stacks.Discriminant.kaehlerSectionsEquiv`: the existence half of [Stacks, Tag 01UT] as a
  linear equivalence.

## Main results

* `Stacks.Discriminant.exists_chart_trivialization_topFormsMap`: around every point of `Y`,
  inside any prescribed open, an affine chart carrying trivializations of `f^*Ω^n_{X/S}` and of
  `Ω^n_{Y/S}` in which `∧ⁿ(df)` is multiplication by a generator `d` of the ideal of the Kähler
  different.
* `Stacks.Discriminant.zeroScheme_eq_kaehlerDifferent_of_tensorFactorization`: given a tensor
  factorization of `∧ⁿ(df)`, the zero scheme of its section is the closed subscheme cut out by
  the Kähler different.
* `Stacks.Discriminant.nonempty_tensorIso_invertibleSheaf_kaehlerDifferent_of_tensorFactorization`:
  given such a factorization and étaleness at the associated points, the bundle identity.
* `Stacks.Discriminant.nonempty_tensorIso_invertibleSheaf_kaehlerDifferent_of_etaleAt`:
  **[Stacks, Tag 0BWJ]**, the bundle identity `f^*Ω^n_{X/S} ⊗_{𝒪_Y} 𝒪_Y(R) ≅ Ω^n_{Y/S}` when
  `f` is étale at the associated points of `Y`.

## Implementation notes

The chart is the one of
`Stacks.Discriminant.exists_chart_le_kaehlerDifferent_ideal_eq_span_det`: an affine `V = Spec B`
over an affine `U = Spec A` over an affine `W = Spec R` on which `Ω[A⁄R]` and `Ω[B⁄R]` are free
of rank `n`.  Three identifications turn the chartwise local equation into a statement about
trivializations:

* the sections of `Ω_{X/S}` over `U` are `Ω[A⁄R]` and those of `Ω_{Y/S}` over `V` are `Ω[B⁄R]`
  ([Stacks, Tag 01UT], `Stacks.AlgebraicGeometry.AffineDifferentialsIso.isIso_kaehlerToSections`);
* the sections of `f^*Ω_{X/S}` over `V` are `B ⊗_A Ω[A⁄R]`
  (`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` of [Stacks, Tag 01I9]), through which
  the sections over `V` of the canonical map on relative differentials are
  `KaehlerDifferential.mapBaseChange R A B`;
* the sections over `V` of `∧ⁿ(df)` are then `exteriorPower.map n` of that map
  (`relativeDifferentialFormsMap_app_exteriorPower_map` in the namespace
  `Stacks.AlgebraicGeometry.AffineOpenDifferentialForms`).

The two trivializations are `exteriorPower.topLinearEquivOfBasis` of the two bases transported
along those identifications: the top exterior power of a free module of rank `n` is free of rank
one on the wedge of a basis.  Each step whose two sides differ only definitionally is isolated
in its own declaration — `Stacks.Discriminant.topTrivialization_inv`,
`Stacks.Discriminant.topTrivialization_apply`,
`Stacks.Discriminant.exists_pullbackDifferentialsSectionsEquiv` — because the whole chain in one
declaration exhausts the elaborator's heartbeats.

**Why the tensor factorization is a hypothesis of the middle two results.** They take as a
hypothesis an invertible `ℳ`, a global section `σ` of `ℳ` and an isomorphism
`f^*Ω^n_{X/S} ⊗ ℳ ≅ Ω^n_{Y/S}` carrying `x ⊗ σ` to `∧ⁿ(df)(x)`.  Such a factorization exists
for any morphism of invertible modules — that is
`Stacks.SheafOfModules.TensorFactorization.exists_tensorFactorization`, which has no geometry in
it — and the last result below supplies it, so the tag is registered there and not on the two
conditional statements.  Keeping them separate is what keeps the chartwise argument, which is
the geometric content, free of the monoidal bookkeeping.

## References

* [Stacks Project, Tag 0BWJ](https://stacks.math.columbia.edu/tag/0BWJ)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AffineExteriorPower (affineOpenExteriorPowerΓIso)
open Stacks.AlgebraicGeometry.AffineOpenDifferentialForms (formsPullbackAffineOpenΓIso
  isExteriorAlgebra_relativeDifferentialFormsAlgebra
  relativeDifferentialFormsMap_app_exteriorPower_map)
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection)
open Stacks.Cohomology.Generators (GeneratorSections)
open scoped TensorProduct

universe u

namespace Stacks.Discriminant

variable {S X Y : Scheme.{u}}

/-- The commutative square with identity bottom edge in which a morphism `f : Y ⟶ X` over
`pX : X ⟶ S` sits. -/
theorem comp_eq_comp_id (pX : X ⟶ S) (f : Y ⟶ X) : f ≫ pX = (f ≫ pX) ≫ 𝟙 S :=
  (Category.comp_id _).symm

/-- **`∧ⁿ(df)`**, the canonical map `f^*Ω^n_{X/S} ⟶ Ω^n_{Y/S}` on relative differential
`n`-forms of a morphism `f : Y ⟶ X` over `pX : X ⟶ S`. -/
abbrev topFormsMap (pX : X ⟶ S) (f : Y ⟶ X) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms pX (n : ℤ)) ⟶
      Scheme.Hom.relativeDifferentialForms (f ≫ pX) (n : ℤ) :=
  Scheme.Hom.relativeDifferentialFormsMap f pX (f ≫ pX) (𝟙 S) (comp_eq_comp_id pX f) (n : ℤ)

/-! ### Trivializations out of a comparison with a top exterior power -/

/-- **A comparison of a module with the top exterior power of a free module of rank `n`
trivializes it**, and the inverse image of the wedge of the basis is the trivializing element.

Stated at abstract modules: applying it to a comparison of sheaf sections then costs one
unification of the statement rather than an unfolding of the comparison. -/
theorem topTrivialization_inv {R : Type u} [CommRing R] {M : ModuleCat.{u} R} {P : Type u}
    [AddCommGroup P] [Module R P] {n : ℕ} (c : M ≅ ModuleCat.of R (⋀[R]^n P))
    (b : Module.Basis (Fin n) R P) :
    (c.toLinearEquiv.trans (exteriorPower.topLinearEquivOfBasis b))
        (c.inv (exteriorPower.ιMulti R n b)) = 1 :=
  (congrArg (fun z => exteriorPower.topLinearEquivOfBasis b z)
      (Iso.inv_hom_id_apply c (exteriorPower.ιMulti R n b))).trans
    (exteriorPower.topLinearEquivOfBasis_ιMulti b)

/-- **An element carried to `d` times the wedge of the basis is read as `d`** in the
trivialization of `Stacks.Discriminant.topTrivialization_inv`. -/
theorem topTrivialization_apply {R : Type u} [CommRing R] {M : ModuleCat.{u} R} {P : Type u}
    [AddCommGroup P] [Module R P] {n : ℕ} (c : M ≅ ModuleCat.of R (⋀[R]^n P))
    (b : Module.Basis (Fin n) R P) (x : M) (d : R)
    (hx : c.hom x = d • exteriorPower.ιMulti R n b) :
    (c.toLinearEquiv.trans (exteriorPower.topLinearEquivOfBasis b)) x = d := by
  refine (congrArg (fun z => exteriorPower.topLinearEquivOfBasis b z) hx).trans ?_
  rw [map_smul, exteriorPower.topLinearEquivOfBasis_ιMulti, smul_eq_mul, mul_one]

/-- **The sections of `Ω_{X/S}` over an affine open are the Kähler differentials of the
sections**, as a linear equivalence: the existence half of [Stacks, Tag 01UT]. -/
def kaehlerSectionsEquiv (q : X ⟶ S) {W : S.Opens} (hW : IsAffineOpen W) {O : X.Opens}
    (hO : IsAffineOpen O) (hOW : O ≤ q ⁻¹ᵁ W) :
    letI := Stacks.Smooth.algebraAppLE q hOW
    Ω[Γ(X, O)⁄Γ(S, W)] ≃ₗ[Γ(X, O)] Γ(Scheme.Hom.relativeDifferentials q, O) :=
  letI := Stacks.Smooth.algebraAppLE q hOW
  haveI := Stacks.AlgebraicGeometry.AffineDifferentialsIso.isIso_kaehlerToSections q hO hOW hW
  LinearEquiv.ofBijective
    (Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections q W O hOW).hom
    (ConcreteCategory.bijective_of_isIso _)

/-- The comparison of `Stacks.Discriminant.kaehlerSectionsEquiv` carries the universal
differential of a section of the structure sheaf to the universal relative differential. -/
theorem kaehlerSectionsEquiv_apply (q : X ⟶ S) {W : S.Opens} (hW : IsAffineOpen W)
    {O : X.Opens} (hO : IsAffineOpen O) (hOW : O ≤ q ⁻¹ᵁ W) :
    letI := Stacks.Smooth.algebraAppLE q hOW
    ∀ x : Ω[Γ(X, O)⁄Γ(S, W)], kaehlerSectionsEquiv q hW hO hOW x =
      (Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections q W O hOW).hom x :=
  fun _ => rfl

/-- **[Stacks, Tag 01X0] (2) at a known zero scheme.**  The closed subscheme appears in the type
of the isomorphism, so the equality is destructured rather than rewritten. -/
theorem nonempty_invertibleSheafIso_of_eq {Z : Scheme.{u}} (L : Z.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L]
    (s : L.sections) (hs : IsRegularSection Z.sheaf.obj Z.ringCatSheaf.property s)
    {E : Z.IdealSheafData} (hE : zeroScheme Z L (s.eval (op ⊤)) = E) :
    Nonempty (Stacks.Divisors.invertibleSheaf' E ≅ L) := by
  cases hE
  obtain ⟨i, -⟩ := (existsUnique_invertibleSheafIso_zeroScheme Z L s hs).exists
  exact ⟨i⟩

section Main

variable (pX : X ⟶ S) (f : Y ⟶ X) (n : ℕ) [IsLocallyNoetherian S]
  [SmoothOfRelativeDimension n pX] [SmoothOfRelativeDimension n (f ≫ pX)]

/-- **The chart of [Stacks, Tag 0BWJ] inside a prescribed open.**  This is
`Stacks.Discriminant.exists_chart_kaehlerDifferent_ideal_eq_span_det` with the chart `V` of `Y`
required to lie inside a given open neighbourhood of the point: the charts come from
`Stacks.Discriminant.exists_isAffineOpen_basis_kaehlerDifferential`, which already shrinks into
any prescribed open. -/
theorem exists_chart_le_kaehlerDifferent_ideal_eq_span_det (y : Y) (T : Y.Opens) (hyT : y ∈ T) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
    ∃ (W : S.Opens) (_ : IsAffineOpen W) (U : X.affineOpens) (V : Y.affineOpens)
      (hUW : U.1 ≤ pX ⁻¹ᵁ W) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (hVW : V.1 ≤ (f ≫ pX) ⁻¹ᵁ W),
      y ∈ V.1 ∧ V.1 ≤ T ∧
      letI := Stacks.Smooth.algebraAppLE pX hUW
      letI := Stacks.Smooth.algebraAppLE f hVU
      letI := Stacks.Smooth.algebraAppLE (f ≫ pX) hVW
      letI := isScalarTower_appLE pX f hUW hVU hVW
      ∃ (bA : Module.Basis (Fin n) Γ(X, U.1) Ω[Γ(X, U.1)⁄Γ(S, W)])
        (bB : Module.Basis (Fin n) Γ(Y, V.1) Ω[Γ(Y, V.1)⁄Γ(S, W)]),
        (kaehlerDifferent f).ideal V =
          Ideal.span {(LinearMap.toMatrix (bA.baseChange Γ(Y, V.1)) bB
            (KaehlerDifferential.mapBaseChange Γ(S, W) Γ(X, U.1) Γ(Y, V.1))).det} := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_smoothOfRelativeDimension pX n
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_smoothOfRelativeDimension (f ≫ pX) n
  obtain ⟨W, hyW, -⟩ := exists_affine_subset ((f ≫ pX).base y) ⊤ trivial
  have hxW : pX.base (f.base y) ∈ W.1 := hyW
  obtain ⟨U, hU, hxU, hUW, bA⟩ :=
    exists_isAffineOpen_basis_kaehlerDifferential (n := n) pX (f.base y) W.2
      (T := pX ⁻¹ᵁ W.1) hxW le_rfl
  obtain ⟨V, hV, hyV, hVT, bB⟩ :=
    exists_isAffineOpen_basis_kaehlerDifferential (n := n) (f ≫ pX) y W.2
      (T := (f ⁻¹ᵁ U) ⊓ T) ⟨hxU, hyT⟩ fun z hz => hUW hz.1
  have hVU : V ≤ f ⁻¹ᵁ U := fun z hz => (hVT hz).1
  refine ⟨W.1, W.2, ⟨U, hU⟩, ⟨V, hV⟩, hUW, hVU, fun z hz => hUW (hVT hz).1, hyV,
    fun z hz => (hVT hz).2, ?_⟩
  obtain ⟨bA⟩ := bA
  obtain ⟨bB⟩ := bB
  exact ⟨bA, bB, kaehlerDifferent_ideal_eq_span_det pX f ⟨U, hU⟩ ⟨V, hV⟩ hUW hVU _ bA bB⟩

omit [IsLocallyNoetherian S] in
/-- **The sections over a chart of the canonical map on relative differentials are
`KaehlerDifferential.mapBaseChange`.**  For affine opens `W = Spec R` of `S`, `U = Spec A` of
`X` and `V = Spec B` of `Y` with `U ≤ pX⁻¹W` and `V ≤ f⁻¹U`, the sections of `f^*Ω_{X/S}` over
`V` are `B ⊗_A Ω[A⁄R]` by a comparison through which the sections over `V` of the canonical map
of [Stacks, Tag 01UV] become `KaehlerDifferential.mapBaseChange R A B` read into
`Stacks.Discriminant.kaehlerSectionsEquiv`.

The comparison is `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` of [Stacks, Tag 01I9]
composed with [Stacks, Tag 01UT] on `U`; it is returned existentially because it is only ever
used through this identity. -/
theorem exists_pullbackDifferentialsSectionsEquiv {W : S.Opens} (hW : IsAffineOpen W)
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V)
    (hUW : U ≤ pX ⁻¹ᵁ W) (hVU : V ≤ f ⁻¹ᵁ U) (hVW : V ≤ (f ≫ pX) ⁻¹ᵁ W) :
    letI := Stacks.Smooth.algebraAppLE pX hUW
    letI := Stacks.Smooth.algebraAppLE f hVU
    letI := Stacks.Smooth.algebraAppLE (f ≫ pX) hVW
    letI := isScalarTower_appLE pX f hUW hVU hVW
    ∃ Teq : Γ(Y, V) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄Γ(S, W)] ≃ₗ[Γ(Y, V)]
        Γ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials pX), V),
      (Scheme.Modules.sectionsLinearMap
          (Scheme.Hom.relativeDifferentialsMap f pX (f ≫ pX) (𝟙 S) (comp_eq_comp_id pX f))
          V).comp Teq.toLinearMap =
        (kaehlerSectionsEquiv (f ≫ pX) hW hV hVW).toLinearMap.comp
          (KaehlerDifferential.mapBaseChange Γ(S, W) Γ(X, U) Γ(Y, V)) := by
  let := Stacks.Smooth.algebraAppLE pX hUW
  let := Stacks.Smooth.algebraAppLE f hVU
  let := Stacks.Smooth.algebraAppLE (f ≫ pX) hVW
  let := isScalarTower_appLE pX f hUW hVU hVW
  have : (Scheme.Hom.relativeDifferentials pX).IsQuasicoherent :=
    Scheme.Hom.isQuasicoherent_relativeDifferentials pX
  let : Module Γ(X, U) Γ((Scheme.Modules.pullback f).obj
      (Scheme.Hom.relativeDifferentials pX), V) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(Y, V))
  have : IsScalarTower Γ(X, U) Γ(Y, V) Γ((Scheme.Modules.pullback f).obj
      (Scheme.Hom.relativeDifferentials pX), V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let ρ : Γ(Scheme.Hom.relativeDifferentials pX, U) →ₗ[Γ(X, U)]
      Γ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials pX), V) :=
    { toFun := pullbackSectionHom f (Scheme.Hom.relativeDifferentials pX) U V hVU
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a =>
        pullbackSectionHom_smul f (Scheme.Hom.relativeDifferentials pX) U V hVU r a }
  have hbc : IsBaseChange Γ(Y, V) ρ :=
    AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso (f.appLE U V hVU).hom rfl
      (affinePullbackSectionsBaseChangeIso f (Scheme.Hom.relativeDifferentials pX) hU hV hVU)
      ρ fun m => affinePullbackSectionsBaseChangeIso_one_tmul f
        (Scheme.Hom.relativeDifferentials pX) hU hV hVU m
  refine ⟨(TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Γ(Y, V) Γ(Y, V))
    (kaehlerSectionsEquiv pX hW hU hUW)).trans hbc.equiv, LinearMap.ext fun t => ?_⟩
  open Stacks.AlgebraicGeometry.AffineDifferentials in
  refine relativeDifferentialsMap_app_kaehlerToSections_eq_mapBaseChange
    f pX (f ≫ pX) (comp_eq_comp_id pX f) W U V hUW hVU hVW _ (fun x => ?_) t
  show hbc.equiv ((1 : Γ(Y, V)) ⊗ₜ (kaehlerSectionsEquiv pX hW hU hUW) x) = _
  rw [hbc.equiv_tmul, one_smul]
  rfl

omit [IsLocallyNoetherian S] [SmoothOfRelativeDimension n pX]
  [SmoothOfRelativeDimension n (f ≫ pX)] in
/-- **The chartwise local equation of `R` read as a pair of trivializations.**  Given the two
comparisons of sections of the preceding lemma and bases of `Ω[A⁄R]` and `Ω[B⁄R]` of rank `n`,
both `f^*Ω^n_{X/S}` and `Ω^n_{Y/S}` are free of rank one over the chart, and `∧ⁿ(df)` carries
the trivializing section of the first to `det(df)` times the trivializing section of the
second.

The trivializations are the wedges of the two bases, carried along the comparison of [Stacks,
Tag 01I8] on the chart; `exteriorPower.map_top_ιMulti_eq_det_smul` is what turns the top
exterior power of `KaehlerDifferential.mapBaseChange` into the determinant. -/
theorem exists_trivialization_of_chart {W : S.Opens} {U : X.Opens} {V : Y.Opens}
    (hV : IsAffineOpen V) (hUW : U ≤ pX ⁻¹ᵁ W) (hVU : V ≤ f ⁻¹ᵁ U)
    (hVW : V ≤ (f ≫ pX) ⁻¹ᵁ W) :
    letI := Stacks.Smooth.algebraAppLE pX hUW
    letI := Stacks.Smooth.algebraAppLE f hVU
    letI := Stacks.Smooth.algebraAppLE (f ≫ pX) hVW
    letI := isScalarTower_appLE pX f hUW hVU hVW
    ∀ (Teq : Γ(Y, V) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄Γ(S, W)] ≃ₗ[Γ(Y, V)]
        Γ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials pX), V))
      (kV : Ω[Γ(Y, V)⁄Γ(S, W)] ≃ₗ[Γ(Y, V)] Γ(Scheme.Hom.relativeDifferentials (f ≫ pX), V)),
      (Scheme.Modules.sectionsLinearMap
          (Scheme.Hom.relativeDifferentialsMap f pX (f ≫ pX) (𝟙 S) (comp_eq_comp_id pX f))
          V).comp Teq.toLinearMap =
        kV.toLinearMap.comp (KaehlerDifferential.mapBaseChange Γ(S, W) Γ(X, U) Γ(Y, V)) →
      ∀ (bA : Module.Basis (Fin n) Γ(X, U) Ω[Γ(X, U)⁄Γ(S, W)])
        (bB : Module.Basis (Fin n) Γ(Y, V) Ω[Γ(Y, V)⁄Γ(S, W)]),
      ∃ (eN : Γ((Scheme.Modules.pullback f).obj
            (Scheme.Hom.relativeDifferentialForms pX (n : ℤ)), V) ≃ₗ[Γ(Y, V)] Γ(Y, V))
        (eG : Γ(Scheme.Hom.relativeDifferentialForms (f ≫ pX) (n : ℤ), V) ≃ₗ[Γ(Y, V)] Γ(Y, V))
        (ν : Γ((Scheme.Modules.pullback f).obj
          (Scheme.Hom.relativeDifferentialForms pX (n : ℤ)), V)),
        eN ν = 1 ∧
          eG (Scheme.Modules.Hom.app (topFormsMap pX f n) V ν) =
            (LinearMap.toMatrix (bA.baseChange Γ(Y, V)) bB
              (KaehlerDifferential.mapBaseChange Γ(S, W) Γ(X, U) Γ(Y, V))).det := by
  let := Stacks.Smooth.algebraAppLE pX hUW
  let := Stacks.Smooth.algebraAppLE f hVU
  let := Stacks.Smooth.algebraAppLE (f ≫ pX) hVW
  let := isScalarTower_appLE pX f hUW hVU hVW
  intro Teq kV hdeg bA bB
  let bN := (bA.baseChange Γ(Y, V)).map Teq
  let bG := bB.map kV
  let cN := formsPullbackAffineOpenΓIso f pX hV n
  let cG := affineOpenExteriorPowerΓIso (Scheme.Hom.relativeDifferentials (f ≫ pX)) hV
    (isExteriorAlgebra_relativeDifferentialFormsAlgebra (f ≫ pX)) n
  have hω : exteriorPower.map n Teq.toLinearMap
      (exteriorPower.ιMulti Γ(Y, V) n (bA.baseChange Γ(Y, V))) =
      exteriorPower.ιMulti Γ(Y, V) n bN := by
    rw [exteriorPower.map_apply_ιMulti]
    exact congrArg _ (funext fun i => (Module.Basis.map_apply _ _ i).symm)
  have hb : exteriorPower.ιMulti Γ(Y, V) n (kV.toLinearMap ∘ (bB : Fin n → _)) =
      exteriorPower.ιMulti Γ(Y, V) n bG :=
    congrArg _ (funext fun i => (Module.Basis.map_apply _ _ i).symm)
  have hkey := relativeDifferentialFormsMap_app_exteriorPower_map f pX (f ≫ pX) hV n
    (comp_eq_comp_id pX f) Teq.toLinearMap kV.toLinearMap
    (KaehlerDifferential.mapBaseChange Γ(S, W) Γ(X, U) Γ(Y, V)) hdeg
    (exteriorPower.ιMulti Γ(Y, V) n (bA.baseChange Γ(Y, V)))
  rw [hω, exteriorPower.map_top_ιMulti_eq_det_smul (bA.baseChange Γ(Y, V)) bB, map_smul,
    exteriorPower.map_apply_ιMulti, hb] at hkey
  exact ⟨cN.toLinearEquiv.trans (exteriorPower.topLinearEquivOfBasis bN),
    cG.toLinearEquiv.trans (exteriorPower.topLinearEquivOfBasis bG),
    cN.inv (exteriorPower.ιMulti Γ(Y, V) n bN),
    topTrivialization_inv cN bN, topTrivialization_apply cG bG _ _ hkey⟩

/-- **The local equation of the different as a trivialized map of line bundles.**  Around every
point of `Y`, inside any prescribed open, there is an affine chart `V` carrying
trivializations of `f^*Ω^n_{X/S}` and of `Ω^n_{Y/S}` in which `∧ⁿ(df)` carries the trivializing
section of the first to `d` times the trivializing section of the second, where `d` generates
the ideal of the Kähler different of `f` over `V`.

In those trivializations `∧ⁿ(df)` *is* multiplication by the local equation of `R`. -/
theorem exists_chart_trivialization_topFormsMap (y : Y) (T : Y.Opens) (hyT : y ∈ T) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
    ∃ (V : Y.affineOpens)
      (eN : Γ((Scheme.Modules.pullback f).obj
          (Scheme.Hom.relativeDifferentialForms pX (n : ℤ)), V.1) ≃ₗ[Γ(Y, V.1)] Γ(Y, V.1))
      (eG : Γ(Scheme.Hom.relativeDifferentialForms (f ≫ pX) (n : ℤ), V.1) ≃ₗ[Γ(Y, V.1)]
        Γ(Y, V.1))
      (ν : Γ((Scheme.Modules.pullback f).obj
        (Scheme.Hom.relativeDifferentialForms pX (n : ℤ)), V.1)) (d : Γ(Y, V.1)),
      y ∈ V.1 ∧ V.1 ≤ T ∧ eN ν = 1 ∧
        eG (Scheme.Modules.Hom.app (topFormsMap pX f n) V.1 ν) = d ∧
        (kaehlerDifferent f).ideal V = Ideal.span {d} := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
  obtain ⟨W, hW, U, V, hUW, hVU, hVW, hyV, hVT, bA, bB, hspan⟩ :=
    exists_chart_le_kaehlerDifferent_ideal_eq_span_det pX f n y T hyT
  obtain ⟨Teq, hdeg⟩ :=
    exists_pullbackDifferentialsSectionsEquiv pX f hW U.2 V.2 hUW hVU hVW
  obtain ⟨eN, eG, ν, hν, hd⟩ :=
    exists_trivialization_of_chart pX f n V.2 hUW hVU hVW Teq _ hdeg bA bB
  exact ⟨V, eN, eG, ν, _, hyV, hVT, hν, hd, hspan⟩

/-! ### The zero scheme of a tensor factorization of `∧ⁿ(df)` -/

/-- **The zero scheme of the section of a tensor factorization of `∧ⁿ(df)` is `R`.**  Suppose
`∧ⁿ(df) : f^*Ω^n_{X/S} ⟶ Ω^n_{Y/S}` is factored as a tensor product with an invertible module
`ℳ` carrying a global section `σ` — that is, an isomorphism `f^*Ω^n_{X/S} ⊗ ℳ ≅ Ω^n_{Y/S}`
carrying `x ⊗ σ` to `∧ⁿ(df)(x)` over every open.  Then the zero scheme of `σ` is the closed
subscheme cut out by the Kähler different of `f`.

On the charts of `Stacks.Discriminant.exists_chart_trivialization_topFormsMap`, shrunk inside
trivializing opens of `f^*Ω^n_{X/S}` and of `ℳ`, the section `σ` is `a` times a generator of
`ℳ` and the trivializing section `ν` is a *unit* times a generator of `f^*Ω^n_{X/S}`; the pure
tensor of the two generators trivializes the tensor product
(`Stacks.Cohomology.Generators.bijective_smul_toTensorSheafSection`), so the local equation `d`
of the different is `a` times a unit.  The local equation of `Z(σ)` is `a`
(`AlgebraicGeometry.zeroScheme_ideal_eq_span_singleton_of_bijective_smul`), so the two ideals
agree on a cover of `Y`. -/
theorem zeroScheme_eq_kaehlerDifferent_of_tensorFactorization (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (σ : M.sections)
    (e : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y.toRingedSpace)).presheaf,
        ((Y.toRingedSpace)).IsSheaf⟩).obj (((Scheme.Modules.pullback f).obj
        (Scheme.Hom.relativeDifferentialForms pX (n : ℤ))))).obj (M)) ≅
      Scheme.Hom.relativeDifferentialForms (f ≫ pX) (n : ℤ))
    (he : ∀ (O : Y.Opens) (x : Γ((Scheme.Modules.pullback f).obj
        (Scheme.Hom.relativeDifferentialForms pX (n : ℤ)), O)),
      Scheme.Modules.Hom.app e.hom O
          (toTensorSheafSection Y.toRingedSpace ((Scheme.Modules.pullback f).obj
            (Scheme.Hom.relativeDifferentialForms pX (n : ℤ))) M (op O)
            (x ⊗ₜ[Y.presheaf.obj (op O)] σ.eval (op O))) =
        Scheme.Modules.Hom.app (topFormsMap pX f n) O x) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
    zeroScheme Y M (σ.eval (op ⊤)) = kaehlerDifferent f := by
  classical
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
  have hN : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property ((Scheme.Modules.pullback f).obj
        (Scheme.Hom.relativeDifferentialForms pX (n : ℤ))) :=
    isInvertible_pullback_relativeDifferentialForms pX f n
  have hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M := ‹_›
  choose UN hyUN gN using
    exists_affineOpens_generator (X := Y) ((Scheme.Modules.pullback f).obj
      (Scheme.Hom.relativeDifferentialForms pX (n : ℤ)))
  choose UM hyUM gM using exists_affineOpens_generator (X := Y) M
  choose V eN eG ν d hyV hVT hν hd hspan using fun y : Y =>
    exists_chart_trivialization_topFormsMap pX f n y ((UN y).1 ⊓ (UM y).1) ⟨hyUN y, hyUM y⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top V
    (le_antisymm le_top fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyV y⟩) fun y => ?_
  -- the two generators, restricted to the chart
  let gNy : GeneratorSections Y.toRingedSpace ((Scheme.Modules.pullback f).obj
      (Scheme.Hom.relativeDifferentialForms pX (n : ℤ))) (V y).1 :=
    Stacks.SheafOfModules.generatorRestrict _ (fun z hz => ((hVT y) hz).1) (gN y).some
  let gMy : GeneratorSections Y.toRingedSpace M (V y).1 :=
    Stacks.SheafOfModules.generatorRestrict _ (fun z hz => ((hVT y) hz).2) (gM y).some
  let gNv : Γ((Scheme.Modules.pullback f).obj
    (Scheme.Hom.relativeDifferentialForms pX (n : ℤ)), (V y).1) := gNy.val
  let gMv : Γ(M, (V y).1) := gMy.val
  have hbij : ∀ (L : Y.Modules) (g : GeneratorSections Y.toRingedSpace L (V y).1)
      (v : Γ(L, (V y).1)), v = g.val → Function.Bijective (fun r : Γ(Y, (V y).1) => r • v) := by
    rintro L g - rfl
    have h := g.property (V y).1 le_rfl
    rwa [Stacks.SheafOfModules.generator_restrict_self _ (V y).1 g] at h
  -- the coefficients of `σ` and of the trivializing section `ν` on the chart
  obtain ⟨a, ha⟩ := (hbij _ gMy gMv rfl).surjective (σ.eval (op (V y).1))
  obtain ⟨b, hb⟩ := (hbij _ gNy gNv rfl).surjective (ν y)
  replace ha : a • gMv = σ.eval (op (V y).1) := ha
  replace hb : b • gNv = ν y := hb
  -- `b` is a unit, because `ν` is itself a trivializing section
  have hbunit : IsUnit b := by
    refine IsUnit.of_mul_eq_one (eN y gNv) ?_
    rw [← smul_eq_mul, ← map_smul, hb]
    exact hν y
  -- the tensor product and the pure tensor of the two generators, read at the index that
  -- `AlgebraicGeometry.Scheme.Modules` is written over: the action of a section of `𝒪_Y` on a
  -- section of the tensor product is then the one the rest of this proof spells
  let T : Y.Modules := ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj ((Scheme.Modules.pullback f).obj
        (Scheme.Hom.relativeDifferentialForms pX (n : ℤ)))).obj M
  let gTv : Γ(T, (V y).1) := toTensorSheafSection Y.toRingedSpace
    ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms pX (n : ℤ))) M
    (op (V y).1) (gNv ⊗ₜ[Y.presheaf.obj (op (V y).1)] gMv)
  let gTa : Γ(T, (V y).1) := toTensorSheafSection Y.toRingedSpace
    ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms pX (n : ℤ))) M
    (op (V y).1) (gNv ⊗ₜ[Y.presheaf.obj (op (V y).1)] (a • gMv))
  -- the pure tensor of the two generators trivializes the tensor product over the chart
  have hbijT : Function.Bijective (fun r : Γ(Y, (V y).1) => r • gTv) :=
    Stacks.Cohomology.Generators.bijective_smul_toTensorSheafSection Y.toRingedSpace _ _
      (V y).1 gNy gMy
  -- the two bilinearity steps, stated at this file's spelling of the base ring
  have hleft : toTensorSheafSection Y.toRingedSpace ((Scheme.Modules.pullback f).obj
        (Scheme.Hom.relativeDifferentialForms pX (n : ℤ))) M (op (V y).1)
        ((b • gNv) ⊗ₜ[Y.presheaf.obj (op (V y).1)] (a • gMv)) = b • gTa :=
    Stacks.Cohomology.Generators.toTensorSheafSection_smul_left Y.toRingedSpace
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms pX (n : ℤ))) M
      (V y).1 b gNv (a • gMv)
  have hright : gTa = a • gTv :=
    Stacks.Cohomology.Generators.toTensorSheafSection_smul_right Y.toRingedSpace
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms pX (n : ℤ))) M
      (V y).1 a gNv gMv
  -- so the image under `e` of the pure tensor is a trivializing section of `Ω^n_{Y/S}`
  have hsm : ∀ r : Γ(Y, (V y).1), Scheme.Modules.Hom.app e.hom (V y).1 (r • gTv) =
      r • Scheme.Modules.Hom.app e.hom (V y).1 gTv := fun r => Scheme.Modules.Hom.app_smul e.hom r _
  have hunit : IsUnit (eG y (Scheme.Modules.Hom.app e.hom (V y).1 gTv)) := by
    obtain ⟨w, hw⟩ := hbijT.surjective
      (Scheme.Modules.Hom.app e.inv (V y).1 ((eG y).symm 1))
    replace hw : w • gTv = Scheme.Modules.Hom.app e.inv (V y).1 ((eG y).symm 1) := hw
    refine IsUnit.of_mul_eq_one w ((mul_comm _ _).trans ?_)
    rw [← smul_eq_mul, ← map_smul, ← hsm, hw,
      Stacks.AlgebraicGeometry.AffineOpenDifferentialForms.app_inv_app_cancel e (V y).1,
      (eG y).apply_symm_apply]
  -- the local equation of the different is `a` times a unit
  have hkey : d y = (b * eG y (Scheme.Modules.Hom.app e.hom (V y).1 gTv)) * a := by
    rw [← hd y, ← hb, ← he (V y).1 (b • gNv), ← ha, hleft, hright, smul_smul, hsm, map_smul,
      smul_eq_mul]
    ring
  rw [zeroScheme_ideal_eq_span_singleton_of_bijective_smul Y M (σ.eval (op ⊤)) (V y) gMv
      (hbij _ gMy gMv rfl) a ((Scheme.Modules.map_eval_top M σ (V y).1).trans ha.symm),
    hspan y, hkey, Ideal.span_singleton_mul_left_unit (hbunit.mul hunit)]

/-! ### The bundle identity -/

/-- **[Stacks, Tag 0BWJ], the bundle identity, from a tensor factorization of `∧ⁿ(df)`.**  If
`f` is étale at the associated points of `Y` and `∧ⁿ(df)` is factored as a tensor product with
an invertible module `ℳ` carrying a global section `σ` — an isomorphism
`f^*Ω^n_{X/S} ⊗ ℳ ≅ Ω^n_{Y/S}` carrying `x ⊗ σ` to `∧ⁿ(df)(x)` — then

`f^*Ω^n_{X/S} ⊗_{𝒪_Y} 𝒪_Y(R) ≅ Ω^n_{Y/S}`

as invertible sheaves on `Y`, where `R` is the closed subscheme cut out by the Kähler different
of `f`.

The zero scheme of `σ` is `R`
(`Stacks.Discriminant.zeroScheme_eq_kaehlerDifferent_of_tensorFactorization`) and `R` is an
effective Cartier divisor
(`Stacks.Discriminant.isEffectiveCartierDivisor_kaehlerDifferent_of_etaleAt`), so `σ` is a
nonzerodivisor section ([Stacks, Tag 02OR] (4)) and [Stacks, Tag 01X0] (2) identifies `𝒪_Y(R)`
with `ℳ`; tensoring that identification with `f^*Ω^n_{X/S}` and composing with the given
factorization gives the identity.

The tensor factorization is a hypothesis: it is the one structural input the development does
not yet construct, and the identity is therefore *not* registered under the tag. -/
theorem nonempty_tensorIso_invertibleSheaf_kaehlerDifferent_of_tensorFactorization
    (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (σ : M.sections)
    (e : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y.toRingedSpace)).presheaf,
        ((Y.toRingedSpace)).IsSheaf⟩).obj (((Scheme.Modules.pullback f).obj
        (Scheme.Hom.relativeDifferentialForms pX (n : ℤ))))).obj (M)) ≅
      Scheme.Hom.relativeDifferentialForms (f ≫ pX) (n : ℤ))
    (he : ∀ (O : Y.Opens) (x : Γ((Scheme.Modules.pullback f).obj
        (Scheme.Hom.relativeDifferentialForms pX (n : ℤ)), O)),
      Scheme.Modules.Hom.app e.hom O
          (toTensorSheafSection Y.toRingedSpace ((Scheme.Modules.pullback f).obj
            (Scheme.Hom.relativeDifferentialForms pX (n : ℤ))) M (op O)
            (x ⊗ₜ[Y.presheaf.obj (op O)] σ.eval (op O))) =
        Scheme.Modules.Hom.app (topFormsMap pX f n) O x)
    (hét : ∀ y ∈ Stacks.Divisors.schemeAssociatedPoints Y, EtaleAt f y) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
    Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y.toRingedSpace)).presheaf,
        ((Y.toRingedSpace)).IsSheaf⟩).obj (((Scheme.Modules.pullback f).obj
        (Scheme.Hom.relativeDifferentialForms pX (n : ℤ))))).obj
          ((Stacks.Divisors.invertibleSheaf' (kaehlerDifferent f)))) ≅
      Scheme.Hom.relativeDifferentialForms (f ≫ pX) (n : ℤ)) := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
  have hzs := zeroScheme_eq_kaehlerDifferent_of_tensorFactorization pX f n M σ e he
  have : Stacks.Divisors.IsEffectiveCartierDivisor (kaehlerDifferent f) :=
    isEffectiveCartierDivisor_kaehlerDifferent_of_etaleAt pX f n hét
  have : Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme Y M (σ.eval (op ⊤))) :=
    Stacks.Divisors.isEffectiveCartierDivisor_of_eq hzs
  obtain ⟨i⟩ := nonempty_invertibleSheafIso_of_eq M σ
    ((isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection Y M σ).1 ‹_›) hzs
  exact ⟨Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMapIso
    (X := Y.toRingedSpace) (Iso.refl _) i ≪≫ e⟩

/-- **[Stacks, Tag 0BWJ], the bundle identity.**  If `f` is étale at the associated points of
`Y` then

`f^*Ω^n_{X/S} ⊗_{𝒪_Y} 𝒪_Y(R) ≅ Ω^n_{Y/S}`

as invertible sheaves on `Y`, where `R` is the closed subscheme cut out by the Kähler different
of `f`.

Both `f^*Ω^n_{X/S}` and `Ω^n_{Y/S}` are invertible
(`Stacks.Discriminant.isInvertible_pullback_relativeDifferentialForms` and
`Stacks.Discriminant.isInvertible_relativeDifferentialForms`), so `∧ⁿ(df)` admits a tensor
factorization
(`Stacks.SheafOfModules.TensorFactorization.exists_tensorFactorization`), and
`Stacks.Discriminant.nonempty_tensorIso_invertibleSheaf_kaehlerDifferent_of_tensorFactorization`
turns that factorization into the identity. -/
@[stacks 0BWJ "the Kähler-different form of the bundle identity: if `f` is étale at the
associated points of `Y` then `f^*Ω^n_{X/S} ⊗_{𝒪_Y} 𝒪_Y(R) = Ω^n_{Y/S}` as invertible sheaves on
`Y`, with `R` the closed subscheme cut out by the Kähler different of Tag 0BVW. The Kähler
different equals the different of Tag 0BW4 by Tag 0BWG; the statement for the different itself
is `nonempty_tensorIso_invertibleSheaf_differentIdealSheaf_of_etaleAt`"]
theorem nonempty_tensorIso_invertibleSheaf_kaehlerDifferent_of_etaleAt
    (hét : ∀ y ∈ Stacks.Divisors.schemeAssociatedPoints Y, EtaleAt f y) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
    Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y.toRingedSpace)).presheaf,
        ((Y.toRingedSpace)).IsSheaf⟩).obj (((Scheme.Modules.pullback f).obj
        (Scheme.Hom.relativeDifferentialForms pX (n : ℤ))))).obj
          ((Stacks.Divisors.invertibleSheaf' (kaehlerDifferent f)))) ≅
      Scheme.Hom.relativeDifferentialForms (f ≫ pX) (n : ℤ)) := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
  have hN : Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (_root_.structureSheafRing Y.toRingedSpace).property
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms pX (n : ℤ))) :=
    isInvertible_pullback_relativeDifferentialForms pX f n
  have hL : Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (_root_.structureSheafRing Y.toRingedSpace).property
      (Scheme.Hom.relativeDifferentialForms (f ≫ pX) (n : ℤ)) :=
    isInvertible_relativeDifferentialForms (f ≫ pX) n
  obtain ⟨M, σ, e, hM, he⟩ :=
    Stacks.SheafOfModules.TensorFactorization.exists_tensorFactorization Y.toRingedSpace
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms pX (n : ℤ)))
      (Scheme.Hom.relativeDifferentialForms (f ≫ pX) (n : ℤ)) (topFormsMap pX f n)
  have : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M := hM
  exact nonempty_tensorIso_invertibleSheaf_kaehlerDifferent_of_tensorFactorization pX f n M σ e
    (fun O x => he (op O) x) hét

end Main

end Stacks.Discriminant

end
