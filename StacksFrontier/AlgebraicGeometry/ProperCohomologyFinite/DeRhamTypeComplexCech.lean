module

public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoverVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineIntersectionComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.DeRhamTypeComplexAlgebra
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.DeRhamTypeComplexCechBridge
public import StacksFrontier.AlgebraicGeometry.TwistCohomologyFiniteness.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.ModuleValuedTotalComplex

/-!
# The Čech complex of a bounded complex with coherent terms on a proper scheme

Let `f : X ⟶ S` be a proper morphism to an affine scheme with `A = Γ(S, 𝒪_S)` Noetherian, and
let `K^•` be a bounded below complex of sheaves of `f^{-1}𝒪_S`-modules on `X` whose terms are
(the restrictions of scalars of) coherent `𝒪_X`-modules; the differentials of `K^•` are only
`f^{-1}𝒪_S`-linear, as for a de Rham complex `M ⊗ Ω^•_{X/S}` of a module with an integrable
connection. For a finite affine open cover `U_0, …, U_m` of `X`, the total complex of the Čech
double complex `Č^p(𝒰, K^q) = ∏_{(i_0, …, i_p)} K^q(U_{i_0} ∩ ⋯ ∩ U_{i_p})` (ordered tuples) is a
complex of `Γ(X, f^{-1}𝒪_S)`-modules, hence of `A`-modules, and:

* its cohomology is a finite `A`-module in every degree;
* if `K^•` is concentrated in degrees `≤ n` its cohomology vanishes in degrees `> n + m`.

## Main definitions

* `AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom`: the ring map
  `Γ(S, 𝒪_S) ⟶ Γ(X, f^{-1}𝒪_S)` through which the Čech complex is read over `A`.
* `AlgebraicGeometry.DeRhamTypeComplex.totalCechComplex`: the total Čech complex of `K^•`.

## Main results

* `AlgebraicGeometry.DeRhamTypeComplex.moduleFinite_homology_totalCechComplex`: the finiteness.
* `AlgebraicGeometry.DeRhamTypeComplex.isZero_homology_totalCechComplex`: the vanishing.

## The proof

The columns of the Čech double complex are the Čech complexes `Č^•(𝒰, K^q)` of the single
terms. The Čech complex of `K^q`, read over `f^{-1}𝒪_S`, is the Čech complex of the coherent
`𝒪_X`-module underlying it, read along `Γ(X, f^{-1}𝒪_S) ⟶ Γ(X, 𝒪_X)`
(`AlgebraicGeometry.DeRhamTypeComplex.cechComplexRestrictScalarsIso`); the intersections of the
cover are affine because `X` is separated, so this computes `H^p(X, K^q)` by [Stacks, Tag 01XD],
which is a finite `A`-module by [Stacks, Tag 02O6] and vanishes for `p > m` by
[Stacks, Tag 01XI]. A weak Serre class containing the column cohomology of a diagonally finite
double complex contains the cohomology of the total complex, and finite `A`-modules form one
since `A` is Noetherian; this gives the finiteness. The vanishing is
`AlgebraicGeometry.DeRhamTypeComplex.isZero_homology_total_of_exactAt`.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 0FLY](https://stacks.math.columbia.edu/tag/0FLY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace ComplexShape
open Stacks.DeRhamDirectImage Stacks.Cohomology.CechSheaf Stacks.Cohomology.CechDerived

universe u

namespace AlgebraicGeometry.DeRhamTypeComplex

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-! ### The rings -/

/-- The sheaf of rings `f^{-1}𝒪_S` on `X`, over which the terms of `K^•` are modules. -/
abbrev inverseImageBaseRing : Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  ringCatSheaf (inverseImageBase f)

/-- The structural morphism `f^{-1}𝒪_S ⟶ 𝒪_X` of sheaves of rings. -/
abbrev inverseImageBaseRingMap : inverseImageBaseRing f ⟶ X.ringCatSheaf :=
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map (inverseImageStructureMap f)

/-- **The ring map `Γ(S, 𝒪_S) ⟶ Γ(X, f^{-1}𝒪_S)`**: the global component of the unit
`𝒪_S ⟶ f_* f^{-1}𝒪_S`. -/
def inverseImageBaseRingHom :
    Γ(S, ⊤) →+* SectionRing (inverseImageBaseRing f) ⊤ :=
  ((inverseImageBaseProjection f).hom.c.app (op ⊤)).hom

/-- The ring map `Γ(S, 𝒪_S) ⟶ Γ(X, f^{-1}𝒪_S)` followed by the structural map to `Γ(X, 𝒪_X)` is
`f^♯` on global sections. -/
theorem inverseImageBaseRingMap_comp_inverseImageBaseRingHom :
    ((inverseImageBaseRingMap f).hom.app (op ⊤)).hom.comp (inverseImageBaseRingHom f) =
      f.appTop.hom := by
  have h := PresheafedSpace.congr_app
    (congrArg InducedCategory.Hom.hom (toInverseImageBase_comp f)) (op ⊤)
  ext a
  refine (congrArg (fun φ => (CommRingCat.Hom.hom φ) a) h).trans ?_
  rw [CommRingCat.comp_apply]
  have hid : X.toRingedSpace.presheaf.map (eqToHom (by simp) : (op (⊤ : X.Opens)) ⟶ op ⊤) =
      𝟙 _ := by
    rw [eqToHom_refl, CategoryTheory.Functor.map_id]
  exact congrArg (fun φ => (CommRingCat.Hom.hom φ) _) hid

/-! ### The Čech complex of a single term -/

section Cech

variable {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)

/-- **The Čech cohomology of a quasi-coherent `𝒪_X`-module, computed over `f^{-1}𝒪_S`, is its
cohomology**: for a cover all of whose finite intersections are affine, the `p`-th cohomology of
the Čech complex of `M` read as a sheaf of `f^{-1}𝒪_S`-modules is `H^p(X, M)` read along
`Γ(X, f^{-1}𝒪_S) ⟶ Γ(X, 𝒪_X)`. The Čech complex over `f^{-1}𝒪_S` is the one over `𝒪_X` read
along that map (`cechComplexRestrictScalarsIso`), restriction of scalars is exact, and the Čech
cohomology over `𝒪_X` is `H^p(X, M)` by [Stacks, Tag 01XD]. -/
def cechHomologyRestrictScalarsIso
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ j, U (s j)))
    (M : X.Modules) [M.IsQuasicoherent] (p : ℕ) :
    ((cechComplexIntFunctor (inverseImageBaseRing f) ⊤ U hU).obj
        ((pushforward (toInverseImageBase f)).obj M)).homology (p : ℤ) ≅
      (ModuleCat.restrictScalars ((inverseImageBaseRingMap f).hom.app (op ⊤)).hom).obj
        (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived p).obj M) :=
  haveI := Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars
    ((inverseImageBaseRingMap f).hom.app (op ⊤)).hom
  HomologicalComplex.extendHomologyIso _ embeddingUpNat (embeddingUpNat_f p) ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).mapIso
      (cechComplexRestrictScalarsIso (inverseImageBaseRingMap f) ⊤ U hU M) ≪≫
    ((cechComplex.{u, u, u, u} ⊤ U hU M).sc p).mapHomologyIso
      (ModuleCat.restrictScalars ((inverseImageBaseRingMap f).hom.app (op ⊤)).hom) ≪≫
    (ModuleCat.restrictScalars ((inverseImageBaseRingMap f).hom.app (op ⊤)).hom).mapIso
      (rightDerivedEvaluationCechHomologyIso X ⊤ U hU haff M p).symm

end Cech

/-! ### Separatedness -/

/-- **A scheme proper over an affine scheme has affine diagonal**: it is separated, as the
composite of the separated morphisms `X ⟶ S ⟶ Spec ℤ`, and the diagonal of a separated scheme is
a closed immersion. -/
theorem isAffineHom_diagonal_of_isProper [IsAffine S] [IsProper f] :
    IsAffineHom (pullback.diagonal (terminal.from X)) := by
  rw [← terminal.hom_ext (f ≫ terminal.from S) (terminal.from X)]
  infer_instance

/-! ### The total Čech complex -/

section Total

variable {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)

/-- **The total complex of the Čech double complex** `Č^p(𝒰, K^q) = ∏ K^q(U_{i_0 … i_p})`, over
ordered tuples `(i_0, …, i_p)`, of a complex `K^•` of `f^{-1}𝒪_S`-modules, the Čech degree first:
a complex of `Γ(X, f^{-1}𝒪_S)`-modules. -/
abbrev totalCechComplex (K : CochainComplex (SheafOfModules.{u} (inverseImageBaseRing f)) ℤ) :
    CochainComplex (ModuleCat.{u} (SectionRing (inverseImageBaseRing f) ⊤)) ℤ :=
  (Stacks.Cech.Linear.totalCechComplexFunctor _ (inverseImageBaseRing f) ⊤ U hU).obj K

/-- The total Čech complex is the total complex of the flip of the Čech double complex
`cechBicomplex`, whose `(q, p)` term is `Č^p(𝒰, K^q)`. -/
theorem totalCechComplex_eq (K : CochainComplex (SheafOfModules.{u} (inverseImageBaseRing f)) ℤ) :
    totalCechComplex f U hU K =
      (cechBicomplex (inverseImageBaseRing f) ⊤ U hU K).flip.total (up ℤ) :=
  rfl

/-- The cohomology of the total Čech complex is that of the total complex of the Čech double
complex taken in the other order. -/
def totalCechComplexHomologyIso (K : CochainComplex (SheafOfModules.{u} (inverseImageBaseRing f)) ℤ)
    (j : ℤ) :
    (totalCechComplex f U hU K).homology j ≅
      ((cechBicomplex (inverseImageBaseRing f) ⊤ U hU K).total (up ℤ)).homology j :=
  (HomologicalComplex.homologyFunctor _ (up ℤ) j).mapIso
    ((cechBicomplex (inverseImageBaseRing f) ⊤ U hU K).totalFlipIso (up ℤ))

/-- The ring of global sections of a locally Noetherian scheme that is affine is Noetherian. -/
private theorem isNoetherianRing_of_isLocallyNoetherian (S : Scheme.{u}) [IsAffine S]
    [IsLocallyNoetherian S] : IsNoetherianRing Γ(S, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩

/-- **The column cohomology is finite**: for a coherent `𝒪_X`-module `M` and a cover with
affine finite intersections, every cohomology module of the Čech complex of `M` read over
`f^{-1}𝒪_S` is finite over `Γ(S, 𝒪_S)`. In nonnegative degree it is `H^p(X, M)`
(`cechHomologyRestrictScalarsIso`), finite by [Stacks, Tag 02O6]. -/
theorem finiteOver_homology_cechComplexInt [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ j, U (s j)))
    (M : X.Modules) [M.IsCoherent] (p : ℤ) :
    finiteOver (inverseImageBaseRingHom f)
      (((cechComplexIntFunctor (inverseImageBaseRing f) ⊤ U hU).obj
        ((pushforward (toInverseImageBase f)).obj M)).homology p) := by
  have : M.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent M
  have := isNoetherianRing_of_isLocallyNoetherian S
  have := isSerreClass_finiteOver.{u} (inverseImageBaseRingHom f)
  rcases lt_or_ge p 0 with hp | hp
  · exact (finiteOver (inverseImageBaseRingHom f)).prop_of_isZero
      (StacksDraft.TotalComplexQuasiIso.isZero_homology_of_isZero_X p
        (isZero_cechComplexIntFunctor_X _ _ _ _ _ p hp))
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  refine (finiteOver (inverseImageBaseRingHom f)).prop_of_iso
    (cechHomologyRestrictScalarsIso f U hU haff M n).symm ?_
  rw [finiteOver_iff]
  exact @Module.Finite.equiv _ _ _ _ _ _ _ _
    (ProperCoherenceWitness.moduleFinite_cohomology f M n)
    (ModuleCat.restrictScalarsComp'App (inverseImageBaseRingHom f)
    ((inverseImageBaseRingMap f).hom.app (op ⊤)).hom f.appTop.hom
    (inverseImageBaseRingMap_comp_inverseImageBaseRingHom f).symm _).toLinearEquiv

/-- **The column cohomology vanishes above the size of the cover**: for a quasi-coherent
`𝒪_X`-module `M` on a scheme with affine diagonal and a cover by `t` affine opens, the Čech
complex of `M` read over `f^{-1}𝒪_S` is exact in degrees `≥ t`. It computes `H^p(X, M)`
(`cechHomologyRestrictScalarsIso`), which vanishes for `p ≥ t` by [Stacks, Tag 01XI]. -/
theorem exactAt_cechComplexInt [IsAffineHom (pullback.diagonal (terminal.from X))] [Finite I]
    (hUaff : ∀ i, IsAffineOpen (U i)) (M : X.Modules) [M.IsQuasicoherent] (p : ℤ)
    (hp : (Nat.card I : ℤ) ≤ p) :
    ((cechComplexIntFunctor (inverseImageBaseRing f) ⊤ U hU).obj
        ((pushforward (toInverseImageBase f)).obj M)).ExactAt p := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans (Int.natCast_nonneg _) hp)
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine IsZero.of_iso ?_ (cechHomologyRestrictScalarsIso f U hU
    (fun _ s => IsAffineOpen.iInf fun j => hUaff (s j)) M n)
  refine Functor.map_isZero _ ?_
  let e := Finite.equivFin I
  refine Stacks.Cohomology.Cech.isZero_rightDerived_evaluation_of_isZero_hgroup X ⊤ M n ?_
  refine Stacks.Cohomology.AffineCover.isZero_cohomology_of_finite_affine_cover X
    (U ∘ e.symm) (fun i => hUaff _) ?_ M n (by omega)
  rw [hU]
  exact e.symm.iSup_comp

/-- **The cohomology of the total Čech complex of a bounded below complex with coherent terms is
finite.** Let `f : X ⟶ S` be proper with `S` affine and locally Noetherian, let `𝒰` be a cover of
`X` by affine opens, and let `K^•` be a bounded below complex of `f^{-1}𝒪_S`-modules each of whose
terms is a coherent `𝒪_X`-module read over `f^{-1}𝒪_S` (its differentials being only
`f^{-1}𝒪_S`-linear). Then every cohomology module of the total complex of the Čech double complex
`∏ K^q(U_{i_0 … i_p})` is a finite `Γ(S, 𝒪_S)`-module.

The column cohomology `Ȟ^p(𝒰, K^q) = H^p(X, K^q)` is finite (`finiteOver_homology_cechComplexInt`),
finite modules over the Noetherian ring `Γ(S, 𝒪_S)` form a weak Serre class, and a weak Serre
class containing the column cohomology of a diagonally finite double complex contains the
cohomology of its total complex. -/
theorem moduleFinite_homology_totalCechComplex [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
    (hUaff : ∀ i, IsAffineOpen (U i))
    (K : CochainComplex (SheafOfModules.{u} (inverseImageBaseRing f)) ℤ)
    (a : ℤ) [K.IsStrictlyGE a]
    (hK : ∀ q, ∃ M : X.Modules, M.IsCoherent ∧
      Nonempty (K.X q ≅ (pushforward (toInverseImageBase f)).obj M))
    (j : ℤ) :
    Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars (inverseImageBaseRingHom f)).obj
      ((totalCechComplex f U hU K).homology j)) := by
  have := isNoetherianRing_of_isLocallyNoetherian S
  have := isAffineHom_diagonal_of_isProper f
  have := isSerreClass_finiteOver.{u} (inverseImageBaseRingHom f)
  let B := cechBicomplex (inverseImageBaseRing f) ⊤ U hU K
  let P := finiteOver (inverseImageBaseRingHom f)
  have hB : ∀ n : ℤ, {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero ((B.X pq.1).X pq.2)}.Finite := by
    intro n
    refine ((diagonalFinite_cechBicomplex (inverseImageBaseRing f) ⊤ U hU K a n).image
      fun q => (q, n - q)).subset ?_
    rintro ⟨q, p⟩ ⟨hqp, hz⟩
    obtain rfl : p = n - q := by simp only at hqp; omega
    exact ⟨q, hz, rfl⟩
  have hcol (q p : ℤ) : P ((B.X q).homology p) := by
    obtain ⟨M, _, ⟨e⟩⟩ := hK q
    refine P.prop_of_iso ((HomologicalComplex.homologyFunctor _ (up ℤ) p).mapIso
      ((cechComplexIntFunctor (inverseImageBaseRing f) ⊤ U hU).mapIso e)).symm ?_
    exact finiteOver_homology_cechComplexInt f U hU
      (fun _ s => IsAffineOpen.iInf fun j => hUaff (s j)) M p
  exact P.prop_of_iso (totalCechComplexHomologyIso f U hU K j).symm
    (weakSerre_homology_total B hB P hcol j)

/-- **The cohomology of the total Čech complex of a bounded complex with quasi-coherent terms
vanishes above the expected degree.** Let `X` have affine diagonal (for instance, be proper over an
affine scheme, `isAffineHom_diagonal_of_isProper`), let `𝒰` be a cover of `X` by `t` affine opens,
and let `K^•` be a complex of `f^{-1}𝒪_S`-modules concentrated in degrees `[a, b]` each of whose
terms is a quasi-coherent `𝒪_X`-module read over `f^{-1}𝒪_S`. Then the total complex of the Čech
double complex has no cohomology in degrees `> b + t - 1`: the columns `Č^•(𝒰, K^q)` are exact
above `t - 1` (`exactAt_cechComplexInt`), which is
`AlgebraicGeometry.DeRhamTypeComplex.isZero_homology_total_of_exactAt`. -/
theorem isZero_homology_totalCechComplex [IsAffineHom (pullback.diagonal (terminal.from X))]
    [Finite I] (hUaff : ∀ i, IsAffineOpen (U i))
    (K : CochainComplex (SheafOfModules.{u} (inverseImageBaseRing f)) ℤ) (a b : ℤ)
    [K.IsStrictlyGE a]
    [K.IsStrictlyLE b]
    (hK : ∀ q, ∃ M : X.Modules, M.IsQuasicoherent ∧
      Nonempty (K.X q ≅ (pushforward (toInverseImageBase f)).obj M))
    (j : ℤ) (hj : b + Nat.card I - 1 < j) :
    IsZero ((totalCechComplex f U hU K).homology j) := by
  let B := cechBicomplex (inverseImageBaseRing f) ⊤ U hU K
  have hneg : ∀ q p : ℤ, p < 0 → IsZero ((B.X q).X p) :=
    fun q p hp => isZero_cechBicomplex_X_X _ ⊤ U hU K q p (Or.inr hp)
  have hzero : ∀ q, IsZero (K.X q) → IsZero (B.X q) :=
    fun q h => (cechComplexIntFunctor (inverseImageBaseRing f) ⊤ U hU).map_isZero h
  have : B.HasTotal (up ℤ) :=
    StacksDraft.TotalComplexQuasiIso.hasTotal_of_bounded B a hneg
      fun q hq => hzero q (K.isZero_of_isStrictlyGE a q hq)
  refine IsZero.of_iso ?_ (totalCechComplexHomologyIso f U hU K j)
  refine isZero_homology_total_of_exactAt B a b (Nat.card I - 1)
    (fun q hq => hzero q (K.isZero_of_isStrictlyGE a q hq))
    (fun q hq => hzero q (K.isZero_of_isStrictlyLE b q hq)) hneg
    (fun q p hp => ?_) j (by omega)
  obtain ⟨M, _, ⟨e⟩⟩ := hK q
  refine (exactAt_cechComplexInt f U hU hUaff M p (by omega)).of_iso ?_
  exact ((cechComplexIntFunctor (inverseImageBaseRing f) ⊤ U hU).mapIso e).symm

end Total

end AlgebraicGeometry.DeRhamTypeComplex

end
