module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechDeRhamColumns
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeDividedPowerPolynomial
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.DoubleComplexGeneral
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope.EtaleCoordinatesForms

/-!
# The Čech–de Rham double complex of a single smooth lift with étale coordinates

Fix a global crystalline situation `(p, (S, I, γ), X)` with `S` affine, `p` nilpotent in
`A = Γ(S, 𝒪_S)` and `X` separated, an affine open `U` of `X` and a smooth lift `Y = Spec B` of
`U` with étale coordinates `t_1, …, t_d` (`A[t] → B` étale), giving the object `D = (U, Y, γ_B)`
of `Cris(X/S)`.  For a quasi-coherent module `N` on `CRIS(X/S)` let `B^{a}(⦋n⦌) = N(D^{n+1}) ⊗
Ω^a_{D^{n+1}}` be the Čech–de Rham double complex of the cover by the single object `D`
(`CechEnvelope.cechDeRhamDoubleComplex`, the index type being a singleton), and
`R = N(D) ⊗ Ω^•_{B/A,γ}` the de Rham complex of the canonical connection on `N(D)`.

The diagonals `D ⟶ D^{n+1}` induce a morphism `B ⟶ Const(R)` (`CechEnvelope.diagonalRowHom`),
which is a quasi-isomorphism on every row (`CechEnvelope.quasiIso_rowMap_diagonalRowHom`): the
row `n` is `N(D^{n+1}) ⊗ Ω^•_{D^{n+1}}`, the first projection `pr_0 : D^{n+1} ⟶ D` presents the
envelope `D^{n+1}` as the divided power polynomial algebra `B⟨τ⟩` over `B`
(`CechEnvelope.exists_dpPolynomial_equiv_envelope_const`), so the restriction along `pr_0` is a
quasi-isomorphism by the relative Poincaré lemma ([Stacks, Tag 07LD]), and the restriction along
the diagonal is a left inverse of it.  Hence, the columns off `0` being acyclic
(`CechEnvelope.isZero_homology_cechDeRhamDoubleComplex_X`), the cohomology of the Čech complex
`Č(D, N)` is the de Rham cohomology `H^j(N(D) ⊗ Ω^•_{B/A,γ})`
(`CechEnvelope.singleLiftHomologyIso`, `CechEnvelope.cechSingleLiftHomologyIso`), as `A`-modules,
and so is the crystalline cohomology `H^j(CRIS(X/S), N)` when `U = X`
(`CechEnvelope.crystallineHomologyIsoSingleLift`, `CechEnvelope.crystallineHomologyIsoOfIsAffine`);
both vanish for `j > d`, the divided power differentials of `B` being spanned by the `dt_i`.

## Main definitions

* `CechEnvelope.polyRingMap` — the divided power polynomial algebra `C⟨x_w⟩ → C'⟨x_w⟩` induced by
  a divided power morphism `C → C'`.
* `CechEnvelope.affineEnvelopeObject`, `CechEnvelope.isLimitAffineFan` — the envelope object of a
  tuple of smooth lifts is a product in `AffineCris S`.
* `CechEnvelope.singleLiftDiagonal` — the diagonal `D ⟶ D^{n+1}`.
* `CechEnvelope.diagonalRowHom` — the morphism `B ⟶ Const(R)` of the diagonals.
* `CechEnvelope.singleLiftHomologyIso` — `H^j(Č(D, N)) ≅ H^j(N(D) ⊗ Ω^•_{B/A,γ})`, given acyclic
  columns; `CechEnvelope.cechSingleLiftHomologyIso` — the same, unconditionally.
* `CechEnvelope.crystallineHomologyIsoSingleLift`, `CechEnvelope.crystallineHomologyIsoOfIsAffine`
  — `H^j(CRIS(X/S), N) ≅ H^j(N(D) ⊗ Ω^•_{B/A,γ})`.

## Main results

* `CechEnvelope.quasiIso_map_interπ_zero` — the restriction along `pr_0 : D^{n+1} ⟶ D` is a
  quasi-isomorphism of de Rham complexes.
* `CechEnvelope.quasiIso_rowMap_diagonalRowHom` — the diagonals are a quasi-isomorphism on every
  row.
* `CechEnvelope.isZero_homology_singleLiftDeRhamComplex`,
  `CechEnvelope.isZero_crystallineHomology_singleLift`,
  `CechEnvelope.isZero_crystallineHomology_of_isAffine` — vanishing in degrees `j > d`.

## References

* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology Opposite Simplicial
open Stacks.CechSite.FinalCover Crystalline.CosimplicialDoubleComplex
open DividedPowers Crystalline.DividedPowerPolynomial
open scoped TensorProduct

universe u

namespace Crystalline.GlobalCrystallineSituation.CechEnvelope

/-! ### Change of coefficients of a divided power polynomial algebra -/

section PolyRingMap

variable {C C' : DividedPowerRing.{u}} (W : Type u)

/-- **The divided power polynomial algebra is functorial in the coefficients**: a divided power
morphism `f : C → C'` induces the divided power morphism `C⟨x_w⟩ → C'⟨x_w⟩` which is `f` on the
coefficients and fixes the variables. -/
def polyRingMap (f : DPMorphism C.dividedPowers C'.dividedPowers) :
    DPMorphism (DeRhamPair.polyRing C W).dividedPowers (DeRhamPair.polyRing C' W).dividedPowers :=
  (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial C W (DeRhamPair.polyRing C' W)
    ((setIndexedDividedPowerPolynomialCoefficientDPMorphism C' W).comp f)
    fun w ↦ ⟨dividedPowerPolynomialVariable C' w, variable_mem_polynomialIdeal C' w⟩).choose

/-- `polyRingMap f` is `f` on the coefficients. -/
theorem polyRingMap_algebraMap (f : DPMorphism C.dividedPowers C'.dividedPowers) (c : C) :
    polyRingMap W f (algebraMap C (setIndexedDividedPowerPolynomialAlgebra C W) c) =
      algebraMap C' (setIndexedDividedPowerPolynomialAlgebra C' W) (f c) :=
  congrArg (fun q : DPMorphism C.dividedPowers (DeRhamPair.polyRing C' W).dividedPowers ↦
      q.toRingHom c)
    (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial C W (DeRhamPair.polyRing C' W)
      ((setIndexedDividedPowerPolynomialCoefficientDPMorphism C' W).comp f)
      fun w ↦ ⟨dividedPowerPolynomialVariable C' w,
        variable_mem_polynomialIdeal C' w⟩).choose_spec.1.1

/-- `polyRingMap f` fixes the variables. -/
theorem polyRingMap_variable (f : DPMorphism C.dividedPowers C'.dividedPowers) (w : W) :
    polyRingMap W f (dividedPowerPolynomialVariable C w) = dividedPowerPolynomialVariable C' w :=
  (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial C W (DeRhamPair.polyRing C' W)
    ((setIndexedDividedPowerPolynomialCoefficientDPMorphism C' W).comp f)
    fun w ↦ ⟨dividedPowerPolynomialVariable C' w,
      variable_mem_polynomialIdeal C' w⟩).choose_spec.1.2 w

/-- Two divided power morphisms out of a divided power polynomial algebra agree as soon as they
agree on the coefficients and on the variables. -/
theorem polyRing_dpMorphism_ext {R : DividedPowerRing.{u}}
    {φ ψ : DPMorphism (DeRhamPair.polyRing C W).dividedPowers R.dividedPowers}
    (hc : ∀ c : C, φ (algebraMap C (setIndexedDividedPowerPolynomialAlgebra C W) c) =
      ψ (algebraMap C (setIndexedDividedPowerPolynomialAlgebra C W) c))
    (hv : ∀ w : W, φ (dividedPowerPolynomialVariable C w) =
      ψ (dividedPowerPolynomialVariable C w)) :
    φ = ψ :=
  (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial C W R
    (ψ.comp (setIndexedDividedPowerPolynomialCoefficientDPMorphism C W))
    fun w ↦ ⟨ψ (dividedPowerPolynomialVariable C w), ψ.ideal_comp
      (Ideal.mem_map_of_mem _ (variable_mem_polynomialIdeal C w))⟩).unique
    ⟨DFunLike.ext _ _ hc, hv⟩ ⟨rfl, fun _ ↦ rfl⟩

/-- `polyRingMap` of a right inverse is a right inverse. -/
theorem polyRingMap_polyRingMap {f : DPMorphism C.dividedPowers C'.dividedPowers}
    {g : DPMorphism C'.dividedPowers C.dividedPowers} (hfg : ∀ c, f (g c) = c)
    (q : setIndexedDividedPowerPolynomialAlgebra C' W) :
    polyRingMap W f (polyRingMap W g q) = q := by
  have h : (polyRingMap W f).comp (polyRingMap W g) = DPMorphism.id _ :=
    polyRing_dpMorphism_ext W
      (fun c ↦ by
        change polyRingMap W f (polyRingMap W g (algebraMap C' _ c)) = algebraMap C' _ c
        rw [polyRingMap_algebraMap, polyRingMap_algebraMap, hfg])
      (fun w ↦ by
        change polyRingMap W f (polyRingMap W g (dividedPowerPolynomialVariable C' w)) = _
        rw [polyRingMap_variable, polyRingMap_variable]
        rfl)
  exact congrArg (fun φ : DPMorphism _ _ ↦ φ q) h

end PolyRingMap

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) [S.X.IsSeparated] {ι : Type}
  {U : ι → S.X.Opens} [∀ i, IsAffine (U i)] (L : ∀ i, SmoothLift S (U i).ι)

/-! ### The envelope objects as products in `AffineCris S` -/

/-- The envelope object of a tuple of smooth lifts, in `AffineCris S`. -/
def affineEnvelopeObject {n : ℕ} (x : Fin (n + 1) → ι) : AffineCris S :=
  ⟨crisEnvelopeObject hp L x,
    inferInstanceAs (IsAffine (envelopeObject hp (fun a ↦ L (x a))).thickening.target.scheme)⟩

/-- The projections of the envelope object of a tuple, in `AffineCris S`. -/
def affineProj {n : ℕ} (x : Fin (n + 1) → ι) (a : Fin (n + 1)) :
    affineEnvelopeObject hp L x ⟶ affineObject hp L (x a) :=
  ObjectProperty.homMk (ObjectProperty.homMk (proj hp (fun a ↦ L (x a)) a))

/-- **The envelope object of a tuple is a product of the `D_{x a}` in `AffineCris S`**: the
inclusion into `Cris(X/S)` is fully faithful and carries the fan to `isLimitCrisFan`. -/
def isLimitAffineFan {n : ℕ} (x : Fin (n + 1) → ι) :
    IsLimit (Fan.mk (affineEnvelopeObject hp L x) (affineProj hp L x) :
      Fan fun a ↦ affineObject hp L (x a)) :=
  Fan.IsLimit.mk _
    (fun s ↦ ObjectProperty.homMk
      (Fan.IsLimit.lift (isLimitCrisFan hp L x) fun a ↦ (s.proj a).hom))
    (fun s a ↦ by
      ext1
      exact Fan.IsLimit.fac (isLimitCrisFan hp L x) _ a)
    (fun s m hm ↦ by
      ext1
      refine Fan.IsLimit.hom_ext (isLimitCrisFan hp L x) _ _ fun a ↦ ?_
      exact (congrArg (fun g ↦ g.hom) (hm a)).trans
        (Fan.IsLimit.fac (isLimitCrisFan hp L x) (fun a ↦ (s.proj a).hom) a).symm)

/-- The product `inter (affineObject hp L) x` in `AffineCris S` is the envelope object. -/
def interIsoAffineEnvelope {n : ℕ} (x : Fin (n + 1) → ι) :
    Stacks.CechSite.FinalCover.inter (affineObject hp L) x ≅ affineEnvelopeObject hp L x :=
  (isLimitInterFan (affineObject hp L) x).conePointUniqueUpToIso (isLimitAffineFan hp L x)

/-- The identification with the envelope object is compatible with the projections. -/
theorem interIsoAffineEnvelope_hom_affineProj {n : ℕ} (x : Fin (n + 1) → ι) (a : Fin (n + 1)) :
    (interIsoAffineEnvelope hp L x).hom ≫ affineProj hp L x a = interπ (affineObject hp L) x a :=
  IsLimit.conePointUniqueUpToIso_hom_comp (isLimitInterFan (affineObject hp L) x)
    (isLimitAffineFan hp L x) ⟨a⟩

/-! ### The first projection of a single lift is a divided power polynomial presentation -/

section SingleLift

variable [Unique ι] {N : SheafOfModules.{u} (crystallineStructureSheaf S)}
  (hN : N.IsQuasicoherentOnSite)

include hp in
/-- **The restriction of de Rham complexes along the first projection `pr_0 : D^{n+1} ⟶ D` of the
envelope object of a smooth lift with étale coordinates is a quasi-isomorphism**: through `pr_0`,
the envelope is the divided power polynomial algebra `B⟨τ⟩` over `B`
(`exists_dpPolynomial_equiv_envelope_const`), so this is the relative Poincaré lemma
`quasiIso_crystalDeRhamPresheaf_map`. -/
theorem quasiIso_map_affineProj_zero (n : ℕ) {d : ℕ} (t : Fin d → (L default).ring)
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) :
    QuasiIso ((bigCrystalDeRhamPresheaf hN).map
      (affineProj hp L (fun _ : Fin (n + 1) ↦ (default : ι)) 0).op) := by
  obtain ⟨e₀, e₀', h1, -, h3, h4⟩ :=
    exists_dpPolynomial_equiv_envelope_const (n := n) (L default) S.prime.out hp t ht
  let W := chartVariables (fun _ : Fin (n + 1) ↦ d)
  let B₀ := (L default).dividedPowerRing
  let D₀ := (envelope (U := fun _ : Fin (n + 1) ↦ U default) (fun _ ↦ L default)).object
  let C := sectionsDPRing S (affineObject hp L default).obj.obj
  let R := sectionsDPRing S
    (affineEnvelopeObject hp L (fun _ : Fin (n + 1) ↦ (default : ι))).obj.obj
  let β : DPMorphism C.dividedPowers B₀.dividedPowers :=
    DPMorphism.mk' (f := (Scheme.ΓSpecIso (CommRingCat.of B₀)).hom.hom)
      (DividedPowerScheme.specSectionsRingIso B₀).inv.isDPMorphism
  let β' : DPMorphism B₀.dividedPowers C.dividedPowers :=
    DPMorphism.mk' (f := (Scheme.ΓSpecIso (CommRingCat.of B₀)).inv.hom)
      (DividedPowerScheme.specSectionsRingIso B₀).hom.isDPMorphism
  let γ := polyRingMap W β
  let γ' := polyRingMap W β'
  let eR : (DeRhamPair.polyRing C W : Type u) →+* (R : Type u) :=
    (Scheme.ΓSpecIso (CommRingCat.of D₀)).inv.hom.comp (e₀.toRingHom.comp γ.toRingHom)
  let e'R : (R : Type u) →+* (DeRhamPair.polyRing C W : Type u) :=
    γ'.toRingHom.comp (e₀'.toRingHom.comp (Scheme.ΓSpecIso (CommRingCat.of D₀)).hom.hom)
  have hfe : ∀ c : C, eR (algebraMap C (setIndexedDividedPowerPolynomialAlgebra C W) c) =
      sectionsDPRingMap (affineProj hp L (fun _ : Fin (n + 1) ↦ (default : ι)) 0).hom.hom c := by
    intro c
    change (Scheme.ΓSpecIso (CommRingCat.of D₀)).inv.hom (e₀ (γ (algebraMap C _ c))) =
      (proj hp (fun _ : Fin (n + 1) ↦ L default) 0).targetHom.hom.appTop.hom c
    refine Eq.trans ?_ (proj_targetHom_appTop hp (fun _ : Fin (n + 1) ↦ L default) 0 c).symm
    exact (congrArg (fun z ↦ (Scheme.ΓSpecIso (CommRingCat.of D₀)).inv.hom (e₀ z))
      (polyRingMap_algebraMap W β c)).trans (congrArg _ (h1 (β c)))
  have he'e : ∀ q, e'R (eR q) = q := fun q ↦ by
    change γ' (e₀' ((Scheme.ΓSpecIso (CommRingCat.of D₀)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of D₀)).inv.hom (e₀ (γ q))))) = q
    refine (congrArg (fun z ↦ γ' (e₀' z))
      (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of D₀)).inv_hom_id _)).trans ?_
    exact (congrArg γ' (h4 (γ q))).trans
      (polyRingMap_polyRingMap W (fun c ↦ ΓSpecIso_inv_hom_apply _ c) q)
  have hee' : ∀ r, eR (e'R r) = r := fun r ↦ by
    change (Scheme.ΓSpecIso (CommRingCat.of D₀)).inv.hom (e₀ (γ (γ' (e₀'
      ((Scheme.ΓSpecIso (CommRingCat.of D₀)).hom.hom r))))) = r
    refine (congrArg (fun z ↦ (Scheme.ΓSpecIso (CommRingCat.of D₀)).inv.hom (e₀ z))
      (polyRingMap_polyRingMap W (fun b ↦
        ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of B₀)).inv_hom_id b) _)).trans ?_
    exact (congrArg (Scheme.ΓSpecIso (CommRingCat.of D₀)).inv.hom (h3 _)).trans
      (ΓSpecIso_inv_hom_apply _ r)
  let e : (DeRhamPair.polyRing C W : Type u) →ₐ[Γ(S.S.scheme, ⊤)] (R : Type u) :=
    { eR with
      commutes' := fun a ↦ by
        change eR (algebraMap Γ(S.S.scheme, ⊤) _ a) = _
        rw [IsScalarTower.algebraMap_apply Γ(S.S.scheme, ⊤) C, hfe]
        exact (sectionsDPRingMap _).commutes a }
  let e' : (R : Type u) →ₐ[Γ(S.S.scheme, ⊤)] (DeRhamPair.polyRing C W : Type u) :=
    { e'R with
      commutes' := fun a ↦ by
        change e'R (algebraMap Γ(S.S.scheme, ⊤) _ a) = _
        rw [← e.commutes a]
        exact he'e _ }
  exact quasiIso_crystalDeRhamPresheaf_map (isQuasicoherentOnSite_restrictSheafOfModules hN)
    (affineProj hp L (fun _ : Fin (n + 1) ↦ (default : ι)) 0) W e hfe e' hee' he'e
    ((DividedPowerScheme.specSectionsRingIso D₀).hom.isDPMorphism.comp _
      (e₀.isDPMorphism.comp _ γ.isDPMorphism))
    (γ'.isDPMorphism.comp _ (e₀'.isDPMorphism.comp _
      (DividedPowerScheme.specSectionsRingIso D₀).inv.isDPMorphism))

include hp in
/-- **The restriction of de Rham complexes along the first projection `D^{n+1} ⟶ D` is a
quasi-isomorphism**, for a smooth lift with étale coordinates. -/
theorem quasiIso_map_interπ_zero (n : ℕ) {d : ℕ} (t : Fin d → (L default).ring)
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) :
    QuasiIso ((bigCrystalDeRhamPresheaf hN).map
      (interπ (affineObject hp L) (fun _ : Fin (n + 1) ↦ (default : ι)) 0).op) := by
  have := quasiIso_map_affineProj_zero hp L hN n t ht
  rw [← interIsoAffineEnvelope_hom_affineProj, op_comp, Functor.map_comp]
  infer_instance

/-! ### The diagonals -/

variable (N) in
/-- The de Rham complex `N(D) ⊗ Ω^•_{B/A,γ}` of the canonical connection on the value of `N` on
the object `D` of the smooth lift. -/
abbrev singleLiftDeRhamComplex : CochainComplex (ModuleCat.{u} Γ(S.S.scheme, ⊤)) ℕ :=
  (bigCrystalDeRhamPresheaf hN).obj (op (affineObject hp L default))

/-- **The diagonal `D ⟶ D^{m+1}`** into the product of `m + 1` copies of the object of the
smooth lift. -/
def singleLiftDiagonal (m : ℕ) :
    affineObject hp L default ⟶
      Stacks.CechSite.FinalCover.inter (affineObject hp L)
        (fun _ : Fin (m + 1) ↦ (default : ι)) :=
  interLift (affineObject hp L) (x := fun _ : Fin (m + 1) ↦ (default : ι)) fun _ ↦ 𝟙 _

/-- The components of the diagonal are identities. -/
theorem singleLiftDiagonal_comp_interπ (m : ℕ) (a : Fin (m + 1)) :
    singleLiftDiagonal hp L m ≫ interπ (affineObject hp L) _ a = 𝟙 _ :=
  interLift_comp_interπ _ _ a

/-- The diagonals are compatible with the reindexing maps of the products. -/
theorem singleLiftDiagonal_comp_interMap {m n : SimplexCategory} (φ : m ⟶ n) :
    singleLiftDiagonal hp L n.len ≫
        interMap (affineObject hp L) (fun _ : Fin (n.len + 1) ↦ (default : ι)) φ.toOrderHom =
      singleLiftDiagonal hp L m.len :=
  inter_hom_ext _ fun a ↦ by
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (singleLiftDiagonal hp L n.len ≫ ·)
      (interMap_comp_interπ _ _ φ.toOrderHom a)).trans ?_
    exact (singleLiftDiagonal_comp_interπ hp L n.len _).trans
      (singleLiftDiagonal_comp_interπ hp L m.len a).symm

variable (N) in
/-- **The morphism of the diagonals `B ⟶ Const(N(D) ⊗ Ω^•_{B/A,γ})`** out of the Čech–de Rham
double complex of the cover by the single object `D`: in bidegree `(a, ⦋m⦌)` it is the
restriction `N(D^{m+1}) ⊗ Ω^a_{D^{m+1}} → N(D) ⊗ Ω^a_{B/A,γ}` along the diagonal
`D ⟶ D^{m+1}`. -/
def diagonalRowHom :
    cechDeRhamDoubleComplex hp L N hN ⟶
      constantCosimplicialCochainComplex.obj (singleLiftDeRhamComplex hp L N hN) :=
  constHom (K := cechDeRhamDoubleComplex hp L N hN) (singleLiftDeRhamComplex hp L N hN)
    (fun a m ↦ cosimplicialObjectπ (affineObject hp L)
        ((bigCrystalDeRhamPresheaf hN) ⋙ HomologicalComplex.eval _ _ a) m
        (fun _ : Fin (m.len + 1) ↦ (default : ι)) ≫
      ((bigCrystalDeRhamPresheaf hN).map (singleLiftDiagonal hp L m.len).op).f a)
    (fun a m n φ ↦ by
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ ((bigCrystalDeRhamPresheaf hN).map
        (singleLiftDiagonal hp L n.len).op).f a) (cosimplicialObject_map_comp_π (affineObject hp L)
          ((bigCrystalDeRhamPresheaf hN) ⋙ HomologicalComplex.eval _ _ a) φ
          (fun _ : Fin (n.len + 1) ↦ (default : ι)))).trans ?_
      refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
      rw [Functor.comp_map, HomologicalComplex.eval_map, ← HomologicalComplex.comp_f,
        ← Functor.map_comp, ← op_comp, singleLiftDiagonal_comp_interMap])
    (fun a a' m ↦ by
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (congrArg (· ≫ ((bigCrystalDeRhamPresheaf hN).map
        (singleLiftDiagonal hp L m.len).op).f a') (cosimplicialFunctor_map_app_comp_π
          (affineObject hp L) (Functor.whiskerLeft (bigCrystalDeRhamPresheaf hN)
            (HomologicalComplex.dNatTrans _ _ a a')) m
          (fun _ : Fin (m.len + 1) ↦ (default : ι)))).symm
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact congrArg (_ ≫ ·)
        (((bigCrystalDeRhamPresheaf hN).map (singleLiftDiagonal hp L m.len).op).comm a a'))

/-- The row `b` of the morphism of the diagonals is the projection of the row onto its single
factor followed by the restriction along the diagonal. -/
theorem rowMap_diagonalRowHom (b : ℕ) :
    rowMap (diagonalRowHom hp L N hN) b =
      rowπ (affineObject hp L) (bigCrystalDeRhamPresheaf hN) b
          (fun _ : Fin (b + 1) ↦ (default : ι)) ≫
        (bigCrystalDeRhamPresheaf hN).map (singleLiftDiagonal hp L b).op :=
  HomologicalComplex.hom_ext _ _ fun _ ↦ rfl

/-- The projection of a row of the double complex onto its single factor is an isomorphism. -/
instance isIso_rowπ (b : ℕ) (x : Fin (b + 1) → ι) :
    IsIso (rowπ (affineObject hp L) (bigCrystalDeRhamPresheaf hN) b x) := by
  obtain rfl : x = default := Subsingleton.elim _ _
  rw [← rowIsoProduct_hom_comp_π, ← productUniqueIso_hom]
  infer_instance

include hp in
/-- **The restriction along the diagonal `D ⟶ D^{n+1}` is a quasi-isomorphism**: it is a left
inverse of the restriction along the first projection, which is one
(`quasiIso_map_interπ_zero`). -/
theorem quasiIso_map_singleLiftDiagonal (b : ℕ) {d : ℕ} (t : Fin d → (L default).ring)
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) :
    QuasiIso ((bigCrystalDeRhamPresheaf hN).map (singleLiftDiagonal hp L b).op) := by
  have := quasiIso_map_interπ_zero hp L hN b t ht
  have : QuasiIso ((bigCrystalDeRhamPresheaf hN).map
        (interπ (affineObject hp L) (fun _ : Fin (b + 1) ↦ (default : ι)) 0).op ≫
      (bigCrystalDeRhamPresheaf hN).map (singleLiftDiagonal hp L b).op) := by
    rw [← Functor.map_comp, ← op_comp, singleLiftDiagonal_comp_interπ, op_id,
      CategoryTheory.Functor.map_id]
    infer_instance
  exact quasiIso_of_comp_left ((bigCrystalDeRhamPresheaf hN).map
    (interπ (affineObject hp L) (fun _ : Fin (b + 1) ↦ (default : ι)) 0).op) _

include hp in
/-- **The diagonals are a quasi-isomorphism on every row** of the Čech–de Rham double complex of
a smooth lift with étale coordinates: the row `b` is `N(D^{b+1}) ⊗ Ω^•_{D^{b+1}}` and the
restriction along the diagonal `D ⟶ D^{b+1}` is a quasi-isomorphism. -/
theorem quasiIso_rowMap_diagonalRowHom {d : ℕ} (t : Fin d → (L default).ring)
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) (b : ℕ) :
    QuasiIso (rowMap (diagonalRowHom hp L N hN) b) := by
  have := quasiIso_map_singleLiftDiagonal hp L hN b t ht
  have : IsIso (rowπ (affineObject hp L) (bigCrystalDeRhamPresheaf hN) b
      (fun _ : Fin (b + 1) ↦ (default : ι))) := isIso_rowπ hp L hN b _
  have : QuasiIso (rowπ (affineObject hp L) (bigCrystalDeRhamPresheaf hN) b
      (fun _ : Fin (b + 1) ↦ (default : ι))) := quasiIso_of_isIso _
  have h := quasiIso_comp (rowπ (affineObject hp L) (bigCrystalDeRhamPresheaf hN) b
      (fun _ : Fin (b + 1) ↦ (default : ι)))
    ((bigCrystalDeRhamPresheaf hN).map (singleLiftDiagonal hp L b).op)
  rw [rowMap_diagonalRowHom]
  exact h

/-- **The Čech cohomology of a quasi-coherent module along a single smooth lift with étale
coordinates is its de Rham cohomology**: if the Moore complexes of the columns `a > 0` of the
Čech–de Rham double complex are acyclic, the diagonals identify the cohomology
`H^j(Č(D, N))` of the Čech complex of `N` along the cover by the single object `D = (U, Spec B,
γ_B)` with the cohomology `H^j(N(D) ⊗ Ω^•_{B/A,γ})` of the de Rham complex of the canonical
connection, as `A`-modules. -/
def singleLiftHomologyIso
    (hcol : ∀ n : ℕ, 0 < n → ∀ j : ℕ, IsZero (((alternatingCofaceMapComplex _).obj
      ((cechDeRhamDoubleComplex hp L N hN).X n)).homology j))
    {d : ℕ} (t : Fin d → (L default).ring)
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) (j : ℕ) :
    ((alternatingCofaceMapComplex _).obj ((cechDeRhamDoubleComplex hp L N hN).X 0)).homology j ≅
      (singleLiftDeRhamComplex hp L N hN).homology j :=
  columnZeroHomologyIsoOfRowComparison _ _ hcol (diagonalRowHom hp L N hN)
    (quasiIso_rowMap_diagonalRowHom hp L hN t ht) j

/-! ### The de Rham complex vanishes above the number of coordinates -/

omit [S.X.IsSeparated] in
include hp in
/-- The images `t_i ∈ Γ(Spec B, ⊤)` of étale coordinates `t_i ∈ B` of a smooth lift are étale
coordinates of `Γ(Spec B, ⊤)` over `A = Γ(S, 𝒪_S)`. -/
theorem etale_aeval_sections {d : ℕ} (t : Fin d → (L default).ring)
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) :
    (MvPolynomial.aeval (R := Γ(S.S.scheme, ⊤))
      (S₁ := sectionsDPRing S (affineObject hp L default).obj.obj)
      fun i ↦ (Scheme.ΓSpecIso (CommRingCat.of (L default).dividedPowerRing)).inv.hom
        (t i)).toRingHom.Etale := by
  have hcomm : ∀ a : Γ(S.S.scheme, ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of (L default).dividedPowerRing)).inv.hom
          (algebraMap (baseSectionsRing S) (L default).ring a) =
        algebraMap Γ(S.S.scheme, ⊤) (sectionsDPRing S (affineObject hp L default).obj.obj) a := by
    intro a
    refine (toBase_appTop_object hp (fun _ : Fin 1 ↦ L default) 0 a).symm.trans ?_
    change _ = (crysBaseAppLE S (affineObject hp L default).obj.obj).hom a
    rw [crysBaseAppLE, baseAppLE, appLE_top_top]
    rfl
  have heq : (MvPolynomial.aeval (R := Γ(S.S.scheme, ⊤))
      (S₁ := sectionsDPRing S (affineObject hp L default).obj.obj)
      fun i ↦ (Scheme.ΓSpecIso (CommRingCat.of (L default).dividedPowerRing)).inv.hom
        (t i)).toRingHom =
      (Scheme.ΓSpecIso (CommRingCat.of (L default).dividedPowerRing)).inv.hom.comp
        (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
    · exact (MvPolynomial.aeval_C (R := Γ(S.S.scheme, ⊤))
        (S₁ := sectionsDPRing S (affineObject hp L default).obj.obj) _ a).trans
        ((hcomm a).symm.trans (congrArg
          (Scheme.ΓSpecIso (CommRingCat.of (L default).dividedPowerRing)).inv.hom
          (MvPolynomial.aeval_C (R := baseSectionsRing S) t a).symm))
    · exact (MvPolynomial.aeval_X (R := Γ(S.S.scheme, ⊤))
        (S₁ := sectionsDPRing S (affineObject hp L default).obj.obj) _ i).trans
        (congrArg (Scheme.ΓSpecIso (CommRingCat.of (L default).dividedPowerRing)).inv.hom
          (MvPolynomial.aeval_X (R := baseSectionsRing S) t i).symm)
  rw [heq]
  exact RingHom.Etale.stableUnderComposition _ _ ht
    (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (L default).dividedPowerRing)).inv))

omit [S.X.IsSeparated] in
include hp in
/-- **The divided power differentials of a smooth lift with étale coordinates are spanned by the
differentials of the coordinates**: `Ω¹_{B/A,γ}` is a quotient of `Ω_{B/A}`, which is spanned by
the `dt_i` (`span_range_kaehlerD_of_etale`). -/
theorem span_range_dividedPowerDifferential_sections {d : ℕ} (t : Fin d → (L default).ring)
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) :
    Submodule.span (sectionsDPRing S (affineObject hp L default).obj.obj)
      (Set.range fun i ↦ dividedPowerDifferential (A := Γ(S.S.scheme, ⊤))
        (sectionsDPRing S (affineObject hp L default).obj.obj).dividedPowers
        ((Scheme.ΓSpecIso (CommRingCat.of (L default).dividedPowerRing)).inv.hom (t i))) = ⊤ := by
  have h := congrArg (Submodule.map (dividedPowerDifferentialRelations (A := Γ(S.S.scheme, ⊤))
    (sectionsDPRing S (affineObject hp L default).obj.obj).dividedPowers).mkQ)
    (span_range_kaehlerD_of_etale (A := Γ(S.S.scheme, ⊤))
      (B := sectionsDPRing S (affineObject hp L default).obj.obj) _
      (etale_aeval_sections hp L t ht))
  have h' : Submodule.span (sectionsDPRing S (affineObject hp L default).obj.obj)
      (Set.range fun i ↦ (dividedPowerDifferentialRelations (A := Γ(S.S.scheme, ⊤))
        (sectionsDPRing S (affineObject hp L default).obj.obj).dividedPowers).mkQ
        (KaehlerDifferential.D Γ(S.S.scheme, ⊤)
          (sectionsDPRing S (affineObject hp L default).obj.obj)
          ((Scheme.ΓSpecIso (CommRingCat.of (L default).dividedPowerRing)).inv.hom
            (t i)))) = ⊤ := by
    simpa only [LinearMap.map_span, ← Set.range_comp, Function.comp_def,
      Submodule.map_top, Submodule.range_mkQ] using h
  exact h'

omit [S.X.IsSeparated] in
include hp in
/-- **The de Rham complex `N(D) ⊗ Ω^•_{B/A,γ}` of a smooth lift with `d` étale coordinates
vanishes in degrees `j > d`**, the forms of degree `j > d` being zero
(`exteriorPower_subsingleton_of_span`). -/
theorem isZero_singleLiftDeRhamComplex_X {d : ℕ} (t : Fin d → (L default).ring)
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) {j : ℕ}
    (hj : d < j) : IsZero ((singleLiftDeRhamComplex hp L N hN).X j) := by
  have : Subsingleton (⋀[sectionsDPRing S (affineObject hp L default).obj.obj]^j
      (dividedPowerDifferentials (A := Γ(S.S.scheme, ⊤))
        (sectionsDPRing S (affineObject hp L default).obj.obj).dividedPowers)) :=
    exteriorPower_subsingleton_of_span _ (span_range_dividedPowerDifferential_sections hp L t ht) hj
  have : Subsingleton ((singleLiftDeRhamComplex hp L N hN).X j) :=
    inferInstanceAs (Subsingleton (_ ⊗[sectionsDPRing S (affineObject hp L default).obj.obj] _))
  exact ModuleCat.isZero_of_subsingleton _

omit [S.X.IsSeparated] in
include hp in
/-- **The de Rham cohomology `H^j(N(D) ⊗ Ω^•_{B/A,γ})` of a smooth lift with `d` étale
coordinates vanishes for `j > d`.** -/
theorem isZero_homology_singleLiftDeRhamComplex {d : ℕ} (t : Fin d → (L default).ring)
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) {j : ℕ}
    (hj : d < j) : IsZero ((singleLiftDeRhamComplex hp L N hN).homology j) :=
  ShortComplex.isZero_homology_of_isZero_X₂ (_ : ShortComplex _)
    (isZero_singleLiftDeRhamComplex_X hp L hN t ht hj)

/-! ### Crystalline cohomology along a single smooth lift -/

include hp in
/-- **The Čech cohomology `H^j(Č(D, N))` of a quasi-coherent module along a single smooth lift
with étale coordinates is the de Rham cohomology `H^j(N(D) ⊗ Ω^•_{B/A,γ})`**, as `A`-modules:
`singleLiftHomologyIso` with the acyclicity of the columns `a > 0`
(`isZero_homology_cechDeRhamDoubleComplex_X`, [Stacks, Tag 07LA]). -/
def cechSingleLiftHomologyIso {d : ℕ} (t : Fin d → (L default).ring)
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) (j : ℕ) :
    ((alternatingCofaceMapComplex _).obj ((cechDeRhamDoubleComplex hp L N hN).X 0)).homology j ≅
      (singleLiftDeRhamComplex hp L N hN).homology j :=
  singleLiftHomologyIso hp L hN
    (fun _ ha j ↦ isZero_homology_cechDeRhamDoubleComplex_X hp L hN ha j) t ht j

section Main

open SmallSite

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe v₂ v₃

variable (hU : ∀ x, ∃ i, x ∈ U i)
  [HasDerivedCategory.{v₂} (BigModuleSheaf S)]
  [HasDerivedCategory.{v₃} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]

/-- **The crystalline cohomology of a quasi-coherent module is the de Rham cohomology of a smooth
lift with étale coordinates**: if `X` is covered by the affine open `U` with smooth lift
`Y = Spec B` carrying étale coordinates `t_1, …, t_d`, then for `N` quasi-coherent on `CRIS(X/S)`,
`H^j(CRIS(X/S), N) ≅ H^j(N(D) ⊗ Ω^•_{B/A,γ})` as `A`-modules, the right-hand side lifted to the
universe `u + 1`: the Čech–de Rham double complex computes crystalline cohomology
(`cechDeRhamHomologyIso`), its total complex has the cohomology of column zero
(`cechHomologyIsoTotal`) and that is `cechSingleLiftHomologyIso`. -/
def crystallineHomologyIsoSingleLift {d : ℕ} (t : Fin d → (L default).ring)
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) (j : ℕ) :
    (DerivedCategory.Plus.homologyFunctor _ (j : ℤ)).obj
        ((derivedBigModuleGlobalSections S).obj ((bigModuleULift S).obj N)) ≅
      (ModuleCat.uliftFunctor.{u + 1, u} Γ(S.S.scheme, ⊤)).obj
        ((singleLiftDeRhamComplex hp L N hN).homology j) :=
  (cechDeRhamHomologyIso hp L hN hU j).symm ≪≫
    (ModuleCat.uliftFunctor.{u + 1, u} Γ(S.S.scheme, ⊤)).mapIso
      (cechHomologyIsoTotal hp L hN j ≪≫ cechSingleLiftHomologyIso hp L hN t ht j)

include hp hN hU in
/-- **The crystalline cohomology `H^j(CRIS(X/S), N)` of a quasi-coherent module vanishes for
`j > d`** when `X` is covered by one affine open with a smooth lift carrying `d` étale
coordinates: it is the de Rham cohomology of the lift, whose forms of degree `j > d` vanish. -/
theorem isZero_crystallineHomology_singleLift {d : ℕ} (t : Fin d → (L default).ring)
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) {j : ℕ}
    (hj : d < j) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ (j : ℤ)).obj
      ((derivedBigModuleGlobalSections S).obj ((bigModuleULift S).obj N))) :=
  IsZero.of_iso (Functor.map_isZero _ (isZero_homology_singleLiftDeRhamComplex hp L hN t ht hj))
    (crystallineHomologyIsoSingleLift hp L hN hU t ht j)

/-- **The crystalline cohomology of a quasi-coherent module on an affine `X` with a smooth lift
carrying étale coordinates**: if `X` is affine and `Y = Spec B` is a smooth lift of `X` over `A`
with étale coordinates `t_1, …, t_d`, then `H^j(CRIS(X/S), N) ≅ H^j(N(D) ⊗ Ω^•_{B/A,γ})` as
`A`-modules, `D = (X, Y, γ_B)`, the right-hand side lifted to the universe `u + 1`. -/
def crystallineHomologyIsoOfIsAffine [IsAffine S.X] (L₀ : SmoothLift S (⊤ : S.X.Opens).ι)
    {d : ℕ} (t : Fin d → L₀.ring)
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) (j : ℕ) :
    haveI : IsAffine (⊤ : S.X.Opens) := isAffineOpen_top S.X
    (DerivedCategory.Plus.homologyFunctor _ (j : ℤ)).obj
        ((derivedBigModuleGlobalSections S).obj ((bigModuleULift S).obj N)) ≅
      (ModuleCat.uliftFunctor.{u + 1, u} Γ(S.S.scheme, ⊤)).obj
        ((singleLiftDeRhamComplex hp (U := fun _ : Unit ↦ ⊤) (fun _ ↦ L₀) N hN).homology j) :=
  haveI : IsAffine (⊤ : S.X.Opens) := isAffineOpen_top S.X
  crystallineHomologyIsoSingleLift hp (U := fun _ : Unit ↦ ⊤) (fun _ ↦ L₀) hN
    (fun _ ↦ ⟨(), trivial⟩) t ht j

include hp hN in
/-- **The crystalline cohomology `H^j(CRIS(X/S), N)` of a quasi-coherent module on an affine `X`
with a smooth lift carrying `d` étale coordinates vanishes for `j > d`.** -/
theorem isZero_crystallineHomology_of_isAffine [IsAffine S.X]
    (L₀ : SmoothLift S (⊤ : S.X.Opens).ι) {d : ℕ} (t : Fin d → L₀.ring)
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) {j : ℕ}
    (hj : d < j) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ (j : ℤ)).obj
      ((derivedBigModuleGlobalSections S).obj ((bigModuleULift S).obj N))) :=
  have : IsAffine (⊤ : S.X.Opens) := isAffineOpen_top S.X
  isZero_crystallineHomology_singleLift hp (U := fun _ : Unit ↦ ⊤) (fun _ ↦ L₀) hN
    (fun _ ↦ ⟨(), trivial⟩) t ht hj

end Main

end SingleLift

end Crystalline.GlobalCrystallineSituation.CechEnvelope
