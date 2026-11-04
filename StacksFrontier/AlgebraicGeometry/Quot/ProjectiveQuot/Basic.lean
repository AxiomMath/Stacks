module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomial
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.FreeSheafTwistAcyclic

/-!
# Quotients of `𝒪^{⊕ r}` on `ℙⁿ_T` with a given Hilbert polynomial

Stacks 0DPA is about the algebraic space `Quot^P_{𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ}`, whose value on a scheme `T`
is the set of quotients `𝒪^{⊕ r}_{ℙⁿ_T} ⟶ 𝒬` which are of finite presentation and flat over
`T` (Stacks 09TR) and whose fibre over every point `t ∈ T` has Hilbert polynomial `P`
(Stacks 0DNF, 0DP6). Since `ℙⁿ_T` is a scheme, these quotients can be read on the Zariski site
of `ℙⁿ_T`; this file records them there, as the scheme-level description of `Quot^P(T)` that
the proof of Stacks 0DPA manipulates.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuot.freeModule n r T`: the free module `𝒪^{⊕ r}` on `ℙⁿ_T`.
* `AlgebraicGeometry.ProjectiveQuot.quotient K`: the quotient `𝒪^{⊕ r} / K` of a submodule `K`.
* `AlgebraicGeometry.ProjectiveQuot.fibre t F`: the restriction of a module on `ℙⁿ_T` to the
  fibre `ℙⁿ_{κ(t)}` over a point `t ∈ T`.
* `AlgebraicGeometry.ProjectiveQuot.HasFibreHilbertPolynomial P F`: every fibre of `F` is
  coherent with Hilbert polynomial `P`.
* `AlgebraicGeometry.ProjectiveQuot.families n r T`: the submodules `K ⊆ 𝒪^{⊕ r}` on `ℙⁿ_T` whose
  quotient is of finite presentation and flat over `T`, that is `Quot_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)` read on
  kernels.
* `AlgebraicGeometry.ProjectiveQuot.hilbertFamilies n r P T`: those whose quotient has fibre
  Hilbert polynomial `P`, that is `Quot^P_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)`.
* `AlgebraicGeometry.ProjectiveQuot.freeModulePullbackIso`: the inverse image of `𝒪^{⊕ r}` along
  `ℙⁿ_{T'} ⟶ ℙⁿ_T` is `𝒪^{⊕ r}`.
* `AlgebraicGeometry.ProjectiveQuot.baseChange g K`: the pullback of a submodule along a morphism
  `g : T' ⟶ T`, the kernel of the pulled-back quotient `𝒪^{⊕ r} ≅ g^* 𝒪^{⊕ r} ⟶ g^*(𝒪^{⊕ r} / K)`.

## Implementation notes

**Quotients are recorded by their kernels**, as in `AlgebraicGeometry.Space.QuotSituation` of
Stacks 09TR, so two quotients with the same kernel are identified.

**Quasi-coherence and proper support are not listed.** A module of finite presentation on a
scheme is quasi-coherent, and every closed subset of `ℙⁿ_T` is proper over `T`, so the
conditions of Stacks 09TR reduce to finite presentation and flatness here.

**The fibre condition is existential in coherence.** `AlgebraicGeometry.hilbertPolynomial` takes
the coherence of its argument as an instance; the fibre of a module of finite presentation over a
point is coherent on the Noetherian scheme `ℙⁿ_{κ(t)}`, and the condition asks for that coherence
together with the value of the Hilbert polynomial, so it is never vacuous.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveQuot

variable (n r : ℕ)

/-- The free module `𝒪^{⊕ r}` on projective space `ℙⁿ_T` over a scheme `T`. -/
abbrev freeModule (T : Scheme.{u}) : (projectiveSpaceOver n T).Modules :=
  ∐ fun _ : Fin r => Scheme.unitModule (projectiveSpaceOver n T)

/-- Over a ring, `AlgebraicGeometry.ProjectiveQuot.freeModule` is the free module
`AlgebraicGeometry.freeModules` of the field step. -/
theorem freeModule_spec (R : Type u) [CommRing R] :
    freeModule n r (Spec (.of R)) = freeModules R n r :=
  rfl

variable {n r}

/-- The quotient `𝒪^{⊕ r} / K` of the free module by a submodule. -/
abbrev quotient {T : Scheme.{u}} (K : Subobject (freeModule n r T)) :
    (projectiveSpaceOver n T).Modules :=
  cokernel K.arrow

/-- The projection `𝒪^{⊕ r} ⟶ 𝒪^{⊕ r} / K`. -/
abbrev quotientπ {T : Scheme.{u}} (K : Subobject (freeModule n r T)) :
    freeModule n r T ⟶ quotient K :=
  cokernel.π K.arrow

variable (n) in
/-- The fibre `ℙⁿ_{κ(t)} ⟶ ℙⁿ_T` of projective space over a point `t` of the base. -/
abbrev fibreMap {T : Scheme.{u}} (t : T) :
    projectiveSpaceOverRing n (.of (T.residueField t)) ⟶ projectiveSpaceOver n T :=
  projectiveSpaceOverMap n (T.fromSpecResidueField t)

/-- The restriction of a module on `ℙⁿ_T` to the fibre `ℙⁿ_{κ(t)}` over a point `t ∈ T`. -/
abbrev fibre {T : Scheme.{u}} (t : T) (F : (projectiveSpaceOver n T).Modules) :
    (projectiveSpaceOverRing n (.of (T.residueField t))).Modules :=
  (Scheme.Modules.pullback (fibreMap n t)).obj F

/-- Every fibre of `F` is coherent with Hilbert polynomial `P`: for each point `t ∈ T`,
`χ(ℙⁿ_{κ(t)}, F_t(d)) = P(d)` for every `d ∈ ℤ` (the membership condition of Stacks 0DNF). -/
def HasFibreHilbertPolynomial (P : Polynomial ℚ) {T : Scheme.{u}}
    (F : (projectiveSpaceOver n T).Modules) : Prop :=
  ∀ t : T, ∃ _ : (fibre t F).IsCoherent, ∀ d : ℤ,
    (hilbertPolynomial (T.residueField t) n (fibre t F) d : ℚ) = P.eval (d : ℚ)

/-- A module on `ℙⁿ_T` which is of finite presentation and flat over `T`. -/
def IsFlatFamily {T : Scheme.{u}} (F : (projectiveSpaceOver n T).Modules) : Prop :=
  F.IsFinitePresentation ∧ IsFlatOver (projectiveSpaceOver n T ↘ T).toLRSHom.toShHom F

variable (n r) in
/-- `Quot_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)` read on kernels: the submodules `K ⊆ 𝒪^{⊕ r}` on `ℙⁿ_T` whose
quotient is of finite presentation and flat over `T` (Stacks 09TR). -/
def families (T : Scheme.{u}) : Set (Subobject (freeModule n r T)) :=
  {K | IsFlatFamily (quotient K)}

variable (n r) in
/-- `Quot^P_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)` read on kernels: the members of
`AlgebraicGeometry.ProjectiveQuot.families` whose quotient has Hilbert polynomial `P` on every
fibre (Stacks 0DNF). -/
def hilbertFamilies (P : Polynomial ℚ) (T : Scheme.{u}) : Set (Subobject (freeModule n r T)) :=
  {K | K ∈ families n r T ∧ HasFibreHilbertPolynomial P (quotient K)}

/-- A submodule `K ⊆ 𝒪^{⊕ r}` lies in `hilbertFamilies n r P T` if and only if its quotient is of
finite presentation and flat over `T` and has Hilbert polynomial `P` on every fibre. -/
theorem mem_hilbertFamilies_iff {P : Polynomial ℚ} {T : Scheme.{u}}
    (K : Subobject (freeModule n r T)) :
    K ∈ hilbertFamilies n r P T ↔
      IsFlatFamily (quotient K) ∧ HasFibreHilbertPolynomial P (quotient K) :=
  Iff.rfl

/-! ### Base change -/

variable (n r) in
/-- The inverse image of `𝒪^{⊕ r}` along `ℙⁿ_{T'} ⟶ ℙⁿ_T` is `𝒪^{⊕ r}`. -/
def freeModulePullbackIso {T' T : Scheme.{u}} (g : T' ⟶ T) :
    (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj (freeModule n r T) ≅
      freeModule n r T' :=
  PreservesCoproduct.iso (Scheme.Modules.pullback (projectiveSpaceOverMap n g)) _ ≪≫
    Sigma.mapIso fun _ => Scheme.Modules.pullbackUnitIso (projectiveSpaceOverMap n g)

/-- The pullback of the quotient map `𝒪^{⊕ r} ⟶ 𝒪^{⊕ r} / K` along `g : T' ⟶ T`, read on the free
module `𝒪^{⊕ r}` of `ℙⁿ_{T'}`. -/
def baseChangeQuotientMap {T' T : Scheme.{u}} (g : T' ⟶ T) (K : Subobject (freeModule n r T)) :
    freeModule n r T' ⟶ (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj (quotient K) :=
  (freeModulePullbackIso n r g).inv ≫
    (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map (quotientπ K)

/-- The pullback `𝒪^{⊕ r} ⟶ g^*(𝒪^{⊕ r} / K)` of the quotient map is an epimorphism. -/
instance {T' T : Scheme.{u}} (g : T' ⟶ T) (K : Subobject (freeModule n r T)) :
    Epi (baseChangeQuotientMap g K) := by
  unfold baseChangeQuotientMap
  infer_instance

/-- The pullback of a submodule `K ⊆ 𝒪^{⊕ r}` on `ℙⁿ_T` along `g : T' ⟶ T`: the kernel of the
pulled-back quotient `𝒪^{⊕ r} ≅ g^* 𝒪^{⊕ r} ⟶ g^*(𝒪^{⊕ r} / K)`, which is the base change of the
quotient `𝒪^{⊕ r} ⟶ 𝒪^{⊕ r} / K` in the sense of Stacks 09TR. -/
def baseChange {T' T : Scheme.{u}} (g : T' ⟶ T) (K : Subobject (freeModule n r T)) :
    Subobject (freeModule n r T') :=
  kernelSubobject (baseChangeQuotientMap g K)

end AlgebraicGeometry.ProjectiveQuot

end
