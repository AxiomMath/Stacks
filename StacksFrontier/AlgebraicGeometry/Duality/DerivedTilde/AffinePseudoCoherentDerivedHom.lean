module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedHom
public import StacksFrontier.AlgebraicGeometry.InternalHomTilde.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.AffineInternalHom
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.BoundedAboveHomComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexOfAStrictlyPerfectComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree
public import StacksFrontier.Homology.HomComplex.ProjectiveRHom
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.AlgebraicGeometry.ModuleSpecGammaAdditive
import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom of associated complexes on an affine scheme, pseudo-coherent source

Let `R` be a commutative ring and `X = Spec R`. Sheafification `M ↦ M̃` is exact, so it induces
a functor `D(R) ⥤ D(𝒪_X)` on derived categories. This file proves part (3)(a) of
[Stacks, Tag 0A6H]: for `K` pseudo-coherent and `L` bounded below there is a canonical
isomorphism

`R𝓗om_{𝒪_X}(K̃, L̃)  ≅  (RHom_R(K, L))~`

in `D(𝒪_X)`, natural in `K` and in `L`.

The proof follows the source. `K` is replaced by a bounded-above representative `E` with finite
free terms, `L` by a bounded-below K-injective representative `J`. On those representatives both
sides are computed by ordinary Hom complexes: the sheaf side by [Stacks, Tag 08I5]
(`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_of_boundedAbove`, which
applies because `Ẽ` is bounded above with finite-free-summand terms and `J̃` is bounded below),
the module side by [Stacks, Tag 0A66] (`StacksDraft.DerivedHom.projectiveHomComparison`, which
applies because `E` is bounded above with projective terms). What remains is a comparison of
those two ordinary complexes, and that is the affine internal-Hom isomorphism of
[Stacks, Tag 01I8] assembled over all degrees.

## Main definitions

* `AlgebraicGeometry.affinePseudoCoherentDerivedSheafHomIso` is the comparison isomorphism of
  [Stacks, Tag 0A6H] (3)(a).

## Main results

* `AlgebraicGeometry.affinePseudoCoherentDerivedSheafHomIso_natural_left` and
  `AlgebraicGeometry.affinePseudoCoherentDerivedSheafHomIso_natural_right` state that the
  comparison is contravariantly natural in the pseudo-coherent argument and covariantly natural
  in the bounded-below argument.

## Implementation notes

The source states (3)(a) as an equality of objects of `D(𝒪_X)`. An equality of objects is not
available in a formalisation where the two sides are built differently, so it is expressed here
as an isomorphism; what makes that faithful rather than weaker is the pair of naturality
statements together with the normalisation on representatives, since an isomorphism natural in
both variables and prescribed on representatives is unique.

The degreewise comparison is normalised, and that normalisation is what the proof of the
complex-level statement rests on. In degree `n` the term of `SheafHom(Ẽ, J̃)` is the product,
over `q : ℤ`, of the internal Hom sheaves `SheafHom(Ẽ^{-q}, J̃^{n-q})`
(`AlgebraicGeometry.RingedSite.homDegreeIsLimit`, which needs no hypothesis); the two-sided
bound makes all but finitely many factors vanish, so that term is the sheafification of its
module of global sections. Those global sections are identified with degree-`n` module Hom
cochains by reading off each coordinate with
`AlgebraicGeometry.RingedSite.homDegreeProjection` and applying the global-sections form
`AlgebraicGeometry.sheafHomTildeΓLinearEquiv` of [Stacks, Tag 01I8] to it; the resulting
isomorphism sends the canonical global section attached to a cochain `α` to the sheaf Hom
cochain with components `α.v p q`, sheafified. That identity is what fixes the comparison and
excludes a global sign, and it is also what makes the compatibility with the Hom-complex
differential and with the induced maps in both variables provable: both are checked on global
sections, where they become the corresponding identities for module Hom cochains.

Two spellings of the category of `𝒪_{Spec R}`-modules meet in this statement. Mathlib's
`AlgebraicGeometry.tilde.functor` lands in `AlgebraicGeometry.Scheme.Modules`, whereas the
internal Hom complex and the derived internal Hom of a ringed space are stated for
`Stacks.SheafOfModules.StructureSheafModules`. The two agree, but not as terms, so
sheafification is retyped once through the private abbreviation `tildeH`, and every expression
of the construction then lives in one category with one instance. That is what lets the file be
written with no transparency option anywhere. The same reason explains the private abbreviations
`tildeHC` and `tildeD`; the ringed site itself is `AlgebraicGeometry.specSite`, taken from
`AffineDerivedHom`.

The `08I5` representation statement is taken at the derived internal Hom
`Stacks.SheafOfModules.derivedInternalHom (Spec R).sheaf`, whose `hom` field is the bifunctor
`Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf` named in the statement, so the two sides
speak about one and the same derived internal Hom. Its naturality in both variables
(`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality`) holds for arbitrary
complexes — no boundedness, no finite free terms — being just the naturality of the three
factors of `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison`.

The module side is `StacksDraft.DerivedHom.derivedHomAdjunction`, the derived Hom of
`R`-modules that `StacksDraft.DerivedHom.projectiveHomComparison` is stated against, so that the
two clauses of [Stacks, Tag 0A6H] speak about one derived Hom of modules.

## References

* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 08I5](https://stacks.math.columbia.edu/tag/08I5)
* [Stacks Project, Tag 0A66](https://stacks.math.columbia.edu/tag/0A66)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CochainComplex.HomComplex

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

universe u

namespace AlgebraicGeometry

/-! ### Retyping sheafification -/

/-- The category of `𝒪_{Spec R}`-modules in the spelling the internal Hom complex is stated
for. -/
private abbrev SpecHomModules (R : CommRingCat.{u}) :=
  Stacks.SheafOfModules.StructureSheafModules.{u} (Spec R).sheaf

/-- Sheafification, read as a functor into `SpecHomModules R`. -/
private abbrev tildeH (R : CommRingCat.{u}) : ModuleCat.{u} R ⥤ SpecHomModules R :=
  tilde.functor R

private instance tildeH_additive (R : CommRingCat.{u}) : (tildeH R).Additive :=
  inferInstanceAs (tilde.functor R).Additive

private instance tildeH_preservesFiniteLimits (R : CommRingCat.{u}) :
    PreservesFiniteLimits (tildeH R) :=
  AlgebraicGeometry.tilde.preservesFiniteLimits R

private instance tildeH_preservesFiniteColimits (R : CommRingCat.{u}) :
    PreservesFiniteColimits (tildeH R) :=
  Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor R

/-- Sheafification of complexes, read in `SpecHomModules R`. -/
private abbrev tildeHC (R : CommRingCat.{u}) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (SpecHomModules R) ℤ :=
  (tildeH R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Sheafification followed by restriction to the whole of `Spec R`, read on the ringed site.
It is fully faithful and additive, so module Hom cochains are the same thing as sheaf Hom
cochains over the whole space. -/
private abbrev tildeOverTop (R : CommRingCat.{u}) :=
  tildeH R ⋙ SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (specSite R).O)
    (⊤ : (specSite R).C)

private noncomputable local instance tildeOverTop_additive (R : CommRingCat.{u}) :
    (tildeOverTop R).Additive :=
  ⟨by intros; exact tildeOverTop_map_add R _ _⟩

/-- `tildeOverTop` is fully faithful: this is `AlgebraicGeometry.fullyFaithfulTildeOverTop`,
retyped at the ringed-site spelling of the structure sheaf. -/
private def fullyFaithfulTildeOverTopSite (R : CommRingCat.{u}) :
    (tildeOverTop R).FullyFaithful :=
  fullyFaithfulTildeOverTop R

/-! ### Terms of a sheafified finite free complex are finite free summands -/

/-- The sheaf associated to a finite free module is a direct summand of a finite free
`𝒪_{Spec R}`-module. -/
private lemma tildeObj_isFiniteFreeSummand (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    (hM : StacksDraft.PseudoCoherence.IsFiniteFree M) :
    RingedSite.IsFiniteFreeSummand (specSite R) ((tildeH R).obj M) := by
  classical
  have : Module.Finite R M := hM.1
  have : Module.Free R M := hM.2
  let _ : Fintype (Module.Free.ChooseBasisIndex R M) :=
    Module.Free.ChooseBasisIndex.fintype R M
  set I := Module.Free.ChooseBasisIndex R M with hI
  set n := Fintype.card I with hn
  let b : Module.Basis (ULift.{u} (Fin n)) R M :=
    (Module.Free.chooseBasis R M).reindex ((Fintype.equivFin I).trans Equiv.ulift.symm)
  let e : (tildeH R).obj M ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n)) :=
    (tilde.functor R).mapIso b.repr.toModuleIso ≪≫ tildeFinsupp (R := R) (ULift.{u} (Fin n))
  exact RingedSite.isFiniteFreeSummand_of_retract_free (specSite R)
    (ULift.{u} (Fin n)) (Retract.ofIso e)

/-- A finite free module is projective. -/
private lemma projective_of_isFiniteFree {R : CommRingCat.{u}} {M : ModuleCat.{u} R}
    (hM : StacksDraft.PseudoCoherence.IsFiniteFree M) : Projective M := by
  have := hM.2
  infer_instance

/-- A sheafified complex is zero in the degrees above a bound for the source. -/
private lemma tildeHC_isZero_of_isStrictlyLE (R : CommRingCat.{u})
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) (hE : E.IsStrictlyLE b) :
    ∀ i : ℤ, b < i → IsZero (((tildeHC R).obj E).X i) := by
  intro i hi
  exact (tildeH R).map_isZero (E.isZero_of_isStrictlyLE b i hi)

/-- A sheafified complex is zero in the degrees below a bound for the source. -/
private lemma tildeHC_isZero_of_isStrictlyGE (R : CommRingCat.{u})
    (J : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) (hJ : J.IsStrictlyGE a) :
    ∀ i : ℤ, i < a → IsZero (((tildeHC R).obj J).X i) := by
  intro i hi
  exact (tildeH R).map_isZero (J.isZero_of_isStrictlyGE a i hi)

/-! ### Each term of the internal Hom complex is an associated sheaf -/

/-- A module of homomorphisms with a zero source or a zero target is zero. -/
private lemma moduleHomObject_isZero (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)
    (h : IsZero M ∨ IsZero N) : IsZero (ModuleCat.of R (M ⟶ N)) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun f g => ?_⟩
  rcases h with hM | hN
  · exact hM.eq_of_src f g
  · exact hN.eq_of_tgt f g

/-- A product of objects supported on a finite set is the product over that set. -/
private noncomputable def piIsoFiniteSupport {C : Type*} [Category C]
    [HasProducts C] [HasZeroMorphisms C] {ι : Type*}
    (A : ι → C) (s : Finset ι) (hzero : ∀ i, i ∉ s → IsZero (A i)) :
    (∏ᶜ A) ≅ ∏ᶜ (fun i : {i // i ∈ s} => A i) := by
  classical
  refine ⟨Pi.lift (fun i => Pi.π A i.1),
    Pi.lift (fun i => if hi : i ∈ s then
      Pi.π (fun j : {j // j ∈ s} => A j) ⟨i, hi⟩ else
      (hzero i hi).from_ _), ?_, ?_⟩
  · apply Pi.hom_ext
    intro i
    by_cases hi : i ∈ s
    · simp [hi]
    · exact (hzero i hi).eq_of_tgt _ _
  · apply Pi.hom_ext
    intro i
    simp

/-- A functor preserving the relevant product commutes with it. -/
private noncomputable def mapPiIsoFinite {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {ι : Type*} (A : ι → C)
    [HasProduct A] [HasProduct (fun i => F.obj (A i))]
    [PreservesLimit (Discrete.functor A) F] :
    F.obj (∏ᶜ A) ≅ ∏ᶜ (fun i => F.obj (A i)) :=
  preservesLimitIso F (Discrete.functor A) ≪≫
    HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete A F)

/-- The degree-`n` term of the internal Hom complex of two associated complexes is the sheaf
associated to the degree-`n` term of the module Hom complex, when the source is bounded above
with finite free terms and the target is bounded below.

Only the existence of this isomorphism is used; the comparison singled out by its action on
global sections is `affineHomCanonicalDegreeIso`. -/
private noncomputable def affineHomDegreeTildeIso (R : CommRingCat.{u})
    [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E J : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hE : E.IsStrictlyLE b) (hJ : J.IsStrictlyGE a)
    (hfree : ∀ i : ℤ, StacksDraft.PseudoCoherence.IsFiniteFree (E.X i)) (n : ℤ) :
    (RingedSite.sheafHomComplex (specSite R) ((tildeHC R).obj E)
        ((tildeHC R).obj J)).obj.X n ≅
      (tildeH R).obj ((CochainComplex.HomComplexR R E J).X n) := by
  classical
  let A : ℤ → ModuleCat.{u} R := fun q => ModuleCat.of R (E.X (-q) ⟶ J.X (n - q))
  have hs : ∀ q : ℤ, q ∉ Finset.Icc (-b) (n - a) → IsZero (A q) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    refine moduleHomObject_isZero R _ _ ?_
    by_cases h : -b ≤ q
    · exact Or.inr (J.isZero_of_isStrictlyGE a (n - q) (by omega))
    · exact Or.inl (E.isZero_of_isStrictlyLE b (-q) (by omega))
  have hs' : ∀ q : ℤ, q ∉ Finset.Icc (-b) (n - a) → IsZero ((tildeH R).obj (A q)) :=
    fun q hq => (tildeH R).map_isZero (hs q hq)
  have hterms : ∀ q : ℤ,
      RingedSite.internalHomSheaf (specSite R) (((tildeHC R).obj E).X (-q))
          (((tildeHC R).obj J).X (n - q)) ≅ (tildeH R).obj (A q) := by
    intro q
    have : Module.Finite R (E.X (-q)) := (hfree (-q)).1
    have : Module.Free R (E.X (-q)) := (hfree (-q)).2
    have : Module.FinitePresentation R (E.X (-q)) :=
      Module.finitePresentation_of_projective R (E.X (-q))
    exact affineInternalHomTildeIso R (E.X (-q)) (J.X (n - q))
  refine ((RingedSite.homDegreeIsLimit (specSite R) ((tildeHC R).obj E)
        ((tildeHC R).obj J) n).conePointUniqueUpToIso
      (limit.isLimit (Discrete.functor (fun q : ℤ =>
        RingedSite.internalHomSheaf (specSite R) (((tildeHC R).obj E).X (-q))
          (((tildeHC R).obj J).X (n - q)))))) ≪≫ ?_
  refine Pi.mapIso hterms ≪≫ ?_
  refine piIsoFiniteSupport (fun q => (tildeH R).obj (A q)) _ hs' ≪≫ ?_
  refine (mapPiIsoFinite (tildeH R) (fun i : {i // i ∈ Finset.Icc (-b) (n - a)} => A i)).symm
    ≪≫ ?_
  refine (tildeH R).mapIso (piIsoFiniteSupport A _ hs).symm ≪≫ ?_
  exact (tildeH R).mapIso (ModuleCat.piIsoPi A ≪≫
    (cochainFamilyLinearEquiv E J n).symm.toModuleIso)

/-- Every term of the internal Hom complex of two associated complexes is the sheaf associated
to its module of global sections. -/
private lemma isIso_fromTildeΓ_sheafHomComplex (R : CommRingCat.{u})
    [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E J : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hE : E.IsStrictlyLE b) (hJ : J.IsStrictlyGE a)
    (hfree : ∀ i : ℤ, StacksDraft.PseudoCoherence.IsFiniteFree (E.X i)) (n : ℤ) :
    IsIso (Scheme.Modules.fromTildeΓ
      ((RingedSite.sheafHomComplex (specSite R) ((tildeHC R).obj E)
        ((tildeHC R).obj J)).obj.X n)) :=
  AlgebraicGeometry.isIso_fromTildeΓ_iff.mpr
    ⟨(CochainComplex.HomComplexR R E J).X n,
      ⟨(affineHomDegreeTildeIso R E J a b hE hJ hfree n).symm⟩⟩

/-! ### The complex-level affine comparison -/

/-- The canonical degreewise comparison: the degree-`n` term of the internal Hom complex is the
sheaf associated to its module of global sections, which is the degree-`n` term of the module
Hom complex. -/
private noncomputable def affineHomCanonicalDegreeIso (R : CommRingCat.{u})
    [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E J : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hE : E.IsStrictlyLE b) (hJ : J.IsStrictlyGE a)
    (hfree : ∀ i : ℤ, StacksDraft.PseudoCoherence.IsFiniteFree (E.X i)) (n : ℤ) :
    (RingedSite.sheafHomComplex (specSite R) ((tildeHC R).obj E)
        ((tildeHC R).obj J)).obj.X n ≅
      (tildeH R).obj ((CochainComplex.HomComplexR R E J).X n) :=
  haveI := isIso_fromTildeΓ_sheafHomComplex R E J a b hE hJ hfree n
  (asIso (Scheme.Modules.fromTildeΓ
      ((RingedSite.sheafHomComplex (specSite R) ((tildeHC R).obj E)
        ((tildeHC R).obj J)).obj.X n))).symm ≪≫
    (tildeH R).mapIso (affineHomSectionsLinearEquiv R E J n).toModuleIso

/-- The degreewise comparison sends the canonical global section attached to a module Hom
cochain to the sheaf Hom cochain whose components are the sheafifications of its components.
This is what singles the comparison out. -/
private lemma affineHomCanonicalDegreeIso_inv_sections (R : CommRingCat.{u})
    [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E J : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hE : E.IsStrictlyLE b) (hJ : J.IsStrictlyGE a)
    (hfree : ∀ i : ℤ, StacksDraft.PseudoCoherence.IsFiniteFree (E.X i))
    (n p q : ℤ) (hpq : p + n = q) (α : Cochain E J n) :
    ((RingedSite.sheafHomComplex (specSite R) ((tildeHC R).obj E)
        ((tildeHC R).obj J)).sectionsEquiv (⊤ : Opens (PrimeSpectrum.Top R)) n
      (((affineHomCanonicalDegreeIso R E J a b hE hJ hfree n).inv).val.app (op ⊤)
        (tilde.toOpen ((CochainComplex.HomComplexR R E J).X n) ⊤ α))).v p q hpq =
      (tildeOverTop R).map (α.v p q hpq) := by
  have hc := congrArg (fun k : (CochainComplex.HomComplexR R E J).X n ⟶
      moduleSpecΓFunctor.obj
        ((RingedSite.sheafHomComplex (specSite R) ((tildeHC R).obj E)
          ((tildeHC R).obj J)).obj.X n) => k α)
    (tilde_adjunction_unit_map_counit (R := R)
      ((RingedSite.sheafHomComplex (specSite R) ((tildeHC R).obj E)
        ((tildeHC R).obj J)).obj.X n)
      (affineHomSectionsLinearEquiv R E J n).toModuleIso.inv)
  have he : affineHomSectionsLinearMap R E J n
      (((affineHomCanonicalDegreeIso R E J a b hE hJ hfree n).inv).val.app (op ⊤)
        (tilde.toOpen ((CochainComplex.HomComplexR R E J).X n) ⊤ α)) = α := by
    change affineHomSectionsLinearEquiv R E J n _ = α
    convert (affineHomSectionsLinearEquiv R E J n).apply_symm_apply α using 1
    exact congrArg (affineHomSectionsLinearEquiv R E J n) hc
  have hv : (fullyFaithfulTildeOverTopSite R).preimage
      (((RingedSite.sheafHomComplex (specSite R) ((tildeHC R).obj E)
        ((tildeHC R).obj J)).sectionsEquiv (⊤ : Opens (PrimeSpectrum.Top R)) n
        (((affineHomCanonicalDegreeIso R E J a b hE hJ hfree n).inv).val.app (op ⊤)
          (tilde.toOpen ((CochainComplex.HomComplexR R E J).X n) ⊤ α))).v p q hpq) =
      α.v p q hpq :=
    (affineHomSectionsLinearMap_v R E J n p q hpq _).symm.trans
      (congrArg (fun z : Cochain E J n => z.v p q hpq) he)
  exact ((fullyFaithfulTildeOverTopSite R).map_preimage _).symm.trans
    (congrArg (fun f => (tildeOverTop R).map f) hv)

/-- Two chain maps from a sheafified module Hom complex to an internal Hom complex agree when
their values on the canonical global sections have the same sheaf Hom cochain components. -/
private lemma tildeHomComplex_hom_ext (R : CommRingCat.{u})
    (E J : CochainComplex (ModuleCat.{u} R) ℤ) {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (φ ψ : (tildeHC R).obj (CochainComplex.HomComplexR R P Q) ⟶
      (RingedSite.sheafHomComplex (specSite R) ((tildeHC R).obj E) ((tildeHC R).obj J)).obj)
    (h : ∀ (n : ℤ) (α : (CochainComplex.HomComplexR R P Q).X n) (p q : ℤ) (hpq : p + n = q),
      ((RingedSite.sheafHomComplex (specSite R) ((tildeHC R).obj E)
          ((tildeHC R).obj J)).sectionsEquiv (⊤ : Opens (PrimeSpectrum.Top R)) n
        ((φ.f n).val.app (op ⊤) (tilde.toOpen ((CochainComplex.HomComplexR R P Q).X n) ⊤ α))).v
          p q hpq =
      ((RingedSite.sheafHomComplex (specSite R) ((tildeHC R).obj E)
          ((tildeHC R).obj J)).sectionsEquiv (⊤ : Opens (PrimeSpectrum.Top R)) n
        ((ψ.f n).val.app (op ⊤) (tilde.toOpen ((CochainComplex.HomComplexR R P Q).X n) ⊤ α))).v
          p q hpq) :
    φ = ψ := by
  ext n : 1
  apply tildeHom_ext_globalSections R
  intro α
  apply (RingedSite.SheafHomComplex.sectionsEquiv
    (RingedSite.sheafHomComplex (specSite R) ((tildeHC R).obj E) ((tildeHC R).obj J))
    (⊤ : Opens (PrimeSpectrum.Top R)) n).injective
  apply Cochain.ext
  intro p q hpq
  exact h n α p q hpq

/-- **The complex-level affine comparison.** The internal Hom complex of two associated
complexes is the sheaf associated to the module Hom complex, when the source is bounded above
with finite free terms and the target is bounded below. -/
private noncomputable def affineHomComplexIso (R : CommRingCat.{u})
    [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E J : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hE : E.IsStrictlyLE b) (hJ : J.IsStrictlyGE a)
    (hfree : ∀ i : ℤ, StacksDraft.PseudoCoherence.IsFiniteFree (E.X i)) :
    (RingedSite.sheafHomComplex (specSite R) ((tildeHC R).obj E)
        ((tildeHC R).obj J)).obj ≅
      (tildeHC R).obj (CochainComplex.HomComplexR R E J) :=
  (tildeΓComplexIso R _
      (fun n => isIso_fromTildeΓ_sheafHomComplex R E J a b hE hJ hfree n)).symm ≪≫
    (tildeHC R).mapIso (affineHomSectionsComplexIso R E J)

/-- The inverse of the complex-level affine comparison takes a module Hom cochain to the sheaf
Hom cochain whose components are the sheafifications of its components. This is what pins the
comparison down, excluding in particular a global sign. -/
private lemma affineHomComplexIso_inv_toOpen (R : CommRingCat.{u})
    [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E J : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hE : E.IsStrictlyLE b) (hJ : J.IsStrictlyGE a)
    (hfree : ∀ i : ℤ, StacksDraft.PseudoCoherence.IsFiniteFree (E.X i))
    (n p q : ℤ) (hpq : p + n = q) (α : Cochain E J n) :
    ((RingedSite.sheafHomComplex (specSite R) ((tildeHC R).obj E)
        ((tildeHC R).obj J)).sectionsEquiv (⊤ : Opens (PrimeSpectrum.Top R)) n
      (((affineHomComplexIso R E J a b hE hJ hfree).inv.f n).val.app (op ⊤)
        (tilde.toOpen ((CochainComplex.HomComplexR R E J).X n) ⊤ α))).v p q hpq =
      (tildeOverTop R).map (α.v p q hpq) :=
  affineHomCanonicalDegreeIso_inv_sections R E J a b hE hJ hfree n p q hpq α

/-! ### Naturality of the complex-level comparison -/

/-- The complex-level affine comparison is natural in both variables: it carries the induced
map of module Hom complexes to the induced map of internal Hom complexes. -/
private lemma affineHomComplexIso_inv_naturality (R : CommRingCat.{u})
    [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E E' J J' : CochainComplex (ModuleCat.{u} R) ℤ) (a b a' b' : ℤ)
    (hE : E.IsStrictlyLE b) (hJ : J.IsStrictlyGE a)
    (hfree : ∀ i : ℤ, StacksDraft.PseudoCoherence.IsFiniteFree (E.X i))
    (hE' : E'.IsStrictlyLE b') (hJ' : J'.IsStrictlyGE a')
    (hfree' : ∀ i : ℤ, StacksDraft.PseudoCoherence.IsFiniteFree (E'.X i))
    (f : E' ⟶ E) (g : J ⟶ J') :
    (tildeHC R).map (Stacks.HomComplex.TensorHomComparison.HomCxMap E E' J J' f g) ≫
        (affineHomComplexIso R E' J' a' b' hE' hJ' hfree').inv =
      (affineHomComplexIso R E J a b hE hJ hfree).inv ≫
        RingedSite.homMap (specSite R) ((tildeHC R).map f) ((tildeHC R).map g) := by
  apply tildeHomComplex_hom_ext R E' J' (P := E) (Q := J)
  intro n α p q hpq
  have ht :
      (((tildeH R).map
          ((Stacks.HomComplex.TensorHomComparison.HomCxMap E E' J J' f g).f n)).val.app
            (op ⊤)) (tilde.toOpen ((CochainComplex.HomComplexR R E J).X n) ⊤ α) =
        tilde.toOpen ((CochainComplex.HomComplexR R E' J').X n) ⊤
          (((Stacks.HomComplex.TensorHomComparison.HomCxMap E E' J J' f g).f n).hom α) :=
    ConcreteCategory.congr_hom
      (tilde.toOpen_map_app
        ((Stacks.HomComplex.TensorHomComparison.HomCxMap E E' J J' f g).f n) ⊤) α
  change ((RingedSite.sheafHomComplex (specSite R) ((tildeHC R).obj E')
        ((tildeHC R).obj J')).sectionsEquiv (⊤ : Opens (PrimeSpectrum.Top R)) n
      (((affineHomComplexIso R E' J' a' b' hE' hJ' hfree').inv.f n).val.app (op ⊤)
        (((tildeH R).map
          ((Stacks.HomComplex.TensorHomComparison.HomCxMap E E' J J' f g).f n)).val.app
            (op ⊤) (tilde.toOpen _ ⊤ α)))).v p q hpq =
    ((RingedSite.sheafHomComplex (specSite R) ((tildeHC R).obj E')
        ((tildeHC R).obj J')).sectionsEquiv (⊤ : Opens (PrimeSpectrum.Top R)) n
      (((RingedSite.homMap (specSite R) ((tildeHC R).map f) ((tildeHC R).map g)).f n).val.app
        (op ⊤)
        (((affineHomComplexIso R E J a b hE hJ hfree).inv.f n).val.app (op ⊤)
          (tilde.toOpen _ ⊤ α)))).v p q hpq
  rw [ht]
  trans (tildeOverTop R).map (f.f p) ≫ (tildeOverTop R).map (α.v p q hpq) ≫
    (tildeOverTop R).map (g.f q)
  · refine (affineHomComplexIso_inv_toOpen R E' J' a' b' hE' hJ' hfree' n p q hpq _).trans ?_
    refine (congrArg (fun h => (tildeOverTop R).map h)
      (Stacks.HomComplex.TensorHomComparison.HomCxMapDeg_v E E' J J' f g n α p q hpq)).trans ?_
    exact ((tildeOverTop R).map_comp _ _).trans
      (congrArg (fun w => (tildeOverTop R).map (f.f p) ≫ w) ((tildeOverTop R).map_comp _ _))
  · refine Eq.trans (congrArg (fun w => (tildeOverTop R).map (f.f p) ≫ w ≫
      (tildeOverTop R).map (g.f q))
        (affineHomComplexIso_inv_toOpen R E J a b hE hJ hfree n p q hpq α).symm) ?_
    exact (RingedSite.sectionsIso_homMap_v (specSite R) ((tildeHC R).map f)
      ((tildeHC R).map g) (⊤ : Opens (PrimeSpectrum.Top R)) n p q hpq _).symm

/-! ### Abstract rearrangements -/

/-- A naturality square for the `inv` components gives one for the `hom` components. -/
private lemma iso_hom_naturality {C : Type*} [Category C] {A B A' B' : C}
    (e : A ≅ B) (e' : A' ≅ B') (f : A ⟶ A') (g : B ⟶ B')
    (h : g ≫ e'.inv = e.inv ≫ f) : f ≫ e'.hom = e.hom ≫ g :=
  (CommSq.vert_inv (g := e.symm) (h := e'.symm) ⟨h⟩).w

/-- Pasting four naturality squares into one, for a composite isomorphism with four factors. -/
private lemma paste_four_squares {C : Type*} [Category C]
    {S₀ S₁ S₂ S₃ S₄ T₀ T₁ T₂ T₃ T₄ : C}
    {u : S₀ ⟶ T₀} {a : S₀ ⟶ S₁} {a' : T₀ ⟶ T₁} {u₁ : S₁ ⟶ T₁}
    {b : S₁ ⟶ S₂} {b' : T₁ ⟶ T₂} {u₂ : S₂ ⟶ T₂}
    {c : S₂ ⟶ S₃} {c' : T₂ ⟶ T₃} {u₃ : S₃ ⟶ T₃}
    {d : S₃ ⟶ S₄} {d' : T₃ ⟶ T₄} {v : S₄ ⟶ T₄}
    (h₁ : u ≫ a' = a ≫ u₁) (h₂ : u₁ ≫ b' = b ≫ u₂) (h₃ : u₂ ≫ c' = c ≫ u₃)
    (h₄ : u₃ ≫ d' = d ≫ v) :
    u ≫ a' ≫ b' ≫ c' ≫ d' = (a ≫ b ≫ c ≫ d) ≫ v := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]
  simp only [Category.assoc]

/-- Pasting three naturality squares into one, when the leading square covers the first two
factors of a four-factor composite. -/
private lemma paste_double_then_two {C : Type*} [Category C]
    {S₀ S₁ S₂ S₃ S₄ T₀ T₁ T₂ T₃ T₄ : C}
    {u : S₀ ⟶ T₀} {a₁ : S₀ ⟶ S₁} {a₂ : S₁ ⟶ S₂}
    {b₁ : T₀ ⟶ T₁} {b₂ : T₁ ⟶ T₂} {u₂ : S₂ ⟶ T₂}
    {a₃ : S₂ ⟶ S₃} {b₃ : T₂ ⟶ T₃} {u₃ : S₃ ⟶ T₃}
    {a₄ : S₃ ⟶ S₄} {b₄ : T₃ ⟶ T₄} {u₄ : S₄ ⟶ T₄}
    (h₁ : u ≫ b₁ ≫ b₂ = (a₁ ≫ a₂) ≫ u₂)
    (h₂ : u₂ ≫ b₃ = a₃ ≫ u₃) (h₃ : u₃ ≫ b₄ = a₄ ≫ u₄) :
    u ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ = (a₁ ≫ a₂ ≫ a₃ ≫ a₄) ≫ u₄ := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]
  simp only [Category.assoc]

/-! ### Chosen representatives -/

/-- Derived sheafification, read as a functor into the derived category of `SpecHomModules R`. -/
private abbrev tildeD (R : CommRingCat.{u}) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (SpecHomModules R) :=
  (tildeH R).mapDerivedCategory

/-- A pseudo-coherent object has a bounded-above representative with finite free terms. -/
private lemma exists_pseudoCoherent_finiteFree_representative (R : CommRingCat.{u})
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    ∃ (E : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ),
      E.IsStrictlyLE b ∧
        (∀ i : ℤ, StacksDraft.PseudoCoherence.IsFiniteFree (E.X i)) ∧
        Nonempty ((DerivedCategory.Q).obj E ≅ K) := by
  obtain ⟨E, hE, e⟩ := hK
  obtain ⟨b, hb⟩ := hE.upperBound
  exact ⟨E, b, hb, hE.finiteFree, e⟩

/-- A bounded-below object has a bounded-below K-injective representative. -/
private lemma exists_boundedBelow_kInjective_representative (R : CommRingCat.{u})
    (L : DerivedCategory (ModuleCat.{u} R))
    (hL : (DerivedCategory.TStructure.t).plus L) :
    ∃ (J : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ),
      J.IsStrictlyGE a ∧ J.IsKInjective ∧ Nonempty (DerivedCategory.Q.obj J ≅ L) := by
  obtain ⟨a, ha⟩ := hL
  have : (DerivedCategory.TStructure.t).IsGE L a := ha
  obtain ⟨F, hF, ⟨eF⟩⟩ := L.exists_iso_Q_obj_of_isGE a
  have : F.IsStrictlyGE a := hF
  obtain ⟨r, -, hr⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a F
  have : r.cocomplex.IsStrictlyGE a := hr
  exact ⟨r.cocomplex, a, hr,
    CochainComplex.isKInjective_of_injective r.cocomplex a,
    ⟨(asIso (DerivedCategory.Q.map r.ι)).symm ≪≫ eF.symm⟩⟩

/-- A bounded-above representative with finite free terms of a pseudo-coherent object. -/
private structure PseudoRep (R : CommRingCat.{u}) (K : DerivedCategory (ModuleCat.{u} R)) where
  /-- The representing complex. -/
  cx : CochainComplex (ModuleCat.{u} R) ℤ
  /-- An upper bound for its support. -/
  bound : ℤ
  /-- The complex vanishes above `bound`. -/
  le : cx.IsStrictlyLE bound
  /-- Every term is finite free. -/
  free : ∀ i : ℤ, StacksDraft.PseudoCoherence.IsFiniteFree (cx.X i)
  /-- It represents the given derived object. -/
  iso : DerivedCategory.Q.obj cx ≅ K

/-- A bounded-below K-injective representative of a bounded-below object. -/
private structure PlusRep (R : CommRingCat.{u}) (L : DerivedCategory (ModuleCat.{u} R)) where
  /-- The representing complex. -/
  cx : CochainComplex (ModuleCat.{u} R) ℤ
  /-- A lower bound for its support. -/
  bound : ℤ
  /-- The complex vanishes below `bound`. -/
  ge : cx.IsStrictlyGE bound
  /-- The complex is K-injective. -/
  kinj : cx.IsKInjective
  /-- It represents the given derived object. -/
  iso : DerivedCategory.Q.obj cx ≅ L

private lemma nonempty_pseudoRep (R : CommRingCat.{u}) (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) : Nonempty (PseudoRep R K) := by
  obtain ⟨E, b, hb, hfree, ⟨e⟩⟩ := exists_pseudoCoherent_finiteFree_representative R K hK
  exact ⟨⟨E, b, hb, hfree, e⟩⟩

private lemma nonempty_plusRep (R : CommRingCat.{u}) (L : DerivedCategory (ModuleCat.{u} R))
    (hL : (DerivedCategory.TStructure.t).plus L) : Nonempty (PlusRep R L) := by
  obtain ⟨J, a, ha, hkinj, ⟨e⟩⟩ := exists_boundedBelow_kInjective_representative R L hL
  exact ⟨⟨J, a, ha, hkinj, e⟩⟩

private noncomputable def pseudoRep (R : CommRingCat.{u})
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) : PseudoRep R K :=
  Classical.choice (nonempty_pseudoRep R K hK)

private noncomputable def plusRep (R : CommRingCat.{u}) (L : DerivedCategory (ModuleCat.{u} R))
    (hL : (DerivedCategory.TStructure.t).plus L) : PlusRep R L :=
  Classical.choice (nonempty_plusRep R L hL)

/-- The comparison of the sheafified derived object with the localization of the sheafified
representative. -/
private noncomputable def repIso (R : CommRingCat.{u}) (M : DerivedCategory (ModuleCat.{u} R))
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (e : DerivedCategory.Q.obj C ≅ M) :
    (tildeD R).obj M ≅ DerivedCategory.Q.obj ((tildeHC R).obj C) :=
  (tildeD R).mapIso e.symm ≪≫ (tildeH R).mapDerivedCategoryFactors.app C

/-! ### The comparison on a chosen pair of representatives -/

/-- The 08I5 comparison for a bounded-above sheafified complex of finite free modules against
a bounded-below target. -/
private lemma isIso_affineStrictlyPerfectHomComparison (R : CommRingCat.{u})
    [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (specSite R).O))]
    (D : RingedSite.DerivedInternalHom.{u, u + 1} (specSite R))
    (E J : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hE : E.IsStrictlyLE b) (hJ : J.IsStrictlyGE a)
    (hfree : ∀ i : ℤ, StacksDraft.PseudoCoherence.IsFiniteFree (E.X i)) :
    IsIso (RingedSite.strictlyPerfectHomComparison (specSite R) D
      ((tildeHC R).obj E) ((tildeHC R).obj J)) :=
  RingedSite.strictlyPerfectHomComparison_isIso_of_boundedAbove (specSite R)
    ((tildeHC R).obj E) ((tildeHC R).obj J) D a
    (tildeHC_isZero_of_isStrictlyGE R J a hJ)
    ⟨b, tildeHC_isZero_of_isStrictlyLE R E b hE⟩
    (fun i => tildeObj_isFiniteFreeSummand R (E.X i) (hfree i))

/-- The affine comparison on a bounded-above representative with finite free terms of the
source and a bounded-below representative of the target. -/
private noncomputable def modelIso (R : CommRingCat.{u})
    [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E J : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hE : E.IsStrictlyLE b) (hJ : J.IsStrictlyGE a)
    (hfree : ∀ i : ℤ, StacksDraft.PseudoCoherence.IsFiniteFree (E.X i)) :
    ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
        (op (DerivedCategory.Q.obj ((tildeHC R).obj E)))).obj
          (DerivedCategory.Q.obj ((tildeHC R).obj J)) ≅
      (tildeD R).obj
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.obj
          (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj J)) :=
  haveI := hE
  haveI : ∀ i : ℤ, Projective (E.X i) := fun i => projective_of_isFiniteFree (hfree i)
  haveI := isIso_affineStrictlyPerfectHomComparison R
    (Stacks.SheafOfModules.derivedInternalHom (Spec R).sheaf) E J a b hE hJ hfree
  (asIso (RingedSite.strictlyPerfectHomComparison (specSite R)
      (Stacks.SheafOfModules.derivedInternalHom (Spec R).sheaf)
      ((tildeHC R).obj E) ((tildeHC R).obj J))).symm ≪≫
    DerivedCategory.Q.mapIso (affineHomComplexIso R E J a b hE hJ hfree) ≪≫
    ((tildeH R).mapDerivedCategoryFactors.app (CochainComplex.HomComplexR R E J)).symm ≪≫
    (tildeD R).mapIso
      ((StacksDraft.DerivedHom.projectiveHomComparison (R := R)).iso E J b).symm

/-- The model comparison is natural for chain maps between the representatives: its four
factors paste into one square. -/
private lemma modelIso_naturality (R : CommRingCat.{u})
    [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E E' J J' : CochainComplex (ModuleCat.{u} R) ℤ) (a b a' b' : ℤ)
    (hE : E.IsStrictlyLE b) (hJ : J.IsStrictlyGE a)
    (hfree : ∀ i : ℤ, StacksDraft.PseudoCoherence.IsFiniteFree (E.X i))
    (hE' : E'.IsStrictlyLE b') (hJ' : J'.IsStrictlyGE a')
    (hfree' : ∀ i : ℤ, StacksDraft.PseudoCoherence.IsFiniteFree (E'.X i))
    (k : E' ⟶ E) (h : J ⟶ J') :
    (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).map
          (DerivedCategory.Q.map ((tildeHC R).map k)).op).app
          (DerivedCategory.Q.obj ((tildeHC R).obj J)) ≫
        ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
          (op (DerivedCategory.Q.obj ((tildeHC R).obj E')))).map
            (DerivedCategory.Q.map ((tildeHC R).map h))) ≫
      (modelIso R E' J' a' b' hE' hJ' hfree').hom =
    (modelIso R E J a b hE hJ hfree).hom ≫
      (tildeD R).map
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.map
          (show (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj J) ⟶
            (op (DerivedCategory.Q.obj E'), DerivedCategory.Q.obj J') from
            ((DerivedCategory.Q.map k).op, DerivedCategory.Q.map h))) := by
  have := hE
  have := hE'
  have : ∀ i : ℤ, Projective (E.X i) := fun i => projective_of_isFiniteFree (hfree i)
  have : ∀ i : ℤ, Projective (E'.X i) := fun i => projective_of_isFiniteFree (hfree' i)
  have := isIso_affineStrictlyPerfectHomComparison R
    (Stacks.SheafOfModules.derivedInternalHom (Spec R).sheaf) E J a b hE hJ hfree
  have := isIso_affineStrictlyPerfectHomComparison R
    (Stacks.SheafOfModules.derivedInternalHom (Spec R).sheaf) E' J' a' b' hE' hJ' hfree'
  have h₁ := (CommSq.vert_inv
    (g := asIso (RingedSite.strictlyPerfectHomComparison (specSite R)
      (Stacks.SheafOfModules.derivedInternalHom (Spec R).sheaf)
      ((tildeHC R).obj E) ((tildeHC R).obj J)))
    (h := asIso (RingedSite.strictlyPerfectHomComparison (specSite R)
      (Stacks.SheafOfModules.derivedInternalHom (Spec R).sheaf)
      ((tildeHC R).obj E') ((tildeHC R).obj J')))
    ⟨RingedSite.strictlyPerfectHomComparison_naturality (specSite R)
      (Stacks.SheafOfModules.derivedInternalHom (Spec R).sheaf)
      ((tildeHC R).obj E) ((tildeHC R).obj E') ((tildeHC R).obj J) ((tildeHC R).obj J')
      ((tildeHC R).map k) ((tildeHC R).map h)⟩).w
  have h₂ := map_comp_naturality DerivedCategory.Q
    (iso_hom_naturality (affineHomComplexIso R E J a b hE hJ hfree)
      (affineHomComplexIso R E' J' a' b' hE' hJ' hfree') _ _
      (affineHomComplexIso_inv_naturality R E E' J J' a b a' b' hE hJ hfree hE' hJ' hfree' k h))
  have h₃ := (CommSq.vert_inv
    (g := (tildeH R).mapDerivedCategoryFactors.app (CochainComplex.HomComplexR R E J))
    (h := (tildeH R).mapDerivedCategoryFactors.app (CochainComplex.HomComplexR R E' J'))
    ⟨(tildeH R).mapDerivedCategoryFactors_hom_naturality
      (Stacks.HomComplex.TensorHomComparison.HomCxMap E E' J J' k h)⟩).w
  have h₄ := map_comp_naturality (tildeD R)
    (CommSq.vert_inv
      (g := (StacksDraft.DerivedHom.projectiveHomComparison (R := R)).iso E J b)
      (h := (StacksDraft.DerivedHom.projectiveHomComparison (R := R)).iso E' J' b')
      ⟨(StacksDraft.DerivedHom.projectiveHomComparison (R := R)).naturality
        E E' J J' b b' k h⟩).w
  exact paste_four_squares h₁ h₂ h₃ h₄

/-! ### Lifting a derived morphism to the chosen representatives -/

private lemma isKProjective_pseudoRep (R : CommRingCat.{u})
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    (pseudoRep R K hK).cx.IsKProjective := by
  have := (pseudoRep R K hK).le
  have : ∀ i : ℤ, Projective ((pseudoRep R K hK).cx.X i) := fun i =>
    projective_of_isFiniteFree ((pseudoRep R K hK).free i)
  exact CochainComplex.isKProjective_of_projective _ (pseudoRep R K hK).bound

/-- Naturality of the comparison between a derived object and the localization of a chosen
representative, stated abstractly. -/
private lemma rep_naturality {C D E : Type*} [Category C] [Category D] [Category E]
    (Qc : C ⥤ D) (G : D ⥤ E) (P : C ⥤ E) (c : Qc ⋙ G ≅ P)
    {X X' : C} {M M' : D} (eM : Qc.obj X ≅ M) (eM' : Qc.obj X' ≅ M')
    (w : M ⟶ M') (k : X ⟶ X') (hk : Qc.map k = eM.hom ≫ w ≫ eM'.inv) :
    G.map w ≫ G.map eM'.inv ≫ (c.app X').hom =
      (G.map eM.inv ≫ (c.app X).hom) ≫ P.map k := by
  have hc : G.map (Qc.map k) ≫ (c.app X').hom = (c.app X).hom ≫ P.map k :=
    c.hom.naturality k
  rw [Category.assoc, ← hc, ← Category.assoc (G.map eM.inv),
    ← CategoryTheory.Functor.map_comp, hk, Iso.inv_hom_id_assoc,
    CategoryTheory.Functor.map_comp, Category.assoc]

/-- The uncurried derived internal Hom bifunctor of `Spec R`. -/
private noncomputable abbrev sheafDerivedHomPair (R : CommRingCat.{u})
    [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (DerivedCategory (SpecHomModules R))ᵒᵖ × DerivedCategory (SpecHomModules R) ⥤
      DerivedCategory (SpecHomModules R) :=
  CategoryTheory.Functor.uncurry.obj (Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf)

/-! ### The affine comparison of [Stacks, Tag 0A6H] (3)(a) -/

/-- **[Stacks, Tag 0A6H] (3)(a).** Let `R` be a commutative ring, `X = Spec R`, and let `K`, `L`
be objects of `D(R)` with `K` pseudo-coherent and `L` bounded below. Then the derived internal
Hom of the derived sheafifications of `K` and `L` is the derived sheafification of the derived
Hom `RHom_R(K, L)`:

`RSheafHom_{𝒪_X}(K̃, L̃) ≅ (RHom_R(K, L))~`.

The comparison is not an arbitrary isomorphism. `K` is replaced by a bounded-above
representative with finite free terms and `L` by a bounded-below K-injective representative;
there the sheaf side is computed by the ordinary internal Hom complex (Stacks 08I5) and the
module side by the ordinary Hom complex (Stacks 0A66), and the comparison is the one pinned
degreewise by the affine internal-Hom isomorphism of [Stacks, Tag 01I8]. The representatives
are definite choices, so the construction is a function of its arguments, and it is natural in
both of them (`affinePseudoCoherentDerivedSheafHomIso_natural_left` and
`affinePseudoCoherentDerivedSheafHomIso_natural_right`). The canonical comparison
`AlgebraicGeometry.affineDerivedTildeHomComparison` in the other direction is an isomorphism under
the same hypotheses, `isIso_affineDerivedTildeHomComparison_of_isPseudoCoherent`. -/
@[no_expose, stacks 0A6H "(3)(a) K pseudo-coherent and L bounded below"]
noncomputable def affinePseudoCoherentDerivedSheafHomIso (R : CommRingCat.{u})
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hL : (DerivedCategory.TStructure.t).plus L) :
    ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
        (op ((tilde.functor R).mapDerivedCategory.obj K))).obj
          ((tilde.functor R).mapDerivedCategory.obj L) ≅
      (tilde.functor R).mapDerivedCategory.obj
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.obj (op K, L)) :=
  ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).mapIso
      (repIso R K (pseudoRep R K hK).cx (pseudoRep R K hK).iso).op.symm).app
        ((tildeD R).obj L) ≪≫
    ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
      (op (DerivedCategory.Q.obj ((tildeHC R).obj (pseudoRep R K hK).cx)))).mapIso
        (repIso R L (plusRep R L hL).cx (plusRep R L hL).iso) ≪≫
    modelIso R (pseudoRep R K hK).cx (plusRep R L hL).cx (plusRep R L hL).bound
      (pseudoRep R K hK).bound (pseudoRep R K hK).le (plusRep R L hL).ge
      (pseudoRep R K hK).free ≪≫
    (tildeD R).mapIso
      ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.mapIso
        (Iso.prod (pseudoRep R K hK).iso.op.symm (plusRep R L hL).iso))

/-- The affine comparison is natural in both variables at once. The chosen representatives of
two different derived objects are unrelated, so the derived morphism is lifted to a chain map
between them — possible because the source representative is K-projective and the target
representative K-injective — and the resulting square is `modelIso_naturality` pasted with the
two representative comparisons. -/
private lemma affinePseudoCoherentDerivedSheafHomIso_naturality (R : CommRingCat.{u})
    [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {K K' L L' : DerivedCategory (ModuleCat.{u} R)}
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hK' : StacksDraft.PseudoCoherence.IsPseudoCoherent K')
    (hL : (DerivedCategory.TStructure.t).plus L)
    (hL' : (DerivedCategory.TStructure.t).plus L')
    (f : K' ⟶ K) (g : L ⟶ L') :
    (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).map
          ((tildeD R).map f).op).app ((tildeD R).obj L) ≫
        ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
          (op ((tildeD R).obj K'))).map ((tildeD R).map g)) ≫
      (affinePseudoCoherentDerivedSheafHomIso R K' L' hK' hL').hom =
    (affinePseudoCoherentDerivedSheafHomIso R K L hK hL).hom ≫
      (tildeD R).map
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.map
          (show (op K, L) ⟶ (op K', L') from (f.op, g))) := by
  have := isKProjective_pseudoRep R K' hK'
  have := (plusRep R L' hL').kinj
  obtain ⟨k, hk⟩ := Q_map_surjective_of_isKProjective
    (pseudoRep R K' hK').cx (pseudoRep R K hK).cx
    ((pseudoRep R K' hK').iso.hom ≫ f ≫ (pseudoRep R K hK).iso.inv)
  obtain ⟨w, hw⟩ := Q_map_surjective_of_isKInjective
    (plusRep R L hL).cx (plusRep R L' hL').cx
    ((plusRep R L hL).iso.hom ≫ g ≫ (plusRep R L' hL').iso.inv)
  have hcon : (repIso R K' (pseudoRep R K' hK').cx (pseudoRep R K' hK').iso).inv ≫
        (tildeD R).map f =
      DerivedCategory.Q.map ((tildeHC R).map k) ≫
        (repIso R K (pseudoRep R K hK).cx (pseudoRep R K hK).iso).inv :=
    (CommSq.vert_inv
      (g := repIso R K' (pseudoRep R K' hK').cx (pseudoRep R K' hK').iso)
      (h := repIso R K (pseudoRep R K hK).cx (pseudoRep R K hK).iso)
      ⟨rep_naturality DerivedCategory.Q (tildeD R) _
        (tildeH R).mapDerivedCategoryFactors
        (pseudoRep R K' hK').iso (pseudoRep R K hK).iso f k hk⟩).w.symm
  have hcov : (tildeD R).map g ≫
        (repIso R L' (plusRep R L' hL').cx (plusRep R L' hL').iso).hom =
      (repIso R L (plusRep R L hL).cx (plusRep R L hL).iso).hom ≫
        DerivedCategory.Q.map ((tildeHC R).map w) :=
    rep_naturality DerivedCategory.Q (tildeD R) _
      (tildeH R).mapDerivedCategoryFactors
      (plusRep R L hL).iso (plusRep R L' hL').iso g w hw
  have hpair : (show ((op ((tildeD R).obj K), (tildeD R).obj L) :
          (DerivedCategory (SpecHomModules R))ᵒᵖ × DerivedCategory (SpecHomModules R)) ⟶
        (op ((tildeD R).obj K'), (tildeD R).obj L') from
        (((tildeD R).map f).op, (tildeD R).map g)) ≫
      (show ((op ((tildeD R).obj K'), (tildeD R).obj L') :
          (DerivedCategory (SpecHomModules R))ᵒᵖ × DerivedCategory (SpecHomModules R)) ⟶
        (op (DerivedCategory.Q.obj ((tildeHC R).obj (pseudoRep R K' hK').cx)),
          DerivedCategory.Q.obj ((tildeHC R).obj (plusRep R L' hL').cx)) from
        ((repIso R K' (pseudoRep R K' hK').cx (pseudoRep R K' hK').iso).inv.op,
          (repIso R L' (plusRep R L' hL').cx (plusRep R L' hL').iso).hom)) =
    (show ((op ((tildeD R).obj K), (tildeD R).obj L) :
          (DerivedCategory (SpecHomModules R))ᵒᵖ × DerivedCategory (SpecHomModules R)) ⟶
        (op (DerivedCategory.Q.obj ((tildeHC R).obj (pseudoRep R K hK).cx)),
          DerivedCategory.Q.obj ((tildeHC R).obj (plusRep R L hL).cx)) from
        ((repIso R K (pseudoRep R K hK).cx (pseudoRep R K hK).iso).inv.op,
          (repIso R L (plusRep R L hL).cx (plusRep R L hL).iso).hom)) ≫
      ((DerivedCategory.Q.map ((tildeHC R).map k)).op,
        DerivedCategory.Q.map ((tildeHC R).map w)) :=
    Prod.ext (congrArg Quiver.Hom.op hcon) hcov
  have h1 : (pseudoRep R K' hK').iso.inv ≫ DerivedCategory.Q.map k =
      f ≫ (pseudoRep R K hK).iso.inv :=
    (congrArg (fun z => (pseudoRep R K' hK').iso.inv ≫ z) hk).trans
      (Iso.inv_hom_id_assoc _ _)
  have h2 : DerivedCategory.Q.map w ≫ (plusRep R L' hL').iso.hom =
      (plusRep R L hL).iso.hom ≫ g := by
    rw [hw]
    simp
  have hpair2 : (show ((op (DerivedCategory.Q.obj (pseudoRep R K hK).cx),
            DerivedCategory.Q.obj (plusRep R L hL).cx) :
          (DerivedCategory (ModuleCat.{u} R))ᵒᵖ × DerivedCategory (ModuleCat.{u} R)) ⟶
        (op (DerivedCategory.Q.obj (pseudoRep R K' hK').cx),
          DerivedCategory.Q.obj (plusRep R L' hL').cx) from
        ((DerivedCategory.Q.map k).op, DerivedCategory.Q.map w)) ≫
      ((pseudoRep R K' hK').iso.inv.op, (plusRep R L' hL').iso.hom) =
    (show ((op (DerivedCategory.Q.obj (pseudoRep R K hK).cx),
            DerivedCategory.Q.obj (plusRep R L hL).cx) :
          (DerivedCategory (ModuleCat.{u} R))ᵒᵖ × DerivedCategory (ModuleCat.{u} R)) ⟶
        (op K, L) from
        ((pseudoRep R K hK).iso.inv.op, (plusRep R L hL).iso.hom)) ≫
      (show ((op K, L) :
          (DerivedCategory (ModuleCat.{u} R))ᵒᵖ × DerivedCategory (ModuleCat.{u} R)) ⟶
        (op K', L') from (f.op, g)) :=
    Prod.ext (congrArg Quiver.Hom.op h1) h2
  exact paste_double_then_two
    (map_comp_naturality (sheafDerivedHomPair R) hpair)
    (modelIso_naturality R (pseudoRep R K hK).cx (pseudoRep R K' hK').cx
      (plusRep R L hL).cx (plusRep R L' hL').cx
      (plusRep R L hL).bound (pseudoRep R K hK).bound
      (plusRep R L' hL').bound (pseudoRep R K' hK').bound
      (pseudoRep R K hK).le (plusRep R L hL).ge (pseudoRep R K hK).free
      (pseudoRep R K' hK').le (plusRep R L' hL').ge (pseudoRep R K' hK').free k w)
    (map_comp_naturality (tildeD R)
      (map_comp_naturality
        (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom hpair2))

/-- **[Stacks, Tag 0A6H] (3)(a).** The affine comparison is contravariantly natural in the
pseudo-coherent argument. -/
@[stacks 0A6H "(3)(a) K pseudo-coherent and L bounded below"]
theorem affinePseudoCoherentDerivedSheafHomIso_natural_left (R : CommRingCat.{u})
    {K K' L : DerivedCategory (ModuleCat.{u} R)}
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hK' : StacksDraft.PseudoCoherence.IsPseudoCoherent K')
    (hL : (DerivedCategory.TStructure.t).plus L) (f : K' ⟶ K) :
    ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).map
        ((tilde.functor R).mapDerivedCategory.map f).op).app
          ((tilde.functor R).mapDerivedCategory.obj L) ≫
      (affinePseudoCoherentDerivedSheafHomIso R K' L hK' hL).hom =
    (affinePseudoCoherentDerivedSheafHomIso R K L hK hL).hom ≫
      (tilde.functor R).mapDerivedCategory.map
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.map
          (f.op, 𝟙 L)) :=
  comp_eq_of_snd_eq_id
    ((congrArg (fun z => ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
          (op ((tildeD R).obj K'))).map z)
        (CategoryTheory.Functor.map_id (tildeD R) L)).trans
      (CategoryTheory.Functor.map_id
        ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
          (op ((tildeD R).obj K'))) ((tildeD R).obj L)))
    (affinePseudoCoherentDerivedSheafHomIso_naturality R hK hK' hL hL f (𝟙 L))

/-- **[Stacks, Tag 0A6H] (3)(a).** The affine comparison is covariantly natural in the
bounded-below argument. -/
@[stacks 0A6H "(3)(a) K pseudo-coherent and L bounded below"]
theorem affinePseudoCoherentDerivedSheafHomIso_natural_right (R : CommRingCat.{u})
    {K L L' : DerivedCategory (ModuleCat.{u} R)}
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hL : (DerivedCategory.TStructure.t).plus L)
    (hL' : (DerivedCategory.TStructure.t).plus L') (g : L ⟶ L') :
    ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
        (op ((tilde.functor R).mapDerivedCategory.obj K))).map
          ((tilde.functor R).mapDerivedCategory.map g) ≫
      (affinePseudoCoherentDerivedSheafHomIso R K L' hK hL').hom =
    (affinePseudoCoherentDerivedSheafHomIso R K L hK hL).hom ≫
      (tilde.functor R).mapDerivedCategory.map
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.map
          (𝟙 (op K), g)) :=
  comp_eq_of_fst_eq_id
    ((congrArg (fun z => NatTrans.app
          ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).map z)
          ((tildeD R).obj L))
        (congrArg Quiver.Hom.op (CategoryTheory.Functor.map_id (tildeD R) K))).trans
      (congrArg (fun z => NatTrans.app z ((tildeD R).obj L))
        (CategoryTheory.Functor.map_id
          (Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf)
          (op ((tildeD R).obj K)))))
    (affinePseudoCoherentDerivedSheafHomIso_naturality R hK hK hL hL' (𝟙 K) g)

/-! ### The comparison of (3)(a) is the canonical comparison -/

/-- The complex-level affine comparison is the canonical complex-level map
`AlgebraicGeometry.affineHomComplexTildeMap`, inverted. -/
private lemma affineHomComplexIso_inv_eq (R : CommRingCat.{u})
    (E J : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hE : E.IsStrictlyLE b) (hJ : J.IsStrictlyGE a)
    (hfree : ∀ i : ℤ, StacksDraft.PseudoCoherence.IsFiniteFree (E.X i)) :
    (affineHomComplexIso R E J a b hE hJ hfree).inv = affineHomComplexTildeMap R E J := by
  refine tildeHomComplex_hom_ext R E J _ _ fun n α p q hpq => ?_
  exact (affineHomComplexIso_inv_toOpen R E J a b hE hJ hfree n p q hpq α).trans
    (affineHomComplexTildeMap_toOpen R E J n p q hpq α).symm

/-- On a bounded-above complex of finite free modules and a bounded-below K-injective complex,
the canonical comparison is the inverse of the model comparison, followed by the comparison of
the derived sheafifications of the two complexes with the classes of their sheafifications. -/
private lemma affineDerivedTildeHomComparison_model_pseudo (R : CommRingCat.{u})
    (E J : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hE : E.IsStrictlyLE b) (hJ : J.IsStrictlyGE a) [J.IsKInjective]
    (hfree : ∀ i : ℤ, StacksDraft.PseudoCoherence.IsFiniteFree (E.X i)) :
    affineDerivedTildeHomComparison R (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj J) =
      (modelIso R E J a b hE hJ hfree).inv ≫
        ((specRHom R).hom.map
            ((tilde.functor R).mapDerivedCategoryFactors.hom.app E).op).app
          (DerivedCategory.Q.obj ((tildeCx R).obj J)) ≫
        ((specRHom R).hom.obj
            (op ((tildeDer R).obj (DerivedCategory.Q.obj E)))).map
          ((tilde.functor R).mapDerivedCategoryFactors.inv.app J) := by
  have := hE
  have : ∀ i : ℤ, Projective (E.X i) := fun i => projective_of_isFiniteFree (hfree i)
  have key : (modelIso R E J a b hE hJ hfree).inv =
      (((tildeDer R).map
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso E J).hom ≫
        ((tilde.functor R).mapDerivedCategoryFactors.app
          (CochainComplex.HomComplexR R E J)).hom) ≫
        DerivedCategory.Q.map (affineHomComplexTildeMap R E J)) ≫
        RingedSite.strictlyPerfectHomComparison (specSite R) (specRHom R)
          ((tildeCx R).obj E) ((tildeCx R).obj J) := by
    rw [← affineHomComplexIso_inv_eq R E J a b hE hJ hfree,
      ← StacksDraft.DerivedHom.projectiveHomComparison.iso_eq_homIso E J b]
    rfl
  rw [affineDerivedTildeHomComparison_app_of_isKInjective, key]
  simp only [Category.assoc]
  refine Eq.symm ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (_ ≫ ·) (Category.assoc _ _ _)

/-- **[Stacks, Tag 0A6H] (3)(a), for the canonical comparison.** Let `R` be a commutative ring,
`X = Spec R`, and let `K`, `L` be objects of `D(R)` with `K` pseudo-coherent and `L` bounded below.
Then the canonical comparison

`(RHom_R(K, L))~ ⟶ R𝓗om_{𝒪_X}(K̃, L̃)`

of `AlgebraicGeometry.affineDerivedTildeHomComparison` is an isomorphism. -/
@[stacks 0A6H "(3)(a) K pseudo-coherent and L bounded below: the canonical comparison is an \
isomorphism"]
theorem isIso_affineDerivedTildeHomComparison_of_isPseudoCoherent (R : CommRingCat.{u})
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hL : (DerivedCategory.TStructure.t).plus L) :
    IsIso (affineDerivedTildeHomComparison R K L) := by
  have := (plusRep R L hL).kinj
  let E := (pseudoRep R K hK).cx
  let J := (plusRep R L hL).cx
  let eK := (pseudoRep R K hK).iso
  let eL := (plusRep R L hL).iso
  have hm := affineDerivedTildeHomComparison_model_pseudo R E J (plusRep R L hL).bound
    (pseudoRep R K hK).bound (pseudoRep R K hK).le (plusRep R L hL).ge (pseudoRep R K hK).free
  have i₁ : IsIso (((specRHom R).hom.map
      ((tilde.functor R).mapDerivedCategoryFactors.hom.app E).op).app
        (DerivedCategory.Q.obj ((tildeCx R).obj J))) :=
    (((specRHom R).hom.mapIso ((tilde.functor R).mapDerivedCategoryFactors.app E).op).app
      _).isIso_hom
  have i₂ : IsIso (((specRHom R).hom.obj
      (op ((tildeDer R).obj (DerivedCategory.Q.obj E)))).map
        ((tilde.functor R).mapDerivedCategoryFactors.inv.app J)) :=
    (((specRHom R).hom.obj _).mapIso
      ((tilde.functor R).mapDerivedCategoryFactors.app J).symm).isIso_hom
  have h₀ : IsIso (affineDerivedTildeHomComparison R (DerivedCategory.Q.obj E)
      (DerivedCategory.Q.obj J)) := by
    rw [hm]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv _) (@IsIso.comp_isIso _ _ _ _ _ _ _ i₁ i₂)
  have h₁ : IsIso (affineDerivedTildeHomComparison R (DerivedCategory.Q.obj E) L) :=
    @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _
      ((tildeDer R).mapIso ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.mapIso
        (Iso.prod (Iso.refl _) eL))).isIso_hom
      (@IsIso.comp_isIso _ _ _ _ _ _ _ h₀
        (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
          (op ((tildeDer R).obj (DerivedCategory.Q.obj E)))).mapIso
            ((tildeDer R).mapIso eL)).isIso_hom)
      (affineDerivedTildeHomComparison_natural_right R (DerivedCategory.Q.obj E) eL.hom)
  exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _
    (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).mapIso
      ((tildeDer R).mapIso eK).op).app _).isIso_hom
    (@IsIso.comp_isIso _ _ _ _ _ _ _
      ((tildeDer R).mapIso ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.mapIso
        (Iso.prod eK.op (Iso.refl L)))).isIso_hom h₁)
    (affineDerivedTildeHomComparison_natural_left R eK.hom L).symm

end AlgebraicGeometry

end
