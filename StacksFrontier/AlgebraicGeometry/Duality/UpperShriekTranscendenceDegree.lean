module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekBounded
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingVanishing
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksFrontier.Topology.Noetherian.IrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Properties.Serre
import all StacksFrontier.AlgebraicGeometry.Properties.Serre

/-!
# The relative dualizing complex vanishes below minus the fibre transcendence degree

Let `S` be a Noetherian scheme and let `f : X ⟶ Y` be a morphism of `AlgebraicGeometry.FTS S`,
the category of schemes separated and of finite type over `S` of [Stacks, Tag 0F42].  Let
`x ∈ X` with image `y ∈ Y`.  Assume

1. `𝒪_{Y, y}` is Cohen–Macaulay, and
2. `trdeg_{κ(f ξ)} κ(ξ) ≤ r` for every generic point `ξ` of an irreducible component of `X`
   containing `x`.

This file proves the vanishing half of [Stacks, Tag 0E9V] (Lemma 48.21.4):

  `H^i(f^!𝒪_Y)_x ≠ 0  ⟹  -r ≤ i`,

where `f^!` is `Stacks.Duality.upperShriek` and `𝒪_Y` is
`Stacks.Duality.DerivedPushforward.derivedStructureSheaf`.  Hypothesis (2) is read with
`Stacks.Chow.residueTrdeg`, which *is* the transcendence degree of the residue-field extension
of `f` at a point.

## Main results

* `Stacks.Duality.neg_le_of_nontrivial_stalk_homology_upperShriek_of_residueTrdeg_le` — the
  vanishing half of **[Stacks, Tag 0E9V]**.
* `Stacks.Duality.TranscendenceDegreeBoundOn` — hypothesis (2) of [Stacks, Tag 0E9R] for a map
  of rings, and `Stacks.Duality.RelativeDualizingVanishesBelow` — clause (1) of that tag at the
  sharp bound `r`, the ring-theoretic input carried below.
* `Stacks.Duality.trdeg_le_residueTrdeg_spec` — the dictionary between the geometric reading of
  hypothesis (2) and the algebraic one, `Algebra.trdeg κ(φ⁻¹𝔮) κ(𝔮) ≤ r`.

## Relation to the source, and what is carried

*The source's proof.* The statement is local on `X`, so one chooses affine charts
`Spec Γ(X, U) → X` over `Spec Γ(Y, V) → Y` through `x`; on them `f^!𝒪_Y` is the relative
dualizing complex `ω^•_{Γ(X,U)/Γ(Y,V)}` by Remark [Stacks, Tag 0BV2]; and the bound is
[Stacks, Tag 0E9R].

*Two hypotheses are carried, both visible in the binders.*

* `h0BV2` is the affine-chart description of `f^!𝒪_Y`, in the *cofinal* shape: every open
  neighbourhood of `x` contains an affine chart carrying it.  That is clause (b) of
  [Stacks, Tag 0BV2], which the repository's Tag 0BV2
  (`Stacks.Duality.restrictedUpperShriekIsoOfOpenSquare`) does not claim because
  [Stacks, Tag 0AA1] is absent here; the library's [Stacks, Tag 0B6U] (a) carries it in the same
  shape, with `∀ x` in place of the cofinality in the neighbourhood.  Cofinality is what lets
  the chart be shrunk, which hypothesis (2) requires: a chart too large has generic points of
  components that do not specialize to `x`.  `h0BV2` asserts only an isomorphism and contains
  no degree bound.
* `h0E9R` is clause (1) of [Stacks, Tag 0E9R] at the sharp bound `r`.  What this library has,
  namely `subsingleton_localizedModule_homology_relativeDualizingComplex` in the namespace
  `Dualizing.PolynomialPresentation`, is the same vanishing at the *crude* bound given by the
  number of variables of the presentation, which is a weakening; the sharp bound is what the
  source extracts from the dimension formula [Stacks, Tag 0BAE], and it is not available here.

*What is proved here* is the whole geometric reduction: the shrinking of the chart so that
every generic point of one of its components specializes to `x`
(`exists_open_genericPoints_specialize` together with the transport of components along the
open immersion `Spec Γ(X, U) → X`), the identification of the residue transcendence degrees
across the chart square (through `Stacks.Chow.residueTrdeg_eq_of_comp_eq_comp`), the
Cohen–Macaulay transport `𝒪_{Y, y} ≅ Γ(Y, V)_𝔭`, and the stalk dictionary that carries the
conclusion back from the chart to `x`.

*The `(S_2)` clause of Tag 0E9V is NOT claimed here.*  Tag 0E9V also asserts that the stalk
`H^{-r}(f^!𝒪_Y)_x` satisfies Serre's condition `(S_2)` as an `𝒪_{X,x}`-module.  That clause
needs the `(S_2)` clause of [Stacks, Tag 0E9R], which this library claims only for a *surjective*
ring map, in
`StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingSerreSurjective`; for a general
finite type map the engine,
`StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingSerre`, still has one
identification standing — together with a module-level stalk dictionary, the
identification of the stalk of a cohomology sheaf with a localization *as a module over the
stalk ring*, not merely as an abelian group, which is what the dictionary below provides.
Nothing about `(S_2)` is stated below.

## Implementation notes

*The two derived categories.* `Stacks.Duality.upperShriek` lives on
`Stacks.Duality.quasiCoherentDerivedCategory`, read at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, while the derived category of a chart
ring is read at `CategoryTheory.HasDerivedCategory.standard`.  As in
`StacksFrontier/AlgebraicGeometry/Duality/UpperShriekBounded.lean` the two are never compared: the
derived universes keep them apart and the only traffic between them is through `h0BV2` and the
sheafification functor `AlgebraicGeometry.tilde.functor`.

*`IsLocallyNoetherian` on `X.left` and `Y.left`* is taken as an instance binder rather than
derived, because the Cohen–Macaulay hypothesis mentions a stalk and so needs the stalk to be
known Noetherian while the statement is being elaborated.  Both are consequences of
`[IsNoetherian S]` and the structure maps of `FTS S`, by
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, exactly as
[Stacks, Tag 0BV5] derives them inside its proof.

## References

* [Stacks Project, Tag 0E9V](https://stacks.math.columbia.edu/tag/0E9V)
* [Stacks Project, Tag 0E9R](https://stacks.math.columbia.edu/tag/0E9R)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
* [Stacks Project, Tag 0BV5](https://stacks.math.columbia.edu/tag/0BV5)
* [Stacks Project, Tag 0BAE](https://stacks.math.columbia.edu/tag/0BAE)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance 5000] HasDerivedCategory.standard
attribute [local instance 10000] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

universe u w

namespace Stacks.Duality

private theorem exists_open_genericPoints_specialize (X : Type u) [TopologicalSpace X]
    [NoetherianSpace X] (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∀ ξ ∈ U,
      closure {ξ} ∈ irreducibleComponents X → x ∈ closure {ξ} := by
  let B := {Z ∈ irreducibleComponents X | x ∉ Z}
  have hB : B.Finite := NoetherianSpace.finite_irreducibleComponents.subset
    fun _ hZ => hZ.1
  have hclosed : IsClosed (⋃₀ B) := by
    rw [Set.sUnion_eq_biUnion]
    exact hB.isClosed_biUnion fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  refine ⟨⟨(⋃₀ B)ᶜ, hclosed.isOpen_compl⟩, fun ⟨Z, hZ, hxZ⟩ => hZ.2 hxZ, ?_⟩
  intro ξ hξ hcomp
  by_contra hx
  exact hξ (Set.mem_sUnion.mpr ⟨closure {ξ}, ⟨hcomp, hx⟩,
    subset_closure (Set.mem_singleton ξ)⟩)

private theorem closure_image_genericPoint_mem_irreducibleComponents
    {X : Type u} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Topology.IsOpenEmbedding f) (ξ : X)
    (hξ : closure {ξ} ∈ irreducibleComponents X) :
    closure {f ξ} ∈ irreducibleComponents Y := by
  obtain ⟨Z, hZ, hle⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure {f ξ}) (isIrreducible_singleton.closure)
  have hξZ : ξ ∈ f ⁻¹' Z := hle (subset_closure (Set.mem_singleton _))
  have hpre := preimage_mem_irreducibleComponents hZ hf ⟨f ξ, hξZ, ⟨ξ, rfl⟩⟩
  have hsub : closure {ξ} ⊆ f ⁻¹' Z :=
    closure_minimal (Set.singleton_subset_iff.mpr hξZ)
      ((isClosed_of_mem_irreducibleComponents Z hZ).preimage hf.continuous)
  have heq : f ⁻¹' Z = closure {ξ} := (hξ.2 hpre.1 hsub).antisymm hsub
  have hZle : Z ⊆ closure {f ξ} := by
    rw [← closure_image_preimage_of_isPreirreducible f hf.isOpenMap Z
      ⟨ξ, hξZ⟩ hZ.1.2 (isClosed_of_mem_irreducibleComponents Z hZ), heq,
      closure_image_closure hf.continuous, Set.image_singleton]
  exact (hle.antisymm hZle) ▸ hZ

private theorem trdeg_le_of_commutativeSquare
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Nontrivial S] [Algebra R A] [Algebra S B]
    (e : R ≃+* S) (f : A →+* B) (hf : Function.Injective f)
    (h : (algebraMap S B).comp e.toRingHom = f.comp (algebraMap R A)) :
    Algebra.trdeg R A ≤ Algebra.trdeg S B := by
  unfold Algebra.trdeg
  exact ciSup_le' fun s =>
    (s.property.ringHom_of_comp_eq e f e.surjective hf h).cardinalMk_le_trdeg

/-- The residue field of `Spec R` at a point, read through
`AlgebraicGeometry.Scheme.Spec.residueFieldIso`, is natural in the ring map: the square
comparing `Spec φ` on residue fields with `Ideal.ResidueField.map` commutes. -/
private theorem spec_residueFieldIso_inv_naturality
    (R A : CommRingCat.{u}) (φ : R ⟶ A) (a : Spec A) :
    letI : a.asIdeal.IsPrime := a.isPrime
    letI : (((Spec.map φ).base a).asIdeal).IsPrime := ((Spec.map φ).base a).isPrime
    (Scheme.Spec.residueFieldIso R ((Spec.map φ).base a)).inv ≫
        (Spec.map φ).residueFieldMap a =
      CommRingCat.ofHom
          (Ideal.ResidueField.map ((Spec.map φ).base a).asIdeal a.asIdeal φ.hom rfl) ≫
        (Scheme.Spec.residueFieldIso A a).inv := by
  let _ : a.asIdeal.IsPrime := a.isPrime
  let _ : (((Spec.map φ).base a).asIdeal).IsPrime := ((Spec.map φ).base a).isPrime
  apply CommRingCat.hom_ext
  apply Ideal.ResidueField.ringHom_ext
  ext t
  have h : CommRingCat.ofHom (algebraMap R ((Spec.map φ).base a).asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso R ((Spec.map φ).base a)).inv ≫
          (Spec.map φ).residueFieldMap a =
      φ ≫ CommRingCat.ofHom (algebraMap A a.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso A a).inv := by
    rw [Scheme.Spec.algebraMap_residueFieldIso_inv_assoc,
      Scheme.Spec.algebraMap_residueFieldIso_inv]
    show (Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation ((Spec.map φ).base a) ≫
        (Spec.map φ).residueFieldMap a =
      φ ≫ (Scheme.ΓSpecIso A).inv ≫ (Spec A).Γevaluation a
    rw [Scheme.Γevaluation_naturality, Scheme.ΓSpecIso_inv_naturality_assoc]
  have hgoal := ConcreteCategory.congr_hom h t
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hgoal ⊢
  have hmap : (Ideal.ResidueField.map ((Spec.map φ).base a).asIdeal a.asIdeal φ.hom rfl)
        ((algebraMap R ((Spec.map φ).base a).asIdeal.ResidueField) t) =
      (algebraMap A a.asIdeal.ResidueField) (φ.hom t) :=
    Ideal.ResidueField.map_algebraMap _ _ _ _ t
  rw [hmap]
  exact hgoal

/-- The transcendence degree of the residue-field extension of the primes `φ⁻¹(𝔮) ⊆ 𝔮` of a
ring map is at most the residue transcendence degree of `Spec φ` at the corresponding point. -/
public theorem trdeg_le_residueTrdeg_spec
    (R A : CommRingCat.{u}) (φ : R ⟶ A) (a : Spec A) :
    letI : a.asIdeal.IsPrime := a.isPrime
    letI : (((Spec.map φ).base a).asIdeal).IsPrime := ((Spec.map φ).base a).isPrime
    letI : Algebra ((Spec.map φ).base a).asIdeal.ResidueField a.asIdeal.ResidueField :=
      (Ideal.ResidueField.map ((Spec.map φ).base a).asIdeal a.asIdeal φ.hom rfl).toAlgebra
    Algebra.trdeg ((Spec.map φ).base a).asIdeal.ResidueField a.asIdeal.ResidueField ≤
      Stacks.Chow.residueTrdeg (Spec.map φ) a := by
  let _ : a.asIdeal.IsPrime := a.isPrime
  let _ : (((Spec.map φ).base a).asIdeal).IsPrime := ((Spec.map φ).base a).isPrime
  let _ : Algebra ((Spec.map φ).base a).asIdeal.ResidueField a.asIdeal.ResidueField :=
    (Ideal.ResidueField.map ((Spec.map φ).base a).asIdeal a.asIdeal φ.hom rfl).toAlgebra
  let _ : Algebra ((Spec R).residueField ((Spec.map φ).base a)) ((Spec A).residueField a) :=
    ((Spec.map φ).residueFieldMap a).hom.toAlgebra
  exact trdeg_le_of_commutativeSquare
    (Scheme.Spec.residueFieldIso R ((Spec.map φ).base a)).symm.commRingCatIsoToRingEquiv
    (Scheme.Spec.residueFieldIso A a).inv.hom
    (Scheme.Spec.residueFieldIso A a).symm.commRingCatIsoToRingEquiv.injective
    (congrArg CommRingCat.Hom.hom (spec_residueFieldIso_inv_naturality R A φ a))

/-! ### Nontriviality transports along isomorphisms of abelian groups -/

/-! ### The stalk of an associated sheaf is a localization -/

/-! ### The stalk of the cohomology of a tilde model -/

section StalkModel

variable {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]

end StalkModel

/-! ### Localizing at a larger multiplicative set preserves vanishing -/

/-- If a module dies after localizing at `S`, it dies after localizing at any larger
multiplicative set. -/
private theorem subsingleton_localizedModule_of_le {A : Type u} [CommRing A] {M : Type u}
    [AddCommGroup M] [Module A M] {S T : Submonoid A} (hST : S ≤ T)
    (h : Subsingleton (LocalizedModule S M)) : Subsingleton (LocalizedModule T M) := by
  rw [LocalizedModule.subsingleton_iff] at h ⊢
  intro m
  obtain ⟨s, hs, hsm⟩ := h m
  exact ⟨s, hST hs, hsm⟩

/-! ### Minimal primes are the generic points of the irreducible components -/

/-- A prime of `A` is minimal exactly when its closure in `Spec A` is an irreducible
component; this is the direction used below. -/
private theorem closure_singleton_mem_irreducibleComponents_of_mem_minimalPrimes
    {A : CommRingCat.{u}} (a : Spec A) (h : a.asIdeal ∈ minimalPrimes A) :
    closure {a} ∈ irreducibleComponents (Spec A) := by
  have key : ∀ c : PrimeSpectrum A, c.asIdeal ∈ minimalPrimes A →
      closure {c} ∈ irreducibleComponents (PrimeSpectrum A) := by
    intro c hc
    rw [PrimeSpectrum.closure_singleton]
    exact PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents.mpr
      (by rwa [c.isPrime.isRadical.radical])
  exact key a h

/-! ### The hypotheses of Tag 0E9R, and its clause (1) as a carried statement -/

/-- **Hypothesis (2) of [Stacks, Tag 0E9R] for a ring map `φ : R ⟶ A`.** At every minimal prime
of `A` the residue-field extension over its contraction along `φ` has transcendence degree at
most `r`, read as `Stacks.Chow.residueTrdeg` of `Spec φ` at the corresponding point of `Spec A`.

`Stacks.Duality.trdeg_le_residueTrdeg_spec` identifies this with the purely algebraic reading,
`Algebra.trdeg κ(φ⁻¹𝔮) κ(𝔮) ≤ r`. -/
public def TranscendenceDegreeBoundOn {R A : CommRingCat.{u}} (φ : R ⟶ A) (r : ℕ) : Prop :=
  ∀ a : Spec A, a.asIdeal ∈ minimalPrimes A →
    Stacks.Chow.residueTrdeg (Spec.map φ) a ≤ (r : Cardinal)

/-- **Clause (1) of [Stacks, Tag 0E9R] at the bound `r`.** For a finite-type map of Noetherian
rings presented by `p`, a Cohen–Macaulay prime `𝔭` of the base and the transcendence-degree
bound `r`, the cohomology of the relative dualizing complex `ω^•_{A/R} = φ^!(R)` vanishes in
degrees below `-r` after localizing at the image of `𝔭`.

This is the ring-theoretic input of [Stacks, Tag 0E9V] which this library does not have:
`Dualizing.PolynomialPresentation.subsingleton_localizedModule_homology_relativeDualizingComplex`
proves the same vanishing only at the crude bound given by the number of variables of `p`, and
the sharp bound `r` is what the source extracts from the dimension formula [Stacks, Tag 0BAE].
It is therefore carried as a hypothesis. -/
public def RelativeDualizingVanishesBelow (r : ℕ) : Prop :=
  ∀ {R A : CommRingCat.{u}} (φ : R ⟶ A) [IsNoetherianRing R] [IsNoetherianRing A]
    (p : Dualizing.PolynomialPresentation φ.hom) (𝔭 : Ideal R) [𝔭.IsPrime],
    IsCohenMacaulayLocalRing (Localization.AtPrime 𝔭) →
    TranscendenceDegreeBoundOn φ r →
    ∀ i : ℤ, i < -(r : ℤ) →
      Subsingleton (LocalizedModule (Submonoid.map φ.hom 𝔭.primeCompl)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          (p.upperShriekFunctor.{u, u}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))))

/-- Hypothesis (2) of [Stacks, Tag 0E9R] on an affine chart `U → V` of `f`, from the residue
transcendence bound of `f` at the generic points of the components of `X` meeting `U`. -/
private theorem transcendenceDegreeBoundOn_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens}
    (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) (r : ℕ)
    (h : ∀ ξ ∈ U, closure {ξ} ∈ irreducibleComponents X →
      Stacks.Chow.residueTrdeg f ξ ≤ (r : Cardinal)) :
    TranscendenceDegreeBoundOn (f.appLE V U hUV) r := by
  intro a hac
  have hξc : closure {hU.fromSpec.base a} ∈ irreducibleComponents X :=
    closure_image_genericPoint_mem_irreducibleComponents hU.fromSpec.base
      hU.fromSpec.isOpenEmbedding a
      (closure_singleton_mem_irreducibleComponents_of_mem_minimalPrimes a hac)
  rw [← Stacks.Chow.residueTrdeg_eq_of_comp_eq_comp hU.fromSpec f (Spec.map (f.appLE V U hUV))
    hV.fromSpec (IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV).symm a]
  exact h _ (hU.range_fromSpec.subset ⟨a, rfl⟩) hξc

/-! ### Tag 0E9V, the vanishing bound -/

section Shriek

open DerivedPushforward

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S}
  [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left] (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- **Stacks Project, Tag 0E9V (Lemma 48.21.4), the vanishing.** In Situation
[Stacks, Tag 0F42], let `f : X ⟶ Y` be a morphism of `FTS S` and let `x ∈ X` with image
`y ∈ Y`.  Assume `𝒪_{Y, y}` is Cohen–Macaulay and that the residue transcendence degree of `f`
is at most `r` at every generic point of an irreducible component of `X` containing `x`.  Then

  `H^i(f^!𝒪_Y)_x ≠ 0  ⟹  -r ≤ i`.

Two hypotheses are carried.  `h0BV2` is the affine-chart description of `f^!𝒪_Y` of Remark
[Stacks, Tag 0BV2], in the cofinal shape: every open neighbourhood of `x` contains an affine
chart on which the description holds.  `h0E9R` is clause (1) of [Stacks, Tag 0E9R] at the sharp
bound `r`, which this library has only at the crude bound given by the number of variables of
the presentation.

Everything else is proved here: the reduction of the geometric hypotheses to the chart — the
Cohen–Macaulay transport `𝒪_{Y, y} ≅ Γ(Y, V)_𝔭`, the identification of the residue
transcendence degrees across the chart square, and the shrinking of the chart so that every
generic point of a component of it specializes to `x` — together with the stalk dictionary that
moves the conclusion back from the chart to `x`. -/
theorem neg_le_of_nontrivial_stalk_homology_upperShriek_of_residueTrdeg_le
    (x : X.left) (r : ℕ)
    (h0BV2 : ∀ W : X.left.Opens, x ∈ W → ∃ (U : X.left.Opens) (hU : IsAffineOpen U)
      (V : Y.left.Opens) (_hV : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V), x ∈ U ∧ U ≤ W ∧
      ∃ p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom,
        Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
            (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj) ≅
          (tilde.functor Γ(X.left, U) ⋙
            Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
              (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V))))
    (h0E9R : RelativeDualizingVanishesBelow.{u} r)
    (hCM : IsCohenMacaulayLocalRing (Y.left.presheaf.stalk (f.left.base x)))
    (htrdeg : ∀ ξ : X.left, closure {ξ} ∈ irreducibleComponents X.left → x ∈ closure {ξ} →
      Stacks.Chow.residueTrdeg f.left ξ ≤ (r : Cardinal))
    (i : ℤ)
    (hi : Nontrivial (((DerivedCategory.homologyFunctor X.left.Modules i).obj
      (((upperShriek f j).obj
        (derivedStructureSheaf Y.left)).obj)).presheaf.stalk x)) :
    -(r : ℤ) ≤ i := by
  by_contra! hcon
  have hSc : CompactSpace ((Functor.fromPUnit S).obj X.right) := inferInstanceAs (CompactSpace S)
  have hXc : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have hXN : AlgebraicGeometry.IsNoetherian X.left := ⟨⟩
  obtain ⟨W, hxW, hW⟩ := exists_open_genericPoints_specialize X.left x
  obtain ⟨U, hU, V, hV, hUV, hxU, hUW, p, ⟨e⟩⟩ := h0BV2 W hxW
  have hVn : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hUn : IsNoetherianRing Γ(X.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  -- Hypothesis (2) of Tag 0E9R on the chart.
  have htr := transcendenceDegreeBoundOn_appLE f.left hU hV hUV r
    fun ξ hξ hc => htrdeg ξ hc (hW ξ (hUW hξ) hc)
  -- The point of the chart over `x`, and the point of the base chart under it.
  let xu : U.toScheme := ⟨x, hxU⟩
  let q : Spec Γ(X.left, U) := hU.isoSpec.hom.base xu
  let b : Spec Γ(Y.left, V) := (Spec.map (f.left.appLE V U hUV)).base q
  have hqx : hU.fromSpec.base q = x := by
    have hcomp : hU.isoSpec.hom ≫ hU.fromSpec = U.ι := by
      rw [← IsAffineOpen.isoSpec_inv_ι hU, Iso.hom_inv_id_assoc]
    exact congrArg (fun g : U.toScheme ⟶ X.left => g.base xu) hcomp
  have hby : hV.fromSpec.base b = f.left.base x := by
    rw [← hqx]
    exact congrArg (fun g : Spec Γ(X.left, U) ⟶ Y.left => g.base q)
      (IsAffineOpen.SpecMap_appLE_fromSpec f.left hV hU hUV)
  -- Hypothesis (1) of Tag 0E9R on the chart: `Γ(Y, V)_𝔭 ≅ 𝒪_{Y, y}` is Cohen–Macaulay.
  have hbp : b.asIdeal.IsPrime := b.isPrime
  have hCM' : IsCohenMacaulayLocalRing (Localization.AtPrime b.asIdeal) := by
    have h1 : IsCohenMacaulayLocalRing (Y.left.presheaf.stalk (hV.fromSpec.base b)) :=
      (isCohenMacaulayLocalRing_iff_of_ringEquiv
        (Y.left.presheaf.stalkCongr (.of_eq hby)).commRingCatIsoToRingEquiv).mpr hCM
    exact (isCohenMacaulayLocalRing_iff_of_ringEquiv ((asIso (hV.fromSpec.stalkMap b) ≪≫
      Spec.stalkIso Γ(Y.left, V) b).commRingCatIsoToRingEquiv)).mp h1
  -- Clause (1) of Tag 0E9R on the chart, then localized further at the prime of `x`.
  have hqp : q.asIdeal.IsPrime := q.isPrime
  have hle : Submonoid.map (f.left.appLE V U hUV).hom b.asIdeal.primeCompl ≤
      q.asIdeal.primeCompl := by
    rintro _ ⟨s, hs, rfl⟩
    exact hs
  have hv' := subsingleton_localizedModule_of_le hle
    (h0E9R (f.left.appLE V U hUV) p b.asIdeal hCM' htr i hcon)
  -- The stalk dictionary carries the vanishing back to `x`.
  have hi' : Nontrivial (((DerivedCategory.homologyFunctor X.left.Modules i).obj
      (((upperShriek f j).obj
        (derivedStructureSheaf Y.left)).obj)).presheaf.stalk (U.ι.base xu)) := hi
  have hns := (nontrivial_stalk_homology_iff_nontrivial_localizedHomology hU e xu q rfl i).mp hi'
  exact not_subsingleton _ hv'

end Shriek

end Stacks.Duality

/-! ### Registration against Stacks 0E9V

Stacks 0E9V is **not** proved.  Of its two conclusions only the vanishing bound is established
here, and that conditionally; the `(S_2)` property of the stalk `H^{-r}(f^!𝒪_Y)_x` is not
claimed anywhere in this file.  The two carried hypotheses are clause (b) of Stacks 0BV2 — which
needs Stacks 0AA1, absent from this repository — and clause (1) of Stacks 0E9R at the *sharp*
bound, where the library proves only the crude bound.
-/

add_to_stacks 0E9V "THE VANISHING BOUND ONLY; the tag is NOT proved. Proved: in the stated
situation, if the stalk at x of H^i(f^! O_Y) is nontrivial then -r <= i. NOT PROVED: the second
conclusion, that the stalk H^{-r}(f^! O_Y)_x is (S_2) as an O_{X,x}-module -- nothing about (S_2)
is stated in this file, and the module-level stalk dictionary it needs does not exist in the
library (only the abelian-group version does). TWO HYPOTHESES ARE CARRIED, neither dischargeable
here. h0BV2 is clause (b) of Stacks 0BV2, the affine formula for f^! O_Y, which needs Stacks 0AA1
(f^! = Lf^*[1] for A^1_V -> V), absent from this repository; the library's Stacks 0BV2 explicitly
declines clause (b). NOTE IT IS CARRIED IN A STRENGTHENED FORM relative to the library's Stacks 0BV5
and 0B6U, which take one chart: here it must be COFINAL in neighbourhoods of x, which is what
permits the chart shrinking. h0E9R is clause (1) of Stacks 0E9R at the SHARP bound r, whereas the
library's subsingleton_localizedModule_homology_relativeDualizingComplex gives only the crude
bound (the number of variables); the sharp bound needs the dimension formula of Stacks 0BAE via
the duality formula of Stacks 0E9L localized at a maximal ideal. Stacks 0E9L itself is proved in
general as Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_natIso_dualizingDerivedHom;
the passage to the localization is the base change of Stacks 0BZV, conditional in this library."
  Stacks.Duality.neg_le_of_nontrivial_stalk_homology_upperShriek_of_residueTrdeg_le

end
