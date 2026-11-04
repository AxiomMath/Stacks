module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.TorAmplitude.Composition

/-!
# Tor amplitude modulo a nilpotent ideal

Let `R' → R` be a surjective map of commutative rings whose kernel is a nilpotent ideal, let `K`
be an object of `D(R')` and let `L` be derived extension of scalars along `R' → R`. Then `L.obj K`
has Tor amplitude in `[a, b]` if and only if `K` does. This is the dévissage behind Stacks 0H75.

The tag itself is not here. Everything in this file reads Tor amplitude off
`CochainComplex.DerivedTensor.DerivedTensorProductGeneral`, which is a richer datum than the
three fields Stacks 0652 uses, so these statements are weaker than the source's. They are the
internal helpers; Stacks 0H75 is
`StacksDraft.TorAmplitude.hasTorAmplitudeIn_derivedExtensionScalars_certified_iff` in
`StacksFrontier.Homology.TorAmplitude.NilpotentCertified`, which is quantified over
`StacksDraft.TorAmplitude.CertifiedDerivedTensoring` on each ring and derives the results here by
scalar-lifting both rings into the common module universe.

## Main results

* `StacksDraft.TorAmplitude.hasTorAmplitudeIn_derivedExtensionScalars_iff`: the general form, with
  the universe of `R'`, the universe of `R` and the universe of the module carriers independent,
  as in the source statement. Untagged: it assumes the richer derived-tensor datum.
* `StacksDraft.TorAmplitude.hasTorAmplitudeIn_derivedExtensionScalars_iff_sameUniverse`: the same
  statement with all three universes equal. It is the `u = v = w` case of the endpoint and carries
  no tag; it is what the one-sided exports below are phrased against.
* `StacksDraft.TorAmplitude.hasTorAmplitudeAbove_of_derivedExtensionScalars` and
  `StacksDraft.TorAmplitude.isLE_of_hasTorAmplitudeAbove_derivedExtensionScalars`: the one-sided
  form of the same result, for consumers — Stacks 09AR and its dependents — that have an upper
  bound and no lower bound, so cannot supply the `a` of the two-sided statement.
* `StacksDraft.TorAmplitude.isZero_derivedTensor_single_of_pow_smul_top_eq_bot`: the nilpotent
  dévissage itself, degreewise in the cohomological degree and with no bound of either kind. This
  is the reusable engine; anything the one-sided exports do not cover should be assembled from it
  rather than re-derived.
* `StacksDraft.TorAmplitude.hasTorAmplitudeIn_iff_of_isNilpotent_ker`: the dévissage packaged over
  an *assumed* projection isomorphism between two unrelated objects. This is the helper the
  endpoint is built from; it is strictly weaker and carries no tag.

## Implementation notes

### How derived extension of scalars is expressed

`L` is not constructed here: as in the source statement, it is quantified over, together with a
comparison `Q ⋙ L ⟶ (R ⊗_{R'} -) ⋙ Q` and the `Functor.IsLeftDerivedFunctor` certificate making
`L` the total left derived functor of termwise extension of scalars along `Q`. That certificate
pins `L` down up to unique isomorphism, so the endpoint is a statement about *the* derived base
change, not about an arbitrary functor.

Both Tor amplitudes are taken against certified derived tensor bifunctors in the sense of Stacks
064M and 0BYI, as in `StacksFrontier.Homology.TorAmplitude.Composition`; see that module's docstring
for why the certified triple of Stacks 0652 cannot state a condition on the second variable of the
bifunctor at anything but a module. The source statement quantifies over its certified tensorings
in the same way.

### The projection formula is proved, not assumed

The two sides are related by the projection formula: for every `R`-module `M`, the restriction to
`R'` of `(L.obj K) ⊗_R^L M[0]` is `K ⊗_{R'}^L (M as an R'-module)[0]`.
`nonempty_projectionFormulaIso` derives it from the certificate for `L`, as follows.

Choose a K-flat resolution `P` of a representative of `K` (Stacks 06Y4). The comparison of any
total left derived functor of termwise extension of scalars is invertible at a K-flat complex
(Stacks 06Y6,
`CochainComplex.DerivedTensor.KFlatDerived.isIso_extensionCounit_app_of_kFlat`), so
`L.obj K ≅ Q (R ⊗_{R'} P)`; this is the step that a K-projective resolution cannot supply, since
an unbounded object of `D(R')` has no bounded above projective representative. The complex
`R ⊗_{R'} P` is again K-flat (Stacks 06Y1, `kFlat_baseChange`), and choosing a K-flat resolution
`S` of `M[0]` over `R`, the bifunctor's own comparison at a pair of K-flat complexes computes
`(L.obj K) ⊗_R^L M[0] ≅ Q ((R ⊗_{R'} P) ⊗_R S)`. Restricting scalars and applying the
complex-level projection formula (`baseChangeTensorIso`, Stacks 06Y1) — with the Koszul braiding
of complexes on each side to put the base-changed factor where that isomorphism expects it —
identifies the result with `Q (P ⊗_{R'} S|_{R'})`. Finally `S|_{R'}` is a resolution of
`(M as an R'-module)[0]` which need not be K-flat over `R'`, so it is itself resolved by a K-flat
`S''`; tensoring with the K-flat `P` preserves that quasi-isomorphism
(`quasiIso_tensorLeft_map`), and the bifunctor's comparison over `R'` computes
`K ⊗_{R'}^L (M as an R'-module)[0] ≅ Q (P ⊗_{R'} S'')`.

### Universes

The source constrains no relation between the universe of `R'`, the universe of `R` and the
universe of the module carriers, and the endpoint is stated that way: `R' : Type u`, `R : Type v`,
and both rings' modules read in `ModuleCat.{max u v w}`. Neither ring is `ULift`ed — the statement
is about the source's own rings.

Two layers are needed for that. Tor amplitude cannot be
`Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified T)`, which is defined
for `CochainComplex.DerivedTensor.DerivedTensorProduct R` and therefore puts the modules in the
universe of `R` (`DObj R = DerivedCategory (ModuleCat.{u} R)`); two rings in different universes
would then give two different module categories with nothing for `restrictScalars` to mediate. It
is instead `Stacks.TorAmplitudeTriangle.HasTorAmplitudeInLarge (derivedTensoringOfCertifiedGeneral
T)`, against `CochainComplex.DerivedTensor.DerivedTensorProductGeneral`, whose module universe is
free. And the change-of-scalars inputs are taken at two independent ring universes:
`CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars` for Stacks 06Y1 and
`CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso` for the complex-level projection
formula, in place of the one-universe `kFlat_baseChange` and `baseChangeTensorIso`.

`TotalTensorComplex.cochainComplex_symmetricMonoidalCategory` is *not* needed and is not used in
the general section: the interchange of the two tensor factors is wanted at two specific pairs of
complexes, not as the braiding of a symmetric monoidal structure, and
`CochainComplex.DerivedTensor.tensorFlipIso` supplies exactly that isomorphism above the ring's
universe. The one-universe layer still uses the symmetric monoidal structure, because that is
what the one-sided exports were written against.

The one-universe and general layers duplicate five lemmas apiece and are a dedup target; the
general layer subsumes the one-universe endpoint, which is its `u = v = w` case, but the one-sided
exports and `hasTorAmplitudeIn_iff_of_isNilpotent_ker` are stated at one universe and would have
to be restated at the free module universe first.

### The proof of the dévissage

The direction "`K'` has Tor amplitude in `[a, b]` ⟹ `K` does" is immediate from the projection
formula, because restriction of scalars neither creates nor destroys a vanishing cohomology module
(`isZero_homology_mapDerivedCategory_iff`); it does not need Stacks 066L.

The converse is the nilpotent dévissage. The projection formula gives the Tor-amplitude bound for
`K'` against every `R'`-module of the form `M` for `M` an `R`-module, that is, against every
`R'`-module killed by `I = Ker(R' → R)`. An arbitrary `R'`-module `N` is killed by `I^n` for the
`n` with `I^n = 0`, and one descends along the filtration by `I^t N` using the short exact
sequences `0 → I N → N → N / I N → 0`: the outer terms are handled by induction and by the
`I`-killed case, and the middle one follows because the single-object triangle of a short exact
sequence (`ShortComplex.ShortExact.singleTriangle`) is distinguished and `K' ⊗_{R'}^L -` is exact
in its second variable, so the long exact cohomology sequence applies. That last step is Stacks
0655 (2) read in the *second* variable of the bifunctor, which is why
`Stacks.TorAmplitudeTriangle.DerivedTensoring` — a datum in the first variable only — cannot be
used for it.

Surjectivity and nilpotence of the kernel are used only in this converse direction; the forward
direction is the projection formula alone, which is Stacks 066L for the certificate at hand and
holds for any ring map.

## References

* [Stacks Project, Tag 0H75](https://stacks.math.columbia.edu/tag/0H75)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace StacksDraft.TorAmplitude

universe u v w

attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

@[expose] public section

/-! ### Restriction of scalars neither creates nor destroys vanishing cohomology -/

/-- Restriction of scalars along a ring map between rings in two independent universes preserves
and reflects the vanishing of a cohomology module of an object of the derived category, along any
isomorphism of the restriction with another object: on complexes it changes neither the underlying
groups nor the maps, so the short complex computing cohomology in a degree is exact on one side
exactly when it is on the other. -/
private lemma isZero_homology_iff_of_iso_mapDerivedCategory {R' : Type u} {R : Type v}
    [CommRing R'] [CommRing R] (f : R' →+* R) {X : DerivedCategory (ModuleCat.{w} R)}
    {Y : DerivedCategory (ModuleCat.{w} R')}
    (e' : (ModuleCat.restrictScalars.{w} f).mapDerivedCategory.obj X ≅ Y) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} R') i).obj Y) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj X) := by
  refine ((DerivedCategory.homologyFunctor (ModuleCat.{w} R') i).mapIso e').isZero_iff.symm.trans ?_
  set E := DerivedCategory.Q.objPreimage X
  let e : DerivedCategory.Q.obj E ≅ X := DerivedCategory.Q.objObjPreimageIso X
  let U := ModuleCat.restrictScalars.{w} f
  let eA : (DerivedCategory.homologyFunctor (ModuleCat.{w} R') i).obj
        (U.mapDerivedCategory.obj X) ≅
      ((U.mapHomologicalComplex (ComplexShape.up ℤ)).obj E).homology i :=
    (DerivedCategory.homologyFunctor (ModuleCat.{w} R') i).mapIso
        ((U.mapDerivedCategory.mapIso e).symm ≪≫ U.mapDerivedCategoryFactors.app E) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{w} R') i).app _
  let eB : (DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj X ≅ E.homology i :=
    (DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{w} R) i).app E
  rw [eA.isZero_iff, eB.isZero_iff,
    ← HomologicalComplex.exactAt_iff_isZero_homology,
    ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff, HomologicalComplex.exactAt_iff,
    ShortComplex.moduleCat_exact_iff, ShortComplex.moduleCat_exact_iff]
  rfl

/-! ### Stacks 0655 (2) in the second variable of the bifunctor -/

/-- For an exact endofunctor `F` of the derived category (a certified derived tensor product with
a fixed first variable) and a short exact sequence of modules, a vanishing cohomology module of `F`
applied to the two outer terms forces the vanishing of the corresponding one for the middle term.

The single-object triangle of the short exact sequence is distinguished, `F` preserves it, and the
long exact cohomology sequence of the image triangle has the desired module between two zeros. -/
private lemma isZero_homology_single_X₂ {A : Type u} [CommRing A]
    (F : DerivedCategory (ModuleCat.{w} A) ⥤ DerivedCategory (ModuleCat.{w} A))
    [F.CommShift ℤ] [F.IsTriangulated] (S : ShortComplex (ModuleCat.{w} A))
    (hS : S.ShortExact) (i : ℤ)
    (h₁ : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} A) i).obj
      (F.obj ((DerivedCategory.singleFunctor (ModuleCat.{w} A) 0).obj S.X₁))))
    (h₃ : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} A) i).obj
      (F.obj ((DerivedCategory.singleFunctor (ModuleCat.{w} A) 0).obj S.X₃)))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} A) i).obj
      (F.obj ((DerivedCategory.singleFunctor (ModuleCat.{w} A) 0).obj S.X₂))) := by
  have hex := DerivedCategory.HomologySequence.exact₂
    (F.mapTriangle.obj hS.singleTriangle)
    (F.map_distinguished _ hS.singleTriangle_distinguished) i
  exact hex.isZero_of_both_zeros (h₁.eq_zero_of_src _) (h₃.eq_zero_of_tgt _)


/-! ### Modules killed by the kernel are modules over the quotient -/

section Descent

/-- Restriction of scalars along a ring map preserves and reflects the vanishing of a cohomology
module of an object of the derived category: on complexes it changes neither the underlying groups
nor the maps, so the short complex computing cohomology in a degree is exact on one side exactly
when it is on the other. -/
private lemma isZero_homology_mapDerivedCategory_iff {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) (X : DerivedCategory (ModuleCat.{u} R)) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).obj
        ((ModuleCat.restrictScalars f).mapDerivedCategory.obj X)) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj X) := by
  set E := DerivedCategory.Q.objPreimage X
  let e : DerivedCategory.Q.obj E ≅ X := DerivedCategory.Q.objObjPreimageIso X
  let U := ModuleCat.restrictScalars f
  let eA : (DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).obj
        (U.mapDerivedCategory.obj X) ≅
      ((U.mapHomologicalComplex (ComplexShape.up ℤ)).obj E).homology i :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).mapIso
        ((U.mapDerivedCategory.mapIso e).symm ≪≫ U.mapDerivedCategoryFactors.app E) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R') i).app _
  let eB : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj X ≅ E.homology i :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app E
  rw [eA.isZero_iff, eB.isZero_iff,
    ← HomologicalComplex.exactAt_iff_isZero_homology,
    ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff, HomologicalComplex.exactAt_iff,
    ShortComplex.moduleCat_exact_iff, ShortComplex.moduleCat_exact_iff]
  rfl


/-- The quotient of an `R'`-module by `Ker f` times it is a module over the target ring, through
the isomorphism `R' / Ker f ≅ R`. The two rings and the module carrier live in three independent
universes, which is what the Stacks 0H75 endpoint below needs. -/
private noncomputable instance quotientModule {R' : Type u} {R : Type v} {M : Type w}
    [CommRing R'] [CommRing R]
    [AddCommGroup M] [Module R' M] (f : R' →+* R) [Fact (Function.Surjective f)] :
    Module R (M ⧸ ((RingHom.ker f) • (⊤ : Submodule R' M))) :=
  Module.compHom _ ((RingHom.quotientKerEquivOfSurjective
    (Fact.out (p := Function.Surjective f))).symm : R →+* (R' ⧸ RingHom.ker f))

/-- Restricting that action along `f` gives back the original `R'`-action. -/
private lemma quotient_smul {R' : Type u} {R : Type v} {M : Type w} [CommRing R'] [CommRing R]
    [AddCommGroup M] [Module R' M] (f : R' →+* R) [Fact (Function.Surjective f)]
    (r : R') (x : M) :
    (f r) • (Submodule.Quotient.mk x : M ⧸ ((RingHom.ker f) • (⊤ : Submodule R' M))) =
      Submodule.Quotient.mk (r • x) := by
  have h1 : (f r) • (Submodule.Quotient.mk x :
      M ⧸ ((RingHom.ker f) • (⊤ : Submodule R' M))) =
      ((RingHom.quotientKerEquivOfSurjective
        (Fact.out (p := Function.Surjective f))).symm (f r)) •
          (Submodule.Quotient.mk x) := rfl
  rw [h1, show (RingHom.quotientKerEquivOfSurjective
      (Fact.out (p := Function.Surjective f))).symm (f r) =
      Ideal.Quotient.mk (RingHom.ker f) r by
    apply (RingHom.quotientKerEquivOfSurjective
      (Fact.out (p := Function.Surjective f))).injective
    rw [RingEquiv.apply_symm_apply]
    rfl]
  rfl

/-- **The nilpotent dévissage for an exact functor.** Let `f : R' → R` be surjective with kernel `I`
and let `F` be an exact endofunctor of `D(R')`. If `H^i(F N[0])` vanishes for every `R'`-module `N`
of the form `M` restricted along `f`, that is, for every `R'`-module killed by `I`, then it vanishes
for every `R'`-module killed by `I ^ (n + 1)`.

The `I`-killed `R'`-modules are restrictions of `R`-modules, and the induction on `n` runs along the
short exact sequences `0 → I N → N → N / I N → 0`, the middle term being handled by
`isZero_homology_single_X₂`. -/
private theorem isZero_homology_single_of_pow_smul_top_eq_bot {R' : Type u} {R : Type v}
    [CommRing R'] [CommRing R] (f : R' →+* R) (hf : Function.Surjective f)
    (F : DerivedCategory (ModuleCat.{w} R') ⥤ DerivedCategory (ModuleCat.{w} R'))
    [F.CommShift ℤ] [F.IsTriangulated] (i : ℤ)
    (h : ∀ M : ModuleCat.{w} R,
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} R') i).obj
        (F.obj ((DerivedCategory.singleFunctor (ModuleCat.{w} R') 0).obj
          ((ModuleCat.restrictScalars f).obj M)))))
    (n : ℕ) :
    ∀ N : ModuleCat.{w} R',
      (RingHom.ker f) ^ (n + 1) • (⊤ : Submodule R' (N : Type w)) = ⊥ →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} R') i).obj
          (F.obj ((DerivedCategory.singleFunctor (ModuleCat.{w} R') 0).obj N))) := by
  let _ : Fact (Function.Surjective f) := ⟨hf⟩
  -- An `R'`-module `N` with `I • N = 0` is the restriction of scalars of an `R`-module.
  have hkilled : ∀ N : ModuleCat.{w} R',
      (RingHom.ker f) • (⊤ : Submodule R' (N : Type w)) = ⊥ →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} R') i).obj
          (F.obj ((DerivedCategory.singleFunctor (ModuleCat.{w} R') 0).obj N))) := by
    intro N hN
    set MB : ModuleCat.{w} R :=
      ModuleCat.of R ((N : Type w) ⧸ ((RingHom.ker f) • (⊤ : Submodule R' (N : Type w))))
    let e₁ : (((ModuleCat.restrictScalars f).obj MB : ModuleCat.{w} R') : Type w) ≃ₗ[R']
        ((N : Type w) ⧸ ((RingHom.ker f) • (⊤ : Submodule R' (N : Type w)))) :=
      { toFun := id
        invFun := id
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := by
          intro r x
          refine Quotient.inductionOn x ?_
          intro y
          exact quotient_smul f r y }
    let e₂ : ((N : Type w) ⧸ ((RingHom.ker f) • (⊤ : Submodule R' (N : Type w)))) ≃ₗ[R']
        (N : Type w) := Submodule.quotEquivOfEqBot _ hN
    let e : (ModuleCat.restrictScalars f).obj MB ≅ N := (e₁.trans e₂).toModuleIso
    exact (h MB).of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{w} R') i).mapIso
      (F.mapIso ((DerivedCategory.singleFunctor (ModuleCat.{w} R') 0).mapIso e.symm)))
  induction n with
  | zero =>
    intro N hN
    exact hkilled N (by simpa using hN)
  | succ n ih =>
    intro N hN
    set I := RingHom.ker f
    set P : Submodule R' (N : Type w) := I • (⊤ : Submodule R' (N : Type w)) with hP
    -- The short exact sequence `0 → P → N → N / P → 0`.
    let S : ShortComplex (ModuleCat.{w} R') :=
      ShortComplex.mk (ModuleCat.ofHom P.subtype) (ModuleCat.ofHom P.mkQ) (by ext x; simp)
    have hS : S.ShortExact := ShortComplex.ShortExact.mk'
      (by
        rw [ShortComplex.moduleCat_exact_iff]
        intro x hx
        exact (LinearMap.exact_subtype_mkQ P x).mp hx)
      ((ModuleCat.mono_iff_injective _).2 Subtype.coe_injective)
      ((ModuleCat.epi_iff_surjective _).2 P.mkQ_surjective)
    refine isZero_homology_single_X₂ F S hS i ?_ ?_
    · -- `P` is killed by `I ^ (n + 1)`.
      refine ih (ModuleCat.of R' P) ?_
      refine le_antisymm (Submodule.smul_le.2 ?_) bot_le
      intro r hr x _
      rw [Submodule.mem_bot]
      have hx : r • (x : (N : Type w)) ∈ I ^ (n + 1) • P := Submodule.smul_mem_smul hr x.2
      have hPeq : I ^ (n + 1) • P = ⊥ := by
        rw [hP, ← Submodule.mul_smul, ← pow_succ, hN]
      exact Submodule.coe_eq_zero.mp ((Submodule.mem_bot R').mp (hPeq.le hx))
    · -- `N / P` is killed by `I`.
      refine hkilled (ModuleCat.of R' ((N : Type w) ⧸ P)) ?_
      refine le_antisymm (Submodule.smul_le.2 ?_) bot_le
      intro r hr y _
      rw [Submodule.mem_bot]
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective P y
      exact (Submodule.Quotient.mk_eq_zero P).2
        (Submodule.smul_mem_smul hr Submodule.mem_top)

/-- The same vanishing for every `R'`-module `N`, when the kernel of `f` is nilpotent. -/
private theorem isZero_homology_single_of_isNilpotent_ker {R' : Type u} {R : Type v}
    [CommRing R'] [CommRing R] (f : R' →+* R) (hf : Function.Surjective f)
    (hnil : IsNilpotent (RingHom.ker f))
    (F : DerivedCategory (ModuleCat.{w} R') ⥤ DerivedCategory (ModuleCat.{w} R'))
    [F.CommShift ℤ] [F.IsTriangulated] (i : ℤ)
    (h : ∀ M : ModuleCat.{w} R,
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} R') i).obj
        (F.obj ((DerivedCategory.singleFunctor (ModuleCat.{w} R') 0).obj
          ((ModuleCat.restrictScalars f).obj M)))))
    (N : ModuleCat.{w} R') :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} R') i).obj
      (F.obj ((DerivedCategory.singleFunctor (ModuleCat.{w} R') 0).obj N))) := by
  obtain ⟨n, hn⟩ := hnil
  refine isZero_homology_single_of_pow_smul_top_eq_bot f hf F i h n N ?_
  rw [pow_succ, Submodule.mul_smul, hn]
  simp

end Descent

/-! ### Stacks 0H75 -/

section Nilpotent

variable {R' R : Type u} [CommRing R'] [CommRing R] (f : R' →+* R)

/-- **The nilpotent dévissage.** Let `f : R' → R` be surjective with kernel `I`, let `T'` be a
certified derived tensor bifunctor on `D(R')` and let `K'` be an object of `D(R')`. Fix a single
cohomological degree `i`, and suppose `H^i(K' ⊗_{R'}^L N[0])` vanishes for every `R'`-module `N`
of the form `M` restricted along `f`, that is, for every `R'`-module killed by `I`. Then it
vanishes for every `R'`-module killed by `I ^ (n + 1)`.

The proof is induction on `n` along the short exact sequences `0 → I N → N → N / I N → 0`: the
outer terms are handled by the inductive hypothesis and by the `I`-killed case, and the middle one
by the long exact cohomology sequence of the distinguished single-object triangle, using exactness
of `K' ⊗_{R'}^L -` in its second variable.

This is the engine of Stacks 0H75, and it is stated **one degree at a time and with no lower
bound**, which is what makes it reusable: combined with `I` nilpotent, taking `N` to be an
arbitrary `R'`-module gives the hard direction of 0H75, while taking `N := R'` and using the right
unitor of `T'` gives `H^i(K') = 0`. Consumers that have only an upper bound — no integer `a` to
feed the two-sided `Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn` — should use this lemma, or the
one-sided exports `hasTorAmplitudeAbove_of_derivedExtensionScalars` and
`isLE_of_hasTorAmplitudeAbove_derivedExtensionScalars` built from it, rather than either of the
two-sided statements. -/
public theorem isZero_derivedTensor_single_of_pow_smul_top_eq_bot
    (hf : Function.Surjective f)
    (T' : CochainComplex.DerivedTensor.DerivedTensorProduct R')
    (K' : DerivedCategory (ModuleCat.{u} R')) (i : ℤ)
    (h : ∀ M : ModuleCat.{u} R,
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).obj
        ((T'.tensor.obj K').obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj
          ((ModuleCat.restrictScalars f).obj M)))))
    (n : ℕ) :
    ∀ N : ModuleCat.{u} R',
      (RingHom.ker f) ^ (n + 1) • (⊤ : Submodule R' (N : Type u)) = ⊥ →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).obj
          ((T'.tensor.obj K').obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj N))) :=
    isZero_homology_single_of_pow_smul_top_eq_bot f hf (T'.tensor.obj K') i h n

/-- **The nilpotent dévissage over an assumed projection isomorphism. This is not Stacks 0H75.**

Let `R' → R` be a surjective map of commutative rings whose kernel is a nilpotent ideal, let `K'`
be an object of `D(R')` and `K` an object of `D(R)`, and suppose the two are related by the
projection isomorphism `projection`: for every `R`-module `M`, the restriction to `R'` of
`K ⊗_R^L M[0]` is `K' ⊗_{R'}^L (M as an R'-module)[0]`. Then, for every finite interval `[a, b]`,
`K` has Tor amplitude in `[a, b]` if and only if `K'` does.

Stacks 0H75 is the same equivalence for `K'` and its derived base change `L.obj K'`, where `L` is
certified as the total left derived functor of termwise extension of scalars, and there the
projection isomorphism is *proved* rather than assumed. Since `projection` here is a hypothesis
relating two otherwise unrelated objects, and it carries the whole forward transfer, this statement
is strictly weaker and deliberately carries no tag. It is the dévissage that
`hasTorAmplitudeIn_derivedExtensionScalars_iff_sameUniverse` consumes, after
`nonempty_projectionFormulaIso` discharges `projection` from the certificate for `L`; the tag
endpoint `hasTorAmplitudeIn_derivedExtensionScalars_iff`, which leaves the three universes
independent, consumes `hasTorAmplitudeInLarge_iff_of_isNilpotent_ker` in the same way.

The derived tensor products are certified bifunctors in the sense of Stacks 064M and 0BYI; that
quantification matches the source and is not the reason the tag is withheld. -/
public theorem hasTorAmplitudeIn_iff_of_isNilpotent_ker
    (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f))
    (T' : CochainComplex.DerivedTensor.DerivedTensorProduct R')
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (K' : DerivedCategory (ModuleCat.{u} R')) (K : DerivedCategory (ModuleCat.{u} R))
    (projection : ∀ M : ModuleCat.{u} R,
      (ModuleCat.restrictScalars f).mapDerivedCategory.obj
          ((T.tensor.obj K).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) ≅
        (T'.tensor.obj K').obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj
          ((ModuleCat.restrictScalars f).obj M)))
    (a b : ℤ) :
    Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified T) K a b ↔
      Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified T') K' a b := by
  constructor
  · intro hK N i hi
    exact isZero_homology_single_of_isNilpotent_ker f hf hnil (T'.tensor.obj K') i
      (fun M => (isZero_homology_iff_of_iso_mapDerivedCategory f (projection M) i).2
        (hK M i hi)) N
  · intro hK' M i hi
    exact (isZero_homology_iff_of_iso_mapDerivedCategory f (projection M) i).1
      (hK' ((ModuleCat.restrictScalars f).obj M) i hi)

end Nilpotent

/-- **The projection formula for derived extension of scalars, at three independent universes.**
Let `f : R' → R` be a map of commutative rings with `R'` in `Type u` and `R` in `Type v`, let `L`
be certified as the total left derived functor of termwise extension of scalars along `f` on
modules with carriers in `Type (max u v w)`, let `K` be an object of `D(R')` and `M` an
`R`-module. Then the restriction to `R'` of `(L.obj K) ⊗_R^L M[0]` is
`K ⊗_{R'}^L (M as an R'-module)[0]`.

This is `nonempty_projectionFormulaIso` with the universes freed, and the same argument. A K-flat
resolution `P` of a representative of `K` gives `L.obj K ≅ Q (R ⊗_{R'} P)` because the comparison
of a total left derived functor of extension of scalars is invertible at a K-flat complex
(Stacks 06Y6,
`CochainComplex.DerivedTensor.KFlatDerived.isIso_extensionCounit_app_of_kFlat`, which is already
stated at two independent ring universes). The base change `R ⊗_{R'} P` is again K-flat
(Stacks 06Y1, `CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars`), so with a K-flat
resolution `S` of `M[0]` over `R` the bifunctor's K-flat comparison computes
`(L.obj K) ⊗_R^L M[0] ≅ Q ((R ⊗_{R'} P) ⊗_R S)`; the complex-level projection formula
`CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso` identifies its restriction with
`Q (P ⊗_{R'} S|_{R'})`, the two tensor factors being interchanged on each side by
`CochainComplex.DerivedTensor.tensorFlipIso`. Finally `S|_{R'}` need not be K-flat over `R'`, so
it is itself resolved by a K-flat `S''`; tensoring with the K-flat `P` preserves that
quasi-isomorphism, and the bifunctor's comparison over `R'` computes
`K ⊗_{R'}^L (M as an R'-module)[0] ≅ Q (P ⊗_{R'} S'')`.

The conclusion is `Nonempty` of the isomorphism because the resolutions it is built from are only
available through existential statements. -/
private lemma nonempty_projectionFormulaIsoLarge {R' : Type u} {R : Type v}
    [CommRing R'] [CommRing R] (f : R' →+* R)
    (L : DerivedCategory (ModuleCat.{max u v w} R') ⥤ DerivedCategory (ModuleCat.{max u v w} R))
    (comparison : DerivedCategory.Q (C := ModuleCat.{max u v w} R') ⋙ L ⟶
      CochainComplex.extendScalarsLarge.{w, u, v} f ⋙
        DerivedCategory.Q (C := ModuleCat.{max u v w} R))
    [L.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max u v w} R') (ComplexShape.up ℤ))]
    (T' : CochainComplex.DerivedTensor.DerivedTensorProductGeneral.{u, max v w} R')
    (T : CochainComplex.DerivedTensor.DerivedTensorProductGeneral.{v, max u w} R)
    (K : DerivedCategory (ModuleCat.{max u v w} R')) (M : ModuleCat.{max u v w} R) :
    Nonempty ((ModuleCat.restrictScalars.{max u v w} f).mapDerivedCategory.obj
          ((T.tensor.obj (L.obj K)).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} R) 0).obj M)) ≅
        (T'.tensor.obj K).obj ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} R') 0).obj
          ((ModuleCat.restrictScalars.{max u v w} f).obj M))) := by
  classical
  -- The monoidal structure on modules above the ring's universe has unit `ULift R`, so it cannot
  -- be found by instance search, which reaches Mathlib's same-universe one first; pin it.
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{u, max v w}
  let : MonoidalCategory (ModuleCat.{max u v w} R') :=
    ModuleCat.liftedModuleMonoidal.{u, max v w}
  let : MonoidalPreadditive (ModuleCat.{max u v w} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{u, max v w}
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{v, max u w}
  let : MonoidalCategory (ModuleCat.{max u v w} R) :=
    ModuleCat.liftedModuleMonoidal.{v, max u w}
  let : MonoidalPreadditive (ModuleCat.{max u v w} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{v, max u w}
  -- A K-flat resolution `P` of a representative of `K`.
  obtain ⟨P, p, hP, -, hp, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{u, max v w} (DerivedCategory.Q.objPreimage K)
  have hQp : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  let eK : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  -- Stacks 06Y6: the comparison of `L` is invertible at the K-flat `P`, so `L.obj K = Q (R ⊗ P)`.
  have hcomp : IsIso (comparison.app P) :=
    CochainComplex.DerivedTensor.KFlatDerived.isIso_extensionCounit_app_of_kFlat f L comparison
      P hP
  let EP : CochainComplex (ModuleCat.{max u v w} R) ℤ :=
    (CochainComplex.extendScalarsLarge.{w, u, v} f).obj P
  let eL := L.mapIso eK.symm ≪≫ asIso (comparison.app P)
  have hEP : CochainComplex.KFlat.{v, max u w} EP :=
    CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars f P hP
  -- A K-flat resolution `S` of `M[0]` over `R`.
  obtain ⟨S, s, hS, -, hs, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{v, max u w}
      ((CochainComplex.singleFunctor (ModuleCat.{max u v w} R) 0).obj M)
  have hQs : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 hs
  let eS : DerivedCategory.Q.obj S ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v w} R) 0).obj M :=
    asIso (DerivedCategory.Q.map s) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v w} R) 0).app M).symm
  -- The restriction of `S` to `R'`, and a K-flat resolution `SS` of it.
  let US : CochainComplex (ModuleCat.{max u v w} R') ℤ :=
    (CochainComplex.restrictScalarsLarge.{w, u, v} f).obj S
  obtain ⟨SS, qq, hSS, -, hqq, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, max v w} US
  have hQq : IsIso (DerivedCategory.Q.map qq) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ qq).2 hqq
  have hUs : QuasiIso ((CochainComplex.restrictScalarsLarge.{w, u, v} f).map s) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology s
      (ModuleCat.restrictScalars.{max u v w} f)).2 hs
  have hQUs : IsIso (DerivedCategory.Q.map
      ((CochainComplex.restrictScalarsLarge.{w, u, v} f).map s)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hUs
  let eUS : DerivedCategory.Q.obj US ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v w} R') 0).obj
        ((ModuleCat.restrictScalars.{max u v w} f).obj M) :=
    asIso (DerivedCategory.Q.map ((CochainComplex.restrictScalarsLarge.{w, u, v} f).map s)) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (ModuleCat.restrictScalars.{max u v w} f) (ComplexShape.up ℤ) 0).app M) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v w} R') 0).app _).symm
  let eSS : DerivedCategory.Q.obj SS ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v w} R') 0).obj
        ((ModuleCat.restrictScalars.{max u v w} f).obj M) :=
    asIso (DerivedCategory.Q.map qq) ≪≫ eUS
  -- Stacks 06Y1 on complexes, with the Koszul interchange placing the base-changed factor right.
  let e6 : (CochainComplex.restrictScalarsLarge.{w, u, v} f).obj
        (HomologicalComplex.tensorObj EP S)
      ≅ HomologicalComplex.tensorObj P US :=
    (CochainComplex.restrictScalarsLarge.{w, u, v} f).mapIso
        (CochainComplex.DerivedTensor.tensorFlipIso.{v, max u w} EP S) ≪≫
      CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso f P S ≪≫
      CochainComplex.DerivedTensor.tensorFlipIso.{u, max v w} US P
  have hQtl : IsIso (DerivedCategory.Q.map ((TleftCochain P).map qq)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (CochainComplex.DerivedTensor.quasiIso_tleft_map_of_kFlat P hP qq)
  exact ⟨(ModuleCat.restrictScalars.{max u v w} f).mapDerivedCategory.mapIso
        ((T.tensor.mapIso eL).app _ ≪≫
          (T.tensor.obj (DerivedCategory.Q.obj EP)).mapIso eS.symm ≪≫
          T.comparison EP S hEP hS) ≪≫
      (ModuleCat.restrictScalars.{max u v w} f).mapDerivedCategoryFactors.app
        (HomologicalComplex.tensorObj EP S) ≪≫
      DerivedCategory.Q.mapIso e6 ≪≫
      (asIso (DerivedCategory.Q.map ((TleftCochain P).map qq))).symm ≪≫
      (T'.comparison P SS hP hSS).symm ≪≫
      (T'.tensor.obj (DerivedCategory.Q.obj P)).mapIso eSS ≪≫
      (T'.tensor.mapIso eK).app _⟩

/-! ### The projection formula for derived extension of scalars, and Stacks 0H75 -/

section DerivedExtensionScalars

open CategoryTheory.MonoidalCategory

variable {R' R : Type u} [CommRing R'] [CommRing R] (f : R' →+* R)

/-- **The projection formula for derived extension of scalars.** Let `L` be certified as the
total left derived functor of termwise extension of scalars along `f : R' → R`, let `K` be an
object of `D(R')` and let `M` be an `R`-module. Then the restriction to `R'` of
`(L.obj K) ⊗_R^L M[0]` is `K ⊗_{R'}^L (M as an R'-module)[0]`.

This is the hypothesis that `hasTorAmplitudeIn_iff_of_isNilpotent_ker` assumes, here proved from
the certificate for `L`. The argument is in the module docstring; the step that needs the
certificate rather than a projective resolution is invertibility of the comparison at a K-flat
complex, Stacks 06Y6. The conclusion is `Nonempty` of the isomorphism because the resolutions it
is built from are only available through existential statements. -/
private lemma nonempty_projectionFormulaIso
    (L : DerivedCategory (ModuleCat.{u} R') ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : DerivedCategory.Q (C := ModuleCat.{u} R') ⋙ L ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := ModuleCat.{u} R))
    [L.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R') (ComplexShape.up ℤ))]
    (T' : CochainComplex.DerivedTensor.DerivedTensorProduct R')
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (K : DerivedCategory (ModuleCat.{u} R')) (M : ModuleCat.{u} R) :
    Nonempty ((ModuleCat.restrictScalars f).mapDerivedCategory.obj
          ((T.tensor.obj (L.obj K)).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) ≅
        (T'.tensor.obj K).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj
          ((ModuleCat.restrictScalars f).obj M))) :=
  nonempty_projectionFormulaIsoLarge.{u, u, u} f L comparison T'.toGeneral T.toGeneral K M

/-- **The forward direction of Stacks 0H75, for an arbitrary ring map.** Let `L` be certified as
the total left derived functor of termwise extension of scalars along `f : R' → R`, let `K` be an
object of `D(R')` and let `M` be an `R`-module. If `H^i((L.obj K) ⊗_R^L M[0])` vanishes, so does
`H^i(K ⊗_{R'}^L M[0])`, with `M` read as an `R'`-module.

No hypothesis on `f` is needed: this is the projection formula `nonempty_projectionFormulaIso`
together with the fact that restriction of scalars neither creates nor destroys vanishing
cohomology. It is the direction of `hasTorAmplitudeIn_derivedExtensionScalars_iff_sameUniverse`
that needs neither surjectivity nor nilpotence. -/
public theorem isZero_homology_derivedTensor_restrictScalars_of_derivedExtensionScalars
    (L : DerivedCategory (ModuleCat.{u} R') ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : DerivedCategory.Q (C := ModuleCat.{u} R') ⋙ L ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := ModuleCat.{u} R))
    [L.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R') (ComplexShape.up ℤ))]
    (T' : CochainComplex.DerivedTensor.DerivedTensorProduct R')
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (K : DerivedCategory (ModuleCat.{u} R')) (M : ModuleCat.{u} R) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((T.tensor.obj (L.obj K)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).obj
      ((T'.tensor.obj K).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj
        ((ModuleCat.restrictScalars f).obj M)))) :=
  (isZero_homology_iff_of_iso_mapDerivedCategory f
    (nonempty_projectionFormulaIso f L comparison T' T K M).some i).2 h

/-- **Stacks 0H75 with both rings and all modules in one universe.** Derived extension of scalars
along a surjective map of commutative rings whose kernel is a nilpotent ideal preserves and
reflects Tor amplitude in every finite interval: for `K` an object of `D(R')` and `L` the derived
base change, `L.obj K` has Tor amplitude in `[a, b]` if and only if `K` does.

`L` is quantified over together with its comparison to termwise extension of scalars and the
`Functor.IsLeftDerivedFunctor` certificate, which pins it down as the derived base change; the
derived tensor products are certified bifunctors in the sense of Stacks 064M and 0BYI. The
projection formula relating the two sides is supplied by `nonempty_projectionFormulaIso`, proved
from that certificate, and the equivalence is then the nilpotent dévissage
`hasTorAmplitudeIn_iff_of_isNilpotent_ker`, which takes that projection isomorphism as a
hypothesis. Surjectivity and nilpotence of the kernel enter only the direction "`L.obj K`
bounded ⟹ `K` bounded"; the other direction is the projection formula alone.

This is **not** the tag endpoint: the source leaves the universes of the two rings and of the
module carriers independent, and this statement pins all three to one universe `u`. The endpoint
is `hasTorAmplitudeIn_derivedExtensionScalars_iff` at the end of this file, of which this is the
specialisation at `u = v = w`; it carries the tag and this does not. The proof is kept separate
rather than obtained from the endpoint because the one-sided exports below are phrased at one
universe and consume the same-universe projection formula. -/
public theorem hasTorAmplitudeIn_derivedExtensionScalars_iff_sameUniverse
    (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f))
    (L : DerivedCategory (ModuleCat.{u} R') ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : DerivedCategory.Q (C := ModuleCat.{u} R') ⋙ L ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := ModuleCat.{u} R))
    [L.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R') (ComplexShape.up ℤ))]
    (T' : CochainComplex.DerivedTensor.DerivedTensorProduct R')
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (K : DerivedCategory (ModuleCat.{u} R')) (a b : ℤ) :
    Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified T) (L.obj K) a b ↔
      Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified T') K a b :=
  hasTorAmplitudeIn_iff_of_isNilpotent_ker f hf hnil T' T K (L.obj K)
    (fun M => (nonempty_projectionFormulaIso f L comparison T' T K M).some) a b

/-! ### The one-sided form, for consumers with no lower bound

Stacks 0H75 as stated above is two-sided: `Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn` is
`∀ M i, (i < a ∨ b < i) → IsZero (H^i (K ⊗^L M[0]))`, so using it requires producing an integer
`a`. A consumer such as Stacks 09AR has an object of `D(R')` whose derived reduction is merely
bounded *above*, with no lower bound available — morally 0H75 at `a = -∞`. The dévissage
`isZero_derivedTensor_single_of_pow_smul_top_eq_bot` is degreewise and one-sided, so the
one-sided statement is available directly; these are the exports for it. The one-sided condition
is spelled out rather than named, following
`StacksDraft.TorAmplitude.hasTorAmplitudeAbove_iff_exists_kFlat_flat_representative`.
-/

/-- **Stacks 0H75, one-sided.** Derived extension of scalars along a surjective map of commutative
rings with nilpotent kernel reflects a Tor-amplitude bound *from above*, with no lower bound
involved: if `H^i((L.obj K) ⊗_R^L M[0])` vanishes for every `R`-module `M` and every `i > b`, then
`H^i(K ⊗_{R'}^L N[0])` vanishes for every `R'`-module `N` and every `i > b`.

This is the hard direction of `hasTorAmplitudeIn_derivedExtensionScalars_iff_sameUniverse` with
the lower bound removed. It exists separately because the two-sided statement cannot be used by a
consumer that has no integer `a` to supply; see the section docstring. The projection formula is
again proved from the certificate for `L`, by `nonempty_projectionFormulaIso`. -/
public theorem hasTorAmplitudeAbove_of_derivedExtensionScalars
    (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f))
    (L : DerivedCategory (ModuleCat.{u} R') ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : DerivedCategory.Q (C := ModuleCat.{u} R') ⋙ L ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := ModuleCat.{u} R))
    [L.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R') (ComplexShape.up ℤ))]
    (T' : CochainComplex.DerivedTensor.DerivedTensorProduct R')
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (K : DerivedCategory (ModuleCat.{u} R')) (b : ℤ)
    (hK : ∀ (M : ModuleCat.{u} R) (i : ℤ), b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((T.tensor.obj (L.obj K)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)))) :
    ∀ (N : ModuleCat.{u} R') (i : ℤ), b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).obj
        ((T'.tensor.obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj N))) := by
  intro N i hi
  exact isZero_homology_single_of_isNilpotent_ker f hf hnil (T'.tensor.obj K) i
    (fun M => (isZero_homology_iff_of_iso_mapDerivedCategory f
      (nonempty_projectionFormulaIso f L comparison T' T K M).some i).2 (hK M i hi)) N

/-- **Stacks 0H75, one-sided, in the form a consumer wants.** If the derived base change
`L.obj K` of an object `K` of `D(R')` satisfies the Tor-amplitude bound from above in degrees
`≤ b`, then `K` itself is bounded above by `b`: `K.IsLE b`.

Obtained from `hasTorAmplitudeAbove_of_derivedExtensionScalars` by taking the test module to be
`R'` and identifying `K ⊗_{R'}^L R'[0]` with `K` through the right unitor of the certified
bifunctor `T'`. There is no lower bound anywhere in the statement, which is the point: this is the
form in which Stacks 09AR and its dependents can cite 0H75. -/
public theorem isLE_of_hasTorAmplitudeAbove_derivedExtensionScalars
    (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f))
    (L : DerivedCategory (ModuleCat.{u} R') ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : DerivedCategory.Q (C := ModuleCat.{u} R') ⋙ L ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := ModuleCat.{u} R))
    [L.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R') (ComplexShape.up ℤ))]
    (T' : CochainComplex.DerivedTensor.DerivedTensorProduct R')
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (K : DerivedCategory (ModuleCat.{u} R')) (b : ℤ)
    (hK : ∀ (M : ModuleCat.{u} R) (i : ℤ), b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((T.tensor.obj (L.obj K)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)))) :
    K.IsLE b := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  refine (hasTorAmplitudeAbove_of_derivedExtensionScalars f hf hnil L comparison T' T K b hK
    (ModuleCat.of R' R') i hi).of_iso ?_
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).mapIso
    (T'.rightUnitor.app K).symm

end DerivedExtensionScalars

/-! ### Stacks 0H75 at three independent universes

Everything above pins the two rings and the module carriers to one universe, because
`Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified T)` is stated for
`CochainComplex.DerivedTensor.DerivedTensorProduct R`, whose modules live in the universe of `R`.
The source constrains no relation between the universe of `R'`, the universe of `R` and the
universe of the modules, so this section repeats the whole chain over
`CochainComplex.DerivedTensor.DerivedTensorProductGeneral`, whose module universe is free, with
both rings' modules read in one universe `max u v w` above both rings. Nothing is `ULift`ed: the
rings themselves are the source's rings.

The two ingredients that are genuinely universe-sensitive are supplied by the change-of-scalars
layer at two independent ring universes:
`CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars` for Stacks 06Y1 and
`CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso` for the complex-level projection
formula. The Koszul interchange of the two tensor factors is
`CochainComplex.DerivedTensor.tensorFlipIso`, a single isomorphism of complexes rather than the
braiding of a symmetric monoidal structure; that is what lets this section avoid
`TotalTensorComplex.cochainComplex_symmetricMonoidalCategory`, which is stated only for a ring and
its own modules.

The five lemmas here mirror the five one-universe lemmas above line for line and are a dedup
target: the one-universe layer should eventually be the `u = v = w` case of this one, which needs
the one-sided exports and `hasTorAmplitudeIn_iff_of_isNilpotent_ker` restated at the free module
universe first.
-/

section Large

open CategoryTheory.MonoidalCategory CochainComplex.DerivedTensor

section NilpotentLarge

variable {R' : Type u} {R : Type v} [CommRing R'] [CommRing R] (f : R' →+* R)

/-- **The nilpotent dévissage over an assumed projection isomorphism, at three independent
universes. This is not Stacks 0H75.** This is
`hasTorAmplitudeIn_iff_of_isNilpotent_ker` with the module universe freed: `R'` lives in `Type u`,
`R` in `Type v`, and both rings' modules are read in `ModuleCat.{max u v w}`.

As there, `projection` is a hypothesis relating two otherwise unrelated objects and carries the
whole forward transfer, so this statement is strictly weaker than the tag and carries no tag. It
is what the endpoint `hasTorAmplitudeIn_derivedExtensionScalars_iff` consumes, after
`nonempty_projectionFormulaIsoLarge` discharges `projection` from the certificate for `L`. -/
private theorem hasTorAmplitudeInLarge_iff_of_isNilpotent_ker
    (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f))
    (T' : DerivedTensorProductGeneral.{u, max v w} R')
    (T : DerivedTensorProductGeneral.{v, max u w} R)
    (K' : DerivedCategory (ModuleCat.{max u v w} R'))
    (K : DerivedCategory (ModuleCat.{max u v w} R))
    (projection : ∀ M : ModuleCat.{max u v w} R,
      (ModuleCat.restrictScalars.{max u v w} f).mapDerivedCategory.obj
          ((T.tensor.obj K).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} R) 0).obj M)) ≅
        (T'.tensor.obj K').obj ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} R') 0).obj
          ((ModuleCat.restrictScalars.{max u v w} f).obj M)))
    (a b : ℤ) :
    Stacks.TorAmplitudeTriangle.HasTorAmplitudeInLarge (derivedTensoringOfCertifiedGeneral T) K a b
      ↔
      Stacks.TorAmplitudeTriangle.HasTorAmplitudeInLarge (derivedTensoringOfCertifiedGeneral T') K'
        a b := by
  constructor
  · intro hK N i hi
    exact isZero_homology_single_of_isNilpotent_ker f hf hnil (T'.tensor.obj K') i
      (fun M => (isZero_homology_iff_of_iso_mapDerivedCategory f (projection M) i).2
        (hK M i hi)) N
  · intro hK' M i hi
    exact (isZero_homology_iff_of_iso_mapDerivedCategory f (projection M) i).1
      (hK' ((ModuleCat.restrictScalars.{max u v w} f).obj M) i hi)


/-- The general form of Stacks 0H75: let `f : R' → R` be a surjective map of commutative rings
whose kernel is a nilpotent ideal, and let `L` be the derived base change along `f`. For every
object `K` of `D(R')` and every finite interval `[a, b]`, the object `L.obj K` has Tor amplitude
in `[a, b]` if and only if `K` does.

**This statement is not the tag.** It reads Tor amplitude off
`CochainComplex.DerivedTensor.DerivedTensorProductGeneral`, which carries the comparison at pairs
of K-flat complexes, its naturality, and shift-compatibility and exactness in *both* variables.
Stacks 0652 reads Tor amplitude off three fields only — the bifunctor, the comparison with
termwise tensoring by a module placed in degree zero, and the `IsLeftDerivedFunctor` certificate
— so assuming the richer datum makes this a weaker theorem than the source's. It is kept as the
internal helper that carries the dévissage. The tag sits on
`StacksDraft.TorAmplitude.hasTorAmplitudeIn_derivedExtensionScalars_certified_iff` in
`StacksFrontier.Homology.TorAmplitude.NilpotentCertified`, which is quantified over
`StacksDraft.TorAmplitude.CertifiedDerivedTensoring` on each ring and derives this one by
scalar-lifting both rings into the common module universe.

The universe of `R'`, the universe of `R` and the universe of the module carriers are independent:
`R' : Type u`, `R : Type v`, and both rings' modules are read in `ModuleCat.{max u v w}`, as in the
source statement. Neither ring is `ULift`ed.

`L` is quantified over together with its comparison to termwise extension of scalars and the
`Functor.IsLeftDerivedFunctor` certificate, which pins it down as *the* derived base change rather
than an arbitrary functor; the derived tensor products are certified bifunctors in the sense of
Stacks 064M and 0BYI, with the module universe free
(`CochainComplex.DerivedTensor.DerivedTensorProductGeneral`). The projection formula relating the
two sides is supplied by `nonempty_projectionFormulaIsoLarge`, *proved* from the certificate for
`L` rather than assumed, and the equivalence is then the nilpotent dévissage
`hasTorAmplitudeInLarge_iff_of_isNilpotent_ker`. Surjectivity and nilpotence of the kernel enter
only the direction "`L.obj K` bounded ⟹ `K` bounded"; the other direction is the projection
formula alone, which holds for any ring map.

`hasTorAmplitudeIn_derivedExtensionScalars_iff_sameUniverse` above is the case `u = v = w`. -/
public theorem hasTorAmplitudeIn_derivedExtensionScalars_iff
    (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f))
    (L : DerivedCategory (ModuleCat.{max u v w} R') ⥤ DerivedCategory (ModuleCat.{max u v w} R))
    (comparison : DerivedCategory.Q (C := ModuleCat.{max u v w} R') ⋙ L ⟶
      CochainComplex.extendScalarsLarge.{w, u, v} f ⋙
        DerivedCategory.Q (C := ModuleCat.{max u v w} R))
    [L.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max u v w} R') (ComplexShape.up ℤ))]
    (T' : DerivedTensorProductGeneral.{u, max v w} R')
    (T : DerivedTensorProductGeneral.{v, max u w} R)
    (K : DerivedCategory (ModuleCat.{max u v w} R')) (a b : ℤ) :
    Stacks.TorAmplitudeTriangle.HasTorAmplitudeInLarge (derivedTensoringOfCertifiedGeneral T)
      (L.obj K) a b ↔
      Stacks.TorAmplitudeTriangle.HasTorAmplitudeInLarge (derivedTensoringOfCertifiedGeneral T') K a
        b :=
  hasTorAmplitudeInLarge_iff_of_isNilpotent_ker f hf hnil T' T K (L.obj K)
    (fun M => (nonempty_projectionFormulaIsoLarge f L comparison T' T K M).some) a b

end NilpotentLarge

end Large

end

end StacksDraft.TorAmplitude
