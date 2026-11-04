module

public import StacksFrontier.AlgebraicGeometry.Cohomology.TildeTruncationTower
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.OneStep
public import StacksFrontier.RingTheory.Koszul.PowerLift.KoszulPowerLift

/-!
# The Koszul power lift on an affine scheme, at the level of sheaves

Let `R` be a commutative ring, let `f₁, …, f_r ∈ R` and let `F` be an object of
`D(𝒪_{Spec R})` isomorphic to the derived sheafification of an object `E` of `D(R)` whose
cohomology modules in the degrees `-r + 1, …, 0` are `f_i`-power torsion for every `i`. Then
every morphism `𝒪_{Spec R}[0] ⟶ F` factors through the sheafification of the canonical map
`R[0] ⟶ K(f₁^{e+1}, …, f_r^{e+1})` of [Stacks, Tag 0BKC], for some exponent `e`. This is the
sheaf-level form of [Stacks, Tag 08E3], whose module-level form is
`Stacks.Koszul.PowerLift.exists_koszulPower_lift_koszulCochain`.

## Main definitions

* `Stacks.AffineTilde.koszulPowerTildeComplex` — the complex of `𝒪_{Spec R}`-modules associated
  to the Koszul complex on the `(e+1)`-st powers of `f₁, …, f_r`, placed in the cohomological
  degrees `-r, …, 0`. It is the perfect object of
  `Stacks.AffineTilde.isAdmissible_Q_obj_tildeComplex_extend_seqComplex`.
* `Stacks.AffineTilde.structureSheafSingleComplex` — `𝒪_{Spec R}` placed in cohomological degree
  zero, with `Stacks.AffineTilde.tildeSingleSelfIso` identifying it with the sheafification of
  `R[0]`.
* `Stacks.AffineTilde.koszulPowerUnitTilde` — the sheafification of the canonical map
  `R[0] ⟶ K(f₁^{e+1}, …, f_r^{e+1})`, read as a map out of `𝒪_{Spec R}[0]`.
* `Stacks.AffineTilde.derivedTildeFullyFaithfulAnyModel` and
  `Stacks.AffineTilde.mapDerivedCategoryTildeFullyFaithful` — derived sheafification is fully
  faithful at an arbitrary pair of derived categories, before and after forgetting
  quasi-coherence of the cohomology.

## Main results

* `Stacks.AffineTilde.exists_koszulPowerTilde_lift` — the lift, for an object of
  `D(𝒪_{Spec R})` presented as the derived sheafification of an object of `D(R)`; and
  `Stacks.AffineTilde.exists_koszulPowerTilde_lift_mapDerivedCategory`, its case `F =
  \widetilde{E}`.
* `Stacks.AffineTilde.exists_isAdmissible_koszulPowerTilde_lift` — the same with the source of the
  lift recorded as an admissible approximating object for `V(f₁, …, f_r)`, which is the form the
  one-step construction of [Stacks, Tag 08EQ] consumes.
* `Stacks.AffineTilde.exists_koszulPowerTilde_lift_of_fullyFaithful` — the underlying statement,
  with full faithfulness of derived sheafification as an explicit hypothesis.
* `Stacks.AffineTilde.exists_iso_mapDerivedCategory_tilde_of_isQuasicoherent` — the presentation
  hypothesis is no restriction: every object of `D(𝒪_{Spec R})` with quasi-coherent cohomology is
  the derived sheafification of an object of `D(R)`.

## Implementation notes

The transport from modules to sheaves is along *full faithfulness* of derived sheafification, the
unit half of [Stacks, Tag 06Z0], and not along the equivalence of [Stacks, Tag 06Z0] itself. Full
faithfulness is what the argument needs: a morphism `𝒪_{Spec R}[0] ⟶ \widetilde{E}` descends to
`R[0] ⟶ E`, the module-level lift applies there, and sheafifying the factorization gives the
result back. Essential surjectivity enters only through
`Stacks.AffineTilde.exists_iso_mapDerivedCategory_tilde_of_isQuasicoherent`, which converts the
presentation hypothesis on `F` into quasi-coherence of its cohomology sheaves and is not used by
the lift itself.

*The model.* `HasDerivedCategory` carries the localized category as data, so a statement proved at
one model says nothing about another. Everything here therefore carries free
`[HasDerivedCategory.{w} (ModuleCat.{u} R)]` and `[HasDerivedCategory.{w'} (Spec R).Modules]`
binders, full faithfulness included: `AlgebraicGeometry.derivedTildeFullyFaithful` is stated only
at the locally small model, but its proof —
`AlgebraicGeometry.derivedTildeFullyFaithfulOfIsIsoUnit` fed with
`AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_unit_app_of_quasiIso` — uses nothing
model-dependent, the unbounded affine vanishing behind it
(`AlgebraicGeometry.quasiIso_globalSectionsOver_map_tilde`) being a statement about cochain
complexes that mentions no derived category. That is what
`Stacks.AffineTilde.derivedTildeFullyFaithfulAnyModel` records, and it is why the lift needs no
hypothesis beyond the presentation of `F`.

`AlgebraicGeometry.PerfectApproximation.IsAdmissible` and the rest of the [Stacks, Tag 08EQ]
cluster are, by contrast, defined at `CategoryTheory.HasDerivedCategory.standard`, and the locally
small instances of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` — imported here
through `AlgebraicGeometry.derivedTilde` — are *global*, so `attribute [local instance]
HasDerivedCategory.standard` no longer selects that model in a file importing them. The standard
model is reached in
`Stacks.AffineTilde.exists_isAdmissible_koszulPowerTilde_lift` by a `let` in the statement, the
device of `AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction_counit_isIso`.

**No `08E3` attribute is placed.** What the source states at the sheaf level is the factorization
for an object of `D_QCoh(𝒪_{Spec A})` whose cohomology sheaves *vanish on the open
`⋃ᵢ D(f_i)`*; the hypothesis below is instead the algebraic one, that the cohomology modules of
the complex of `R`-modules presenting `F` are `f_i`-power torsion. The dictionary between the two
— vanishing of `\widetilde{M}` on `D(f)` is `f`-power torsion of `M` — is not in this file, so
the covering set of the geometric statement is incomplete here. The algebraic statement itself
already carries the attribute, on
`Stacks.Koszul.PowerLift.exists_koszulPower_lift`.

## References

* [Stacks Project, Tag 08E3](https://stacks.math.columbia.edu/tag/08E3)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08EQ](https://stacks.math.columbia.edu/tag/08EQ)
* [Stacks Project, Tag 0BKC](https://stacks.math.columbia.edu/tag/0BKC)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.AffineTilde

universe w w' u

variable {R : CommRingCat.{u}} {r : ℕ}

/-! ### The sheafified Koszul power complex and its canonical map -/

/-- The complex of `𝒪_{Spec R}`-modules associated to the Koszul complex on the `(e+1)`-st powers
of `f₁, …, f_r`, placed in the cohomological degrees `-r, …, 0`. -/
abbrev koszulPowerTildeComplex (f : Fin r → R) (e : ℕ) : CochainComplex (Spec R).Modules ℤ :=
  tildeComplex ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} R)).obj
    (Koszul.seqComplex fun i ↦ f i ^ (e + 1)))

section StructureSheaf

variable (R)

/-- The structure sheaf of `Spec R` placed in cohomological degree zero. By
`AlgebraicGeometry.tildeSelf` it is the sheaf associated to `R` as a module over itself. -/
abbrev structureSheafSingleComplex : CochainComplex (Spec R).Modules ℤ :=
  ((CochainComplex.singleFunctors (Spec R).Modules).functor 0).obj
    (show (Spec R).Modules from SheafOfModules.unit (Spec R).ringCatSheaf)

/-- Sheafifying `R` placed in cohomological degree zero gives the structure sheaf placed in
cohomological degree zero. -/
def tildeSingleSelfIso :
    tildeComplex (((CochainComplex.singleFunctors (ModuleCat.{u} R)).functor 0).obj
        (ModuleCat.of R R)) ≅ structureSheafSingleComplex R :=
  ((tilde.functor R).mapCochainComplexSingleFunctor 0).app (ModuleCat.of R R) ≪≫
    ((CochainComplex.singleFunctors (Spec R).Modules).functor 0).mapIso tildeSelf

end StructureSheaf

/-- The sheafification of the canonical map `R[0] ⟶ K(f₁^{e+1}, …, f_r^{e+1})` of
[Stacks, Tag 0BKC], read as a map from the structure sheaf in degree zero. -/
def koszulPowerUnitTilde (f : Fin r → R) (e : ℕ) :
    structureSheafSingleComplex R ⟶ koszulPowerTildeComplex f e :=
  (tildeSingleSelfIso R).inv ≫
    ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (AdicKoszul.koszulPowerUnit f e)

/-! ### The lift at an arbitrary model, from full faithfulness -/

/-- **The Koszul power lift on an affine scheme, from full faithfulness of derived
sheafification.** Let `f₁, …, f_r ∈ R`, let `E` be an object of `D(R)` such that every element of
`Hⁿ(E)` is annihilated by a power of `f_i` for every `i` and every `n` with `-r + 1 ≤ n ≤ 0`, and
let `F` be an object of `D(𝒪_{Spec R})` isomorphic to the derived sheafification of `E`. Then
every morphism `\widetilde{R[0]} ⟶ F` factors through the sheafification of the canonical map
`R[0] ⟶ K(f₁^{e+1}, …, f_r^{e+1})`, for some exponent `e`.

Full faithfulness descends the given morphism to a morphism `R[0] ⟶ E`, where
`Stacks.Koszul.PowerLift.exists_koszulPower_lift_koszulCochain` applies; sheafifying the resulting
factorization and transporting it along
`CategoryTheory.Functor.mapDerivedCategoryFactors` gives the conclusion. -/
theorem exists_koszulPowerTilde_lift_of_fullyFaithful
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (Spec R).Modules]
    (hff : ((tilde.functor R).mapDerivedCategory
      (C₁ := ModuleCat.{u} R) (C₂ := (Spec R).Modules)).FullyFaithful)
    (f : Fin r → R) {F : DerivedCategory (Spec R).Modules}
    (E : DerivedCategory (ModuleCat.{u} R))
    (hEF : (tilde.functor R).mapDerivedCategory.obj E ≅ F)
    (hE : ∀ i : Fin r, ∀ n : ℤ, -(r : ℤ) + 1 ≤ n → n ≤ 0 →
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj E,
        ∃ k : ℕ, f i ^ k • x = 0)
    (s : DerivedCategory.Q.obj (tildeComplex
      (((CochainComplex.singleFunctors (ModuleCat.{u} R)).functor 0).obj
        (ModuleCat.of R R))) ⟶ F) :
    ∃ e : ℕ, ∃ t : DerivedCategory.Q.obj (koszulPowerTildeComplex f e) ⟶ F,
      s = DerivedCategory.Q.map
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (AdicKoszul.koszulPowerUnit f e)) ≫ t := by
  obtain ⟨e, t₀, ht₀⟩ := Stacks.Koszul.PowerLift.exists_koszulPower_lift_koszulCochain f E hE
    (hff.preimage ((tilde.functor R).mapDerivedCategoryFactors.hom.app _ ≫ s ≫ hEF.inv))
  refine ⟨e, (tilde.functor R).mapDerivedCategoryFactors.inv.app _ ≫
    (tilde.functor R).mapDerivedCategory.map t₀ ≫ hEF.hom, ?_⟩
  have hnat := (tilde.functor R).mapDerivedCategoryFactors.inv.naturality
    (AdicKoszul.koszulPowerUnit f e)
  simp only [Functor.comp_map] at hnat
  rw [reassoc_of% hnat, ← Functor.map_comp_assoc, ← ht₀, hff.map_preimage]
  simp

/-! ### Full faithfulness of derived sheafification at an arbitrary model -/

/-- **Derived sheafification is fully faithful, at an arbitrary pair of derived categories.**
This is the unit half of [Stacks, Tag 06Z0], `AlgebraicGeometry.derivedTildeFullyFaithful`, with
the model of both derived categories left free.

The proof is the one of `AlgebraicGeometry.derivedTildeFullyFaithfulOfIsIsoUnit`, whose input —
invertibility of the unit of the derived Spec–Γ adjunction — is available here at any model:
`AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_unit_app_of_quasiIso` carries free
`HasDerivedCategory` binders, and the unbounded affine vanishing feeding it,
`AlgebraicGeometry.quasiIso_globalSectionsOver_map_tilde`, is a statement about cochain complexes
which mentions no derived category at all. -/
def derivedTildeFullyFaithfulAnyModel (R : CommRingCat.{u})
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (Spec R).Modules] :
    (derivedTilde R).FullyFaithful :=
  have : ∀ M : DerivedCategory (ModuleCat.{u} R),
      IsIso ((derivedTildeGlobalSectionsAdjunction R).val.unit.app M) := fun M =>
    isIso_derivedTildeGlobalSectionsAdjunction_unit_app_of_quasiIso R
      (fun M' _ s hI hs => quasiIso_globalSectionsOver_map_tilde R M' s hI hs) M
  have : IsIso (derivedTildeGlobalSectionsAdjunction R).val.unit :=
    NatIso.isIso_of_isIso_app _
  Functor.FullyFaithful.ofCompFaithful
    (G := (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι)
    (derivedTildeGlobalSectionsAdjunction R).val.fullyFaithfulLOfIsIsoUnit

/-- **Derived sheafification, read as a functor to the whole of `D(𝒪_{Spec R})`, is fully
faithful.** `Stacks.AffineTilde.derivedTildeFullyFaithfulAnyModel` composed with the fully
faithful inclusion of `D_QCoh(𝒪_{Spec R})` and transported along
`AlgebraicGeometry.derivedTildeCompι`. -/
def mapDerivedCategoryTildeFullyFaithful (R : CommRingCat.{u})
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (Spec R).Modules] :
    ((tilde.functor R).mapDerivedCategory
      (C₁ := ModuleCat.{u} R) (C₂ := (Spec R).Modules)).FullyFaithful :=
  ((derivedTildeFullyFaithfulAnyModel.{w, w'} R).comp
      (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).fullyFaithfulι).ofIso
    (derivedTildeCompι R)

/-! ### The lift -/

/-- **The Koszul power lift on an affine scheme.** Let `f₁, …, f_r ∈ R`, let `E` be an object of
`D(R)` such that every element of `Hⁿ(E)` is annihilated by a power of `f_i` for every `i` and
every `n` with `-r + 1 ≤ n ≤ 0`, and let `F` be an object of `D(𝒪_{Spec R})` isomorphic to the
derived sheafification of `E`. Then every morphism `𝒪_{Spec R}[0] ⟶ F` factors through
`Stacks.AffineTilde.koszulPowerUnitTilde`, the sheafification of the canonical map
`R[0] ⟶ K(f₁^{e+1}, …, f_r^{e+1})` of [Stacks, Tag 0BKC], for some exponent `e`.

This is `Stacks.AffineTilde.exists_koszulPowerTilde_lift_of_fullyFaithful` with its full
faithfulness hypothesis discharged by
`Stacks.AffineTilde.derivedTildeFullyFaithfulAnyModel`; both derived categories are still at a
free model, so the statement is available at
`CategoryTheory.HasDerivedCategory.standard`, where the approximation statements of
[Stacks, Tag 08EQ] live, as well as at the locally small model. -/
theorem exists_koszulPowerTilde_lift
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (Spec R).Modules]
    (f : Fin r → R)
    {F : DerivedCategory (Spec R).Modules} (E : DerivedCategory (ModuleCat.{u} R))
    (hEF : (tilde.functor R).mapDerivedCategory.obj E ≅ F)
    (hE : ∀ i : Fin r, ∀ n : ℤ, -(r : ℤ) + 1 ≤ n → n ≤ 0 →
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj E,
        ∃ k : ℕ, f i ^ k • x = 0)
    (s : DerivedCategory.Q.obj (structureSheafSingleComplex R) ⟶ F) :
    ∃ e : ℕ, ∃ t : DerivedCategory.Q.obj (koszulPowerTildeComplex f e) ⟶ F,
      s = DerivedCategory.Q.map (koszulPowerUnitTilde f e) ≫ t := by
  obtain ⟨e, t, ht⟩ := exists_koszulPowerTilde_lift_of_fullyFaithful
    (mapDerivedCategoryTildeFullyFaithful.{w, w'} R) f E hEF hE
    (DerivedCategory.Q.map (tildeSingleSelfIso R).hom ≫ s)
  refine ⟨e, t, ?_⟩
  rw [koszulPowerUnitTilde, Functor.map_comp, Category.assoc, ← ht, ← Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The Koszul power lift for the derived sheafification of a complex of modules.** The case
`F = \widetilde{E}` of `Stacks.AffineTilde.exists_koszulPowerTilde_lift`. -/
theorem exists_koszulPowerTilde_lift_mapDerivedCategory
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (Spec R).Modules]
    (f : Fin r → R)
    (E : DerivedCategory (ModuleCat.{u} R))
    (hE : ∀ i : Fin r, ∀ n : ℤ, -(r : ℤ) + 1 ≤ n → n ≤ 0 →
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj E,
        ∃ k : ℕ, f i ^ k • x = 0)
    (s : DerivedCategory.Q.obj (structureSheafSingleComplex R) ⟶
      (tilde.functor R).mapDerivedCategory.obj E) :
    ∃ e : ℕ, ∃ t : DerivedCategory.Q.obj (koszulPowerTildeComplex f e) ⟶
        (tilde.functor R).mapDerivedCategory.obj E,
      s = DerivedCategory.Q.map (koszulPowerUnitTilde f e) ≫ t :=
  exists_koszulPowerTilde_lift f E (Iso.refl _) hE s

/-- **Quasi-coherent cohomology is enough to present an object as a derived sheafification.**
Every object of `D(𝒪_{Spec R})` all of whose cohomology sheaves are quasi-coherent is isomorphic
to the derived sheafification of an object of `D(R)`.

This is essential surjectivity of `AlgebraicGeometry.derivedTilde`, available from
`AlgebraicGeometry.derivedTilde_isEquivalence`, followed by
`AlgebraicGeometry.derivedTildeCompι`. It shows that the presentation hypothesis of
`Stacks.AffineTilde.exists_koszulPowerTilde_lift` restricts `F` no further than membership in
`D_QCoh(𝒪_{Spec R})` does. -/
theorem exists_iso_mapDerivedCategory_tilde_of_isQuasicoherent
    (F : DerivedCategory (Spec R).Modules)
    (hF : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj F).IsQuasicoherent) :
    ∃ E : DerivedCategory (ModuleCat.{u} R),
      Nonempty ((tilde.functor R).mapDerivedCategory.obj E ≅ F) := by
  obtain ⟨E, ⟨e⟩⟩ : (derivedTilde R).essImage
      (⟨F, hF⟩ : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory) :=
    Functor.EssSurj.mem_essImage (F := derivedTilde R) _
  exact ⟨E, ⟨(derivedTildeCompι R).symm.app E ≪≫
    (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.mapIso e⟩⟩

/-! ### The lift by an admissible object, at the standard model -/

/-- Raising a sequence to a positive power does not change its zero locus: a prime contains
`f^{e+1}` exactly when it contains `f`. -/
theorem zeroLocus_range_pow (f : Fin r → R) (e : ℕ) :
    PrimeSpectrum.zeroLocus (Set.range fun i ↦ f i ^ (e + 1)) =
      PrimeSpectrum.zeroLocus (Set.range f) := by
  ext x
  simp only [PrimeSpectrum.mem_zeroLocus, Set.range_subset_iff, SetLike.mem_coe]
  exact forall_congr' fun i ↦ x.isPrime.pow_mem_iff_mem (e + 1) e.succ_pos

/-- **The Koszul power lift by an admissible approximating object.** Let `f₁, …, f_r ∈ R`, let `E`
be an object of `D(R)` whose cohomology modules in the degrees `-r + 1, …, 0` are `f_i`-power
torsion for every `i`, and let `F` be an object of `D(𝒪_{Spec R})` isomorphic to the derived
sheafification of `E`. Then every morphism `𝒪_{Spec R}[0] ⟶ F` factors through the sheafified
Koszul complex on the `(e+1)`-st powers of the sequence, for some `e`, and that complex is a
perfect object with cohomology supported on `V(f₁, …, f_r)`.

This is `Stacks.AffineTilde.exists_koszulPowerTilde_lift` combined with
`Stacks.AffineTilde.isAdmissible_Q_obj_tildeComplex_extend_seqComplex` and
`Stacks.AffineTilde.zeroLocus_range_pow`. The derived category of `𝒪_{Spec R}`-modules is pinned
to `CategoryTheory.HasDerivedCategory.standard` by a `let` in the statement, because that is the
model at which `AlgebraicGeometry.PerfectApproximation.IsAdmissible` is defined, and the locally
small instance of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` — imported here through
`AlgebraicGeometry.derivedTilde` — is a global instance, so a local attribute cannot select
another model. -/
theorem exists_isAdmissible_koszulPowerTilde_lift [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (f : Fin r → R) :
    let _inst : HasDerivedCategory (Spec R).Modules := HasDerivedCategory.standard _
    ∀ {F : DerivedCategory (Spec R).Modules} (E : DerivedCategory (ModuleCat.{u} R)),
      ((tilde.functor R).mapDerivedCategory.obj E ≅ F) →
      (∀ i : Fin r, ∀ n : ℤ, -(r : ℤ) + 1 ≤ n → n ≤ 0 →
        ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj E,
          ∃ k : ℕ, f i ^ k • x = 0) →
      ∀ s : DerivedCategory.Q.obj (structureSheafSingleComplex R) ⟶ F,
      ∃ e : ℕ, ∃ t : DerivedCategory.Q.obj (koszulPowerTildeComplex f e) ⟶ F,
        PerfectApproximation.IsAdmissible (Spec R) (PrimeSpectrum.zeroLocus (Set.range f))
            (DerivedCategory.Q.obj (koszulPowerTildeComplex f e)) ∧
          s = DerivedCategory.Q.map (koszulPowerUnitTilde f e) ≫ t := by
  intro _inst F E hEF hE s
  obtain ⟨e, t, ht⟩ := exists_koszulPowerTilde_lift f E hEF hE s
  refine ⟨e, t, ?_, ht⟩
  rw [← zeroLocus_range_pow f e]
  exact isAdmissible_Q_obj_tildeComplex_extend_seqComplex _

end Stacks.AffineTilde

end
