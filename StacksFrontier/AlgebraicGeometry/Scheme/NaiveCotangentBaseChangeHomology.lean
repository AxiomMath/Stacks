module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DoubleQuasiIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentBaseChangeComparisonMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SquareBaseRingComparison
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentComplex
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentHomologyZeroDifferentials
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentExactSequence
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic

/-!
# Base change for the naive cotangent complex: the two cohomological conclusions

Let
```
X' --g'--> X
|          |
f'         f
v          v
Y' ---g--> Y
```
be a cartesian square of schemes.  Stacks 0FV5 asserts that the canonical map
`(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` induces an isomorphism on `H^0` and a surjection on `H^{-1}`.

The canonical map is **constructed** here, from the commutativity of the square alone, as the
composite of the two transitivity maps of the source:

`(g')^*NL_{X/Y} ≅ NL_{(g')⁻¹𝒪_X/(g')⁻¹f⁻¹𝒪_Y} ⊗ 𝒪_{X'} ⟶ NL_{X'/Y} ⟶ NL_{X'/Y'}`,

the first identification being Stacks 08TM for a morphism of ringed spaces
(`Stacks.SheafOfModules.pulledNaiveCotangentComparison`), the second map the base-change map
`NL_{B/A} ⊗_B C ⟶ NL_{C/A}` of the tower `(g')⁻¹f⁻¹𝒪_Y ⟶ (g')⁻¹𝒪_X ⟶ 𝒪_{X'}`, and the third
the relative map `NL_{C/A} ⟶ NL_{C/B}` of the tower `(g')⁻¹f⁻¹𝒪_Y ⟶ (f')⁻¹𝒪_{Y'} ⟶ 𝒪_{X'}`.
The second tower exists because the square commutes.

Both cohomological conclusions are then proved for that map, from the elementwise base-change
data of Stacks 0FUZ at each stalk, which the two reductions below take as an explicit input; see
exactly what is carried and why.

## Main definitions

* `AlgebraicGeometry.Scheme.pullbackNaiveCotangentComplex` is `(g')^*NL_{X/Y}`, in the form in
  which the library's Stacks 08TM/0E1Z development writes it: the inverse image of `NL_{X/Y}`
  along `g'` with scalars extended to `𝒪_{X'}`.
* `AlgebraicGeometry.Scheme.baseChangeNaiveCotangentComplexMap` is the canonical map
  `(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` attached to a commutative square.  The comparison
  `(g')⁻¹f⁻¹𝒪_Y ⟶ (f')⁻¹𝒪_{Y'}` of base rings it is built from is
  `AlgebraicGeometry.BaseChangeStalk.baseRingComparison`, with its compatibility with the two
  structure maps to `𝒪_{X'}` given by
  `AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp`; the map attached to an arbitrary
  choice of base-ring comparison is
  `Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison`.
* `AlgebraicGeometry.Scheme.modulesStalkComplex` and
  `AlgebraicGeometry.Scheme.modulesStalkComplexMap` are the complex of stalks at a point of a
  complex of `𝒪_X`-modules, and the map of such complexes induced by a chain map.
* `CochainComplex.IsBijectiveOnCokernel` and `CochainComplex.IsSurjectiveOnKernel` are the two
  elementwise conditions on a morphism of two-term complexes of modules that Stacks 0FUZ
  delivers: bijectivity on the cokernel of the differential and surjectivity on its kernel.
* `AlgebraicGeometry.Scheme.baseChangeNaiveCotangentHomologyZeroMap` is the canonical map
  `(g')^*H^0(NL_{X/Y}) ⟶ H^0(NL_{X'/Y'})` of a commutative square, the canonical map on sheaves
  of relative differentials read through the degree-zero identification `H^0(NL) ≅ Ω` of
  Stacks 0D0J, and `AlgebraicGeometry.Scheme.baseChangeNaiveCotangentHomologyZeroIso` is the
  isomorphism it becomes for a cartesian square.

## Main results

* `AlgebraicGeometry.Scheme.isIso_baseChangeNaiveCotangentHomologyZeroMap`: **Stacks 0FV5**, the
  degree-zero isomorphism for a cartesian square, with no hypothesis beyond cartesianness.
  It is obtained from Stacks 01V0 and Stacks 0D0J, and is stated over Mathlib's
  `AlgebraicGeometry.Scheme.Modules.pullback`; see the section heading above it for how it
  relates to the statement about the canonical map of complexes.
* `AlgebraicGeometry.Scheme.naiveCotangentComplex_baseChange_homologyMap_zero_isIso` and
  `AlgebraicGeometry.Scheme.naiveCotangentComplex_baseChange_homologyMap_negOne_epi`: the two
  cohomological conclusions of **Stacks 0FV5** for the map of complexes, each from the
  corresponding elementwise condition on the stalks taken as an explicit hypothesis.  Those
  hypotheses are discharged -- for the canonical base-ring comparison of the square rather than
  for the `Classical.choose` one used here -- in
  `StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentBaseChangeHomologyCartesian`, where
  the two conclusions are therefore stated with no hypothesis beyond cartesianness.
* `AlgebraicGeometry.SheafOfModules.epi_iff_forall_epi_stalkFunctor_map` and
  `AlgebraicGeometry.SheafOfModules.epi_homologyMap_iff_forall_stalk`: epimorphy of a morphism
  of sheaves of modules, and of the map it induces on the homology of complexes, are stalkwise
  conditions.  These are the epimorphy counterparts of
  `AlgebraicGeometry.SheafOfModules.isIso_iff_forall_isIso_stalkFunctor_map` and
  `AlgebraicGeometry.SheafOfModules.isIso_homologyMap_iff_forall_stalk`.
* `CochainComplex.isIso_homologyMap_zero_of_isBijectiveOnCokernel` and
  `CochainComplex.epi_homologyMap_negOne_of_isSurjectiveOnKernel`: for a morphism of complexes of
  modules concentrated in degrees `-1` and `0`, bijectivity on the cokernel of the differential
  alone gives an isomorphism on `H^0`, and surjectivity on its kernel alone gives an
  epimorphism on `H^{-1}`.  These split the two halves of
  `CochainComplex.quasiIso_of_isZero_X_of_bijective`, which needs all four elementary
  conditions at once; the two halves are what a base-change statement can supply, since
  injectivity on the kernel is exactly the condition that fails there.
* `HomologicalComplex.epi_cyclesMap_of_surjective` and
  `HomologicalComplex.epi_homologyMap_of_epi_cyclesMap`: the epimorphy counterparts of
  `HomologicalComplex.isIso_cyclesMap_of_bijective` and
  `HomologicalComplex.isIso_homologyMap_of_isIso_cyclesMap`.
Mathlib's `CategoryTheory.Functor.map_isZero` — a functor preserving zero morphisms carries a
zero object to a zero object — is what makes the two complexes of stalks concentrated in
degrees `-1` and `0`.
* `CochainComplex.isBijectiveOnCokernel_of_addEquiv` and
  `CochainComplex.isSurjectiveOnKernel_of_addEquiv`: those two conditions transported along
  additive identifications of the four nonzero terms, so that the elementwise conclusion of
  Stacks 0FUZ can be read on a morphism of two-term complexes of modules presented in any other
  way.  Their hypotheses are the second, third and fourth conjuncts of
  `NaiveCotangent.naiveCotangentComplex_baseChange_homology` verbatim.

## Implementation notes

The two conclusions are reached along the same two steps.  First they are localized: both
`IsIso` and `Epi` of a morphism of sheaves of modules are stalkwise conditions
(`AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap` and
`AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap`), and the stalk functor is exact,
so it commutes with homology; the transport of homology along it is Mathlib's
`CategoryTheory.ShortComplex.homologyFunctorIso`.  Then, at a point, the two complexes of
stalks are complexes of modules concentrated in degrees `-1` and `0`, where homology in degree
`0` is the cokernel of the single differential and homology in degree `-1` is its kernel; the
elementwise conditions are fed to `HomologicalComplex.isIso_opcyclesMap_of_bijective` and to
`HomologicalComplex.epi_cyclesMap_of_surjective`.

Epimorphy is transported along the natural isomorphism of functors supplied by
`CategoryTheory.ShortComplex.homologyFunctorIso` with a `private` copy of the usual
`epi_map_iff_of_natIso`: the library already has that lemma under that name several times over,
once publicly in `CategoryTheory` itself, so no new public declaration is made for it.

The degree-`-1` half needs only surjectivity on the kernel, and nothing is assumed about
injectivity there: that is the whole point of the tag, whose `H^{-1}` assertion is a surjection
and not an isomorphism.

The base-ring comparison the canonical map is built from is
`AlgebraicGeometry.BaseChangeStalk.baseRingComparison`, the CONSTRUCTED comparison of the square.
It is the same comparison, and so the same map, that the flat-base-change results of Stacks 0FJZ
and 0FK0 are stated about
(`Stacks.NaiveCotangentFlatBaseChange.quasiIso_baseChangeMapOfComparison_of_flat_base`), so the
cohomological conclusions below and those quasi-isomorphisms speak of one map.  An earlier form
of this module took the comparison instead from
`Stacks.Sheaves.RingedSpaceDifferentials.exists_inverseImageComparison`, which asserts existence
and not uniqueness, making the comparison a `Classical.choose`; nothing can be said about the
stalks of such a witness, which is what
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/SquareBaseRingComparison.lean` was written to
supply, and the two maps were unrelated for want of any lemma identifying the two witnesses.
`Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison` still records the map as a
function of an arbitrary comparison datum, so a caller with a different preferred comparison can
use that one instead.

`(g')^*NL_{X/Y}` is written as `Stacks.SheafOfModules.pulledNaiveCotangentComplex`, the model
of the pullback used by the library's Stacks 08TM/0E1Z development: the inverse image followed
by extension of scalars, which is the definition of the pullback of sheaves of modules.  It is
not written with Mathlib's `AlgebraicGeometry.Scheme.Modules.pullback`, because the
identification of that functor with the two-step composite is an open input of this repository
-- see the note on
`Stacks.SheafOfModules.AlgebraPushout.algebraPullbackComparison` and
`StacksFrontier/AlgebraicGeometry/EtaleAlgebra/FlatBaseChange/StructureSheaf.lean`, which name it.

`AlgebraicGeometry.Scheme.Modules` is `SheafOfModules X.ringCatSheaf` with a `Category`
instance of its own, and `AlgebraicGeometry.Scheme.naiveCotangentComplex` is stated over
`Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf`.  The two spellings are
definitionally equal, which is what lets the stalk criteria of
`StacksFrontier/Topology/Sheaves/Modules/StalkAcyclic.lean` be applied to all the complexes here
with no transport.

## References

* [Stacks Project, Tag 0FV5](https://stacks.math.columbia.edu/tag/0FV5)
* [Stacks Project, Tag 0FUZ](https://stacks.math.columbia.edu/tag/0FUZ), the ring-level
  base-change statement, whose elementwise conclusion is the shape of the hypotheses carried
  here.
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM), the inverse image of
  the naive cotangent complex, which identifies the pullback with a base change.
* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y) and
  [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z), the two transitivity
  maps the canonical map is composed of.
* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I), the comparison of
  `NL_{X/Y}` with the ring-level naive cotangent complex over an affine open.
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL), the stalkwise
  criterion for a complex of sheaves of modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u

noncomputable section

namespace CategoryTheory

/-- **Epimorphy is detected through a natural isomorphism of functors.**  If `F ≅ G` then `F`
carries a morphism to an epimorphism exactly when `G` does.

This is the epimorphy counterpart of `CategoryTheory.NatIso.isIso_map_iff`.  It is `private`:
the library already carries several copies of this lemma under this name, one of them public in
this very namespace
(`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasicoherentTransition.lean`), so a public
declaration here would be a duplicate. -/
private theorem epi_map_iff_of_natIso {C : Type*} [Category* C] {D : Type*} [Category* D]
    {F G : C ⥤ D} (α : F ≅ G) {A B : C} (h : A ⟶ B) : Epi (F.map h) ↔ Epi (G.map h) := by
  constructor
  · intro _
    rw [← NatIso.naturality_1 α h]
    infer_instance
  · intro _
    rw [← NatIso.naturality_2 α h]
    infer_instance

end CategoryTheory

namespace HomologicalComplex

section Abelian

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex C c}

/-- **In a degree with no incoming differential, homology is cycles.**  If the map of cycles in
degree `i` is an epimorphism, so is the map of homology.

This is the epimorphy counterpart of
`HomologicalComplex.isIso_homologyMap_of_isIso_cyclesMap`. -/
theorem epi_homologyMap_of_epi_cyclesMap (φ : K ⟶ L) (i j : ι) (hj : c.prev i = j)
    (hK : K.d j i = 0) (hL : L.d j i = 0) (h : Epi (cyclesMap φ i)) :
    Epi (homologyMap φ i) := by
  have h₁ := K.isIso_homologyπ j i hj hK
  have h₂ := L.isIso_homologyπ j i hj hL
  have e : homologyMap φ i = inv (K.homologyπ i) ≫ cyclesMap φ i ≫ L.homologyπ i := by
    rw [← homologyπ_naturality, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

end Abelian

section ModuleCat

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{v} R) c}

/-- **The map of cycles induced by a morphism of complexes of modules is an epimorphism as soon
as it is surjective on the kernels of the differentials out of that degree.**

This is the epimorphy counterpart of `HomologicalComplex.isIso_cyclesMap_of_bijective`, from
which it differs in asking nothing about injectivity. -/
theorem epi_cyclesMap_of_surjective (φ : K ⟶ L) (i j : ι) (hj : c.next i = j)
    (hsurj : ∀ y : L.X i, L.d i j y = 0 → ∃ x : K.X i, K.d i j x = 0 ∧ φ.f i x = y) :
    Epi (cyclesMap φ i) := by
  subst hj
  have hLi : Function.Injective (L.iCycles i) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hmap : ∀ a : K.cycles i, L.iCycles i (cyclesMap φ i a) = φ.f i (K.iCycles i a) :=
    fun a => congr($(cyclesMap_i φ i) a)
  refine (ModuleCat.epi_iff_surjective _).mpr fun b => ?_
  obtain ⟨x, hx, hxy⟩ := hsurj (L.iCycles i b) (congr($(L.iCycles_d i (c.next i)) b))
  obtain ⟨a, ha⟩ := K.exists_iCycles_eq i x hx
  exact ⟨a, hLi (by rw [hmap a, ha, hxy])⟩

end ModuleCat

end HomologicalComplex

namespace CochainComplex

variable {R : Type u} [Ring R] {K L : CochainComplex (ModuleCat.{v} R) ℤ}

/-- **Bijectivity on the cokernel of the differential of a two-term complex, elementwise.**  For
a morphism `φ` of cochain complexes of modules, the induced map
`X^0/d(X^{-1}) ⟶ (X')^0/d((X')^{-1})` is injective and surjective.  Both halves are written as
implications between membership statements, so that no subquotient appears and a caller can
discharge them by hand; this is the shape in which Stacks 0FUZ delivers them. -/
def IsBijectiveOnCokernel (φ : K ⟶ L) : Prop :=
  (∀ x : K.X 0, (∃ y : L.X (-1), L.d (-1) 0 y = φ.f 0 x) →
      ∃ z : K.X (-1), K.d (-1) 0 z = x) ∧
    ∀ y : L.X 0, ∃ (x : K.X 0) (z : L.X (-1)), φ.f 0 x + L.d (-1) 0 z = y

/-- **Surjectivity on the kernel of the differential of a two-term complex, elementwise.**  Every
cycle of the target in degree `-1` is the image of a cycle of the source.  Nothing is said about
injectivity: this is the shape in which Stacks 0FUZ delivers the degree-minus-one half, and it
is all that a surjection on `H^{-1}` needs. -/
def IsSurjectiveOnKernel (φ : K ⟶ L) : Prop :=
  ∀ y : L.X (-1), L.d (-1) 0 y = 0 → ∃ x : K.X (-1), K.d (-1) 0 x = 0 ∧ φ.f (-1) x = y

/-- **The degree-zero half of `CochainComplex.quasiIso_of_isZero_X_of_bijective`.**  For a
morphism of cochain complexes of modules vanishing outside degrees `-1` and `0`, bijectivity on
the cokernel of the single differential already makes the map on `H^0` an isomorphism; nothing
is needed about the kernel. -/
theorem isIso_homologyMap_zero_of_isBijectiveOnCokernel (φ : K ⟶ L)
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i))
    (hL : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (L.X i))
    (h : IsBijectiveOnCokernel φ) :
    IsIso (HomologicalComplex.homologyMap φ 0) := by
  exact HomologicalComplex.isIso_homologyMap_of_isIso_opcyclesMap φ 0 1 (by simp)
    ((hK 1 (by decide) (by decide)).eq_of_tgt _ _)
    ((hL 1 (by decide) (by decide)).eq_of_tgt _ _)
    (HomologicalComplex.isIso_opcyclesMap_of_bijective φ (-1) 0 (by simp) h.1 h.2)

/-- **The degree-minus-one half of `CochainComplex.quasiIso_of_isZero_X_of_bijective`, weakened
to an epimorphism.**  For a morphism of cochain complexes of modules vanishing outside degrees
`-1` and `0`, surjectivity on the kernel of the single differential already makes the map on
`H^{-1}` an epimorphism.  No injectivity on the kernel is assumed, which is what distinguishes
this from the quasi-isomorphism criterion. -/
theorem epi_homologyMap_negOne_of_isSurjectiveOnKernel (φ : K ⟶ L)
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i))
    (hL : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (L.X i))
    (h : IsSurjectiveOnKernel φ) :
    Epi (HomologicalComplex.homologyMap φ (-1)) := by
  exact HomologicalComplex.epi_homologyMap_of_epi_cyclesMap φ (-1) (-2) (by simp)
    ((hK (-2) (by decide) (by decide)).eq_of_src _ _)
    ((hL (-2) (by decide) (by decide)).eq_of_src _ _)
    (HomologicalComplex.epi_cyclesMap_of_surjective φ (-1) 0 (by simp) h)

/-- **The degree-zero data of Stacks 0FUZ, transported onto a morphism of two-term complexes of
modules.**  Given additive identifications of the four nonzero terms under which the two
differentials and the degree-zero component of `φ` become `d₁`, `d₂` and `q`, bijectivity on the
cokernel for `d₁`, `d₂`, `q` gives it for `φ`.

The two hypotheses `hinj` and `hsurj` are, verbatim, the second and third conjuncts of the
conclusion of `NaiveCotangent.naiveCotangentComplex_baseChange_homology` (Stacks 0FUZ), modulo
rewriting `y - f₀ x ∈ LinearMap.range d'` as `∃ z, f₀ x + d' z = y`. -/
theorem isBijectiveOnCokernel_of_addEquiv (φ : K ⟶ L)
    {M₁ N₁ M₂ N₂ : Type*} [AddCommGroup M₁] [AddCommGroup N₁] [AddCommGroup M₂]
    [AddCommGroup N₂]
    (u₁ : ToType (K.X (-1)) ≃+ M₁) (u₀ : ToType (K.X 0) ≃+ N₁)
    (v₁ : ToType (L.X (-1)) ≃+ M₂) (v₀ : ToType (L.X 0) ≃+ N₂)
    (d₁ : M₁ → N₁) (d₂ : M₂ → N₂) (q : N₁ → N₂)
    (hdK : ∀ z, u₀ (K.d (-1) 0 z) = d₁ (u₁ z))
    (hdL : ∀ z, v₀ (L.d (-1) 0 z) = d₂ (v₁ z))
    (hq : ∀ z, v₀ (φ.f 0 z) = q (u₀ z))
    (hinj : ∀ n : N₁, (∃ m : M₂, d₂ m = q n) → ∃ z : M₁, d₁ z = n)
    (hsurj : ∀ n : N₂, ∃ (m : N₁) (z : M₂), q m + d₂ z = n) :
    IsBijectiveOnCokernel φ :=
  ⟨fun x hx => exists_d_eq_of_addEquiv (u₁ := u₁) (u₀ := u₀) (v₁ := v₁) (v₀ := v₀)
      hdK hdL hq hinj x hx,
    fun y => exists_add_d_eq_of_addEquiv (u₀ := u₀) (v₁ := v₁) (v₀ := v₀) hdL hq hsurj y⟩

/-- **The degree-minus-one datum of Stacks 0FUZ, transported onto a morphism of two-term
complexes of modules.**  Given additive identifications of the four nonzero terms under which
the two differentials and the degree-minus-one component of `φ` become `d₁`, `d₂` and `p`,
surjectivity on the kernel for `d₁`, `d₂`, `p` gives it for `φ`.

The hypothesis `hsurj` is, verbatim, the fourth conjunct of the conclusion of
`NaiveCotangent.naiveCotangentComplex_baseChange_homology` (Stacks 0FUZ). -/
theorem isSurjectiveOnKernel_of_addEquiv (φ : K ⟶ L)
    {M₁ N₁ M₂ N₂ : Type*} [AddCommGroup M₁] [AddCommGroup N₁] [AddCommGroup M₂]
    [AddCommGroup N₂]
    (u₁ : ToType (K.X (-1)) ≃+ M₁) (u₀ : ToType (K.X 0) ≃+ N₁)
    (v₁ : ToType (L.X (-1)) ≃+ M₂) (v₀ : ToType (L.X 0) ≃+ N₂)
    (d₁ : M₁ → N₁) (d₂ : M₂ → N₂) (p : M₁ → M₂)
    (hdK : ∀ z, u₀ (K.d (-1) 0 z) = d₁ (u₁ z))
    (hdL : ∀ z, v₀ (L.d (-1) 0 z) = d₂ (v₁ z))
    (hp : ∀ z, v₁ (φ.f (-1) z) = p (u₁ z))
    (hsurj : ∀ m : M₂, d₂ m = 0 → ∃ n : M₁, d₁ n = 0 ∧ p n = m) :
    IsSurjectiveOnKernel φ :=
  fun y hy => exists_of_d_eq_zero_of_addEquiv (u₁ := u₁) (u₀ := u₀) (v₁ := v₁) (v₀ := v₀)
    hdK hdL hp hsurj y hy

/-! ### Composition, and invariance under an isomorphism of complexes

Both elementwise conditions are stable under composition, and both hold for an isomorphism of
complexes.  Together these two facts let a conclusion about a composite be read off from the
factors that are not isomorphisms.
-/

section Composition

variable {M : CochainComplex (ModuleCat.{v} R) ℤ}

/-- The degree-`i` component of a composite of morphisms of complexes of modules, on an
element. -/
private theorem comp_f_apply (φ : K ⟶ L) (ψ : L ⟶ M) (i : ℤ) (x : K.X i) :
    (φ ≫ ψ).f i x = ψ.f i (φ.f i x) :=
  congr($(HomologicalComplex.comp_f φ ψ i) x)

/-- A morphism of complexes of modules commutes with the differentials, on an element. -/
private theorem d_f_apply (φ : K ⟶ L) (i j : ℤ) (x : K.X i) :
    L.d i j (φ.f i x) = φ.f j (K.d i j x) :=
  congr($(φ.comm i j) x)

/-- The inverse of an isomorphism of complexes of modules undoes it, on an element. -/
private theorem inv_f_apply_f (φ : K ⟶ L) [IsIso φ] (i : ℤ) (x : K.X i) :
    (inv φ).f i (φ.f i x) = x := by
  rw [← comp_f_apply, IsIso.hom_inv_id, HomologicalComplex.id_f]
  rfl

/-- An isomorphism of complexes of modules undoes its inverse, on an element. -/
private theorem f_apply_inv_f (φ : K ⟶ L) [IsIso φ] (i : ℤ) (y : L.X i) :
    φ.f i ((inv φ).f i y) = y := by
  rw [← comp_f_apply, IsIso.inv_hom_id, HomologicalComplex.id_f]
  rfl

/-- **Bijectivity on the cokernel of the differential is stable under composition.**

Injectivity composes by lifting through the second factor and then through the first;
surjectivity composes because the second factor carries the correction term supplied by the
first into the image of the differential of the final target. -/
theorem IsBijectiveOnCokernel.comp {φ : K ⟶ L} {ψ : L ⟶ M}
    (hφ : IsBijectiveOnCokernel φ) (hψ : IsBijectiveOnCokernel ψ) :
    IsBijectiveOnCokernel (φ ≫ ψ) := by
  refine ⟨fun x hx => hφ.1 x (hψ.1 (φ.f 0 x)
    (hx.imp fun _ hw => hw.trans (comp_f_apply φ ψ 0 x))), fun y => ?_⟩
  obtain ⟨x₁, z₁, h₁⟩ := hψ.2 y
  obtain ⟨x₂, z₂, h₂⟩ := hφ.2 x₁
  refine ⟨x₂, ψ.f (-1) z₂ + z₁, ?_⟩
  rw [comp_f_apply, map_add, d_f_apply, ← add_assoc, ← map_add, h₂, h₁]

/-- **Surjectivity on the kernel of the differential is stable under composition.** -/
theorem IsSurjectiveOnKernel.comp {φ : K ⟶ L} {ψ : L ⟶ M}
    (hφ : IsSurjectiveOnKernel φ) (hψ : IsSurjectiveOnKernel ψ) :
    IsSurjectiveOnKernel (φ ≫ ψ) := fun y hy => by
  obtain ⟨x, hx, hxy⟩ := hψ y hy
  obtain ⟨w, hw, hwx⟩ := hφ x hx
  exact ⟨w, hw, (comp_f_apply φ ψ (-1) w).trans (by rw [hwx, hxy])⟩

/-- **An isomorphism of complexes of modules is bijective on the cokernel of the
differential.**  The witnesses are produced by the inverse, which is again a chain map. -/
theorem isBijectiveOnCokernel_of_isIso (φ : K ⟶ L) [IsIso φ] : IsBijectiveOnCokernel φ := by
  refine ⟨fun x hx => ?_, fun y => ⟨(inv φ).f 0 y, 0, ?_⟩⟩
  · obtain ⟨w, hw⟩ := hx
    exact ⟨(inv φ).f (-1) w, by rw [d_f_apply, hw, inv_f_apply_f]⟩
  · rw [f_apply_inv_f, map_zero, add_zero]

/-- **An isomorphism of complexes of modules is surjective on the kernel of the
differential.** -/
theorem isSurjectiveOnKernel_of_isIso (φ : K ⟶ L) [IsIso φ] : IsSurjectiveOnKernel φ :=
  fun y hy => ⟨(inv φ).f (-1) y, by rw [d_f_apply, hy, map_zero], f_apply_inv_f φ (-1) y⟩

end Composition

end CochainComplex

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}
  (𝒪 : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- **Epimorphy is stalkwise, over the stalk ring.**  A morphism of sheaves of `𝒪`-modules is
an epimorphism if and only if, for every point `x` of `X`, the induced map of stalks at `x` is
an epimorphism of `𝒪_x`-modules.

This is the epimorphy counterpart of `isIso_iff_forall_isIso_stalkFunctor_map`. -/
theorem epi_iff_forall_epi_stalkFunctor_map {M N : _root_.SheafOfModules.{u} 𝒪} (g : M ⟶ N) :
    Epi g ↔ ∀ x : X, Epi ((stalkFunctor 𝒪 x).map g) := by
  rw [epi_iff_surjective_stalkMap]
  exact forall_congr' fun x => (ModuleCat.epi_iff_surjective _).symm

/-- The map induced in degree `i` on homology by a morphism of cochain complexes of sheaves of
`𝒪`-modules is an epimorphism if and only if, for every point `x` of `X`, the map induced in
degree `i` on homology by the corresponding morphism of complexes of stalks is.

This is the epimorphy counterpart of `isIso_homologyMap_iff_forall_stalk`; the stalk functor is
exact, so it commutes with homology, and epimorphy is then detected on stalks. -/
theorem epi_homologyMap_iff_forall_stalk
    {K L : CochainComplex (_root_.SheafOfModules.{u} 𝒪) ℤ} (f : K ⟶ L) (i : ℤ) :
    Epi (HomologicalComplex.homologyMap f i) ↔ ∀ x : X,
      Epi (HomologicalComplex.homologyMap
        (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).map f) i) := by
  rw [epi_iff_forall_epi_stalkFunctor_map]
  exact forall_congr' fun x => (epi_map_iff_of_natIso
    (ShortComplex.homologyFunctorIso (stalkFunctor 𝒪 x))
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) i).map f)).symm

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.Scheme

open Stacks.SheafOfModules Stacks.Sheaves.RingedSpaceDifferentials

variable {X X' Y Y' : Scheme.{u}}

/-- `(g')^*NL_{X/Y}`, the pullback along `g' : X' ⟶ X` of the naive cotangent complex of
`f : X ⟶ Y`: the inverse image of `NL_{X/Y}` along `g'` with scalars extended to `𝒪_{X'}`,
which is the model of the pullback used by the library's Stacks 08TM/0E1Z development.

This is the `Scheme`-namespace spelling of
`Stacks.NaiveCotangentFlatBaseChange.pulledComplex`, which is the one definition of this
complex. -/
abbrev pullbackNaiveCotangentComplex (f : X ⟶ Y) (g' : X' ⟶ X) : CochainComplex X'.Modules ℤ :=
  Stacks.NaiveCotangentFlatBaseChange.pulledComplex f g'

/-- **The canonical map `(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` of a commutative square of schemes**: the
map of `Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison` for the canonical
base-ring comparison `AlgebraicGeometry.BaseChangeStalk.baseRingComparison` of the square.  Only
commutativity of the square is used, exactly as in the source, where cartesianness enters only in
the two cohomological conclusions. -/
def baseChangeNaiveCotangentComplexMap (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (w : g' ≫ f = f' ≫ g) :
    pullbackNaiveCotangentComplex f g' ⟶ naiveCotangentComplex f' :=
  Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison f f' g'
    (AlgebraicGeometry.BaseChangeStalk.baseRingComparison f f' g' g w)
    (AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp f f' g' g w)

/-- The complex of stalks at `x` of a complex of `𝒪_X`-modules, a complex of modules over the
stalk `𝒪_{X,x}`. -/
abbrev modulesStalkComplex (K : CochainComplex X.Modules ℤ) (x : X) :
    CochainComplex
      (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x)) ℤ :=
  ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- The map of complexes of stalks at `x` induced by a morphism of complexes of
`𝒪_X`-modules. -/
abbrev modulesStalkComplexMap {K L : CochainComplex X.Modules ℤ} (φ : K ⟶ L) (x : X) :
    modulesStalkComplex K x ⟶ modulesStalkComplex L x :=
  ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).mapHomologicalComplex
    (ComplexShape.up ℤ)).map φ

/-- `(g')^*NL_{X/Y}` has no terms outside degrees `-1` and `0`: it is the image of `NL_{X/Y}`
under two additive functors, inverse image and extension of scalars. -/
theorem isZero_pullbackNaiveCotangentComplex_X (f : X ⟶ Y) (g' : X' ⟶ X) (i : ℤ)
    (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((pullbackNaiveCotangentComplex f g').X i) :=
  let := Stacks.SheafOfModules.towerExtendScalars_additive.{u, u, u}
    (Opens.grothendieckTopology (X'.toRingedSpace : TopCat))
    (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.toRingedSpace.sheaf
    (ringedSpaceStructureMap g'.toLRSHom.toShHom)
  (Stacks.SheafOfModules.towerExtendScalars.{u, u, u}
      (Opens.grothendieckTopology (X'.toRingedSpace : TopCat))
      (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.toRingedSpace.sheaf
      (ringedSpaceStructureMap g'.toLRSHom.toShHom)).map_isZero
    ((_root_.SheafOfModules.pullback.{u}
        (AlgebraicGeometry.SheafOfModules.inverseImageRingHom
          g'.toLRSHom.toShHom.hom.base X.toRingedSpace.sheaf)).map_isZero
      (naiveCotangentComplex_isZero_X f i hneg hzero))

/-- The complex of stalks at a point of `(g')^*NL_{X/Y}` has no terms outside degrees `-1` and
`0`. -/
theorem isZero_modulesStalkComplex_pullbackNaiveCotangentComplex_X (f : X ⟶ Y) (g' : X' ⟶ X)
    (x : X') (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((modulesStalkComplex (pullbackNaiveCotangentComplex f g') x).X i) :=
  (AlgebraicGeometry.SheafOfModules.stalkFunctor X'.ringCatSheaf x).map_isZero
    (isZero_pullbackNaiveCotangentComplex_X f g' i hneg hzero)

/-- The complex of stalks at a point of `NL_{X/Y}` has no terms outside degrees `-1` and
`0`. -/
theorem isZero_modulesStalkComplex_naiveCotangentComplex_X (f : X ⟶ Y) (x : X) (i : ℤ)
    (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((modulesStalkComplex (naiveCotangentComplex f) x).X i) :=
  (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map_isZero
    (naiveCotangentComplex_isZero_X f i hneg hzero)

/-- **Stacks Project, Tag 0FV5.**  For a cartesian square of schemes the canonical map
`(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` induces an isomorphism on degree-zero cohomology.

The canonical map is the one constructed by
`AlgebraicGeometry.Scheme.baseChangeNaiveCotangentComplexMap` out of the commutativity of the
square; nothing about it is assumed.  This is a REDUCTION, not a proof of the tag: it takes one
explicit input, `hcoker`,
the degree-zero half of the elementwise conclusion of Stacks 0FUZ
(`NaiveCotangent.naiveCotangentComplex_baseChange_homology`) read on the two complexes of
stalks; the reduction of 0FUZ to those stalks is not assembled here.  See the tag clause. -/
theorem naiveCotangentComplex_baseChange_homologyMap_zero_isIso
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (hcart : IsPullback g' f' f g)
    (hcoker : ∀ x : X', CochainComplex.IsBijectiveOnCokernel
      (modulesStalkComplexMap (baseChangeNaiveCotangentComplexMap f g f' g' hcart.w) x)) :
    IsIso (HomologicalComplex.homologyMap
      (baseChangeNaiveCotangentComplexMap f g f' g' hcart.w) 0) :=
  (AlgebraicGeometry.SheafOfModules.isIso_homologyMap_iff_forall_stalk
    X'.ringCatSheaf (baseChangeNaiveCotangentComplexMap f g f' g' hcart.w) 0).2 fun x =>
      CochainComplex.isIso_homologyMap_zero_of_isBijectiveOnCokernel
        (modulesStalkComplexMap (baseChangeNaiveCotangentComplexMap f g f' g' hcart.w) x)
        (isZero_modulesStalkComplex_pullbackNaiveCotangentComplex_X f g' x)
        (isZero_modulesStalkComplex_naiveCotangentComplex_X f' x)
        (hcoker x)

/-- **Stacks Project, Tag 0FV5.**  For a cartesian square of schemes the canonical map
`(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` induces a surjection on degree-minus-one cohomology.

The canonical map is the one constructed by
`AlgebraicGeometry.Scheme.baseChangeNaiveCotangentComplexMap` out of the commutativity of the
square; nothing about it is assumed.  This is a REDUCTION, not a proof of the tag: it takes one
explicit input, `hker`,
the degree-minus-one half of the elementwise conclusion of Stacks 0FUZ at each stalk.  Only
surjectivity on the kernel is assumed, nothing about injectivity: the source's `H^{-1}`
assertion is a surjection and not an isomorphism, and that is exactly what the ring-level
statement provides and no more.  See the tag clause. -/
theorem naiveCotangentComplex_baseChange_homologyMap_negOne_epi
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (hcart : IsPullback g' f' f g)
    (hker : ∀ x : X', CochainComplex.IsSurjectiveOnKernel
      (modulesStalkComplexMap (baseChangeNaiveCotangentComplexMap f g f' g' hcart.w) x)) :
    Epi (HomologicalComplex.homologyMap
      (baseChangeNaiveCotangentComplexMap f g f' g' hcart.w) (-1)) :=
  (AlgebraicGeometry.SheafOfModules.epi_homologyMap_iff_forall_stalk
    X'.ringCatSheaf (baseChangeNaiveCotangentComplexMap f g f' g' hcart.w) (-1)).2 fun x =>
      CochainComplex.epi_homologyMap_negOne_of_isSurjectiveOnKernel
        (modulesStalkComplexMap (baseChangeNaiveCotangentComplexMap f g f' g' hcart.w) x)
        (isZero_modulesStalkComplex_pullbackNaiveCotangentComplex_X f g' x)
        (isZero_modulesStalkComplex_naiveCotangentComplex_X f' x)
        (hker x)

/-! ### The degree-zero conclusion through the sheaf of relative differentials

The degree-zero cohomology sheaf of `NL_{X/Y}` is `Ω_{X/Y}` (Stacks 0D0J,
`AlgebraicGeometry.Scheme.naiveCotangentComplexHomologyZeroIso`), and the canonical map on
sheaves of relative differentials of a cartesian square is an isomorphism (Stacks 01V0,
`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_of_isPullback`).  Transporting the
second along the first at both ends gives the degree-zero conclusion of Stacks 0FV5 with no
hypothesis beyond cartesianness of the square.

The map so obtained is written over Mathlib's `AlgebraicGeometry.Scheme.Modules.pullback`, which
is the functor `Ω` and its canonical maps are stated over; the map of complexes
`AlgebraicGeometry.Scheme.baseChangeNaiveCotangentComplexMap` above is instead written over the
inverse-image-then-extend-scalars model of the pullback, which is what Stacks 08TM and 0E1Z are
stated over in this library.  Identifying the two is the open input recorded at
`StacksFrontier/AlgebraicGeometry/EtaleAlgebra/FlatBaseChange/StructureSheaf.lean`, and until it is
available the two degree-zero statements stand side by side rather than one implying the other.
-/

/-- **The canonical map `(g')^*H^0(NL_{X/Y}) ⟶ H^0(NL_{X'/Y'})` of a commutative square of
schemes.**  The canonical map `(g')^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` of Stacks 01UV, read through the
degree-zero identification `H^0(NL) ≅ Ω` of Stacks 0D0J at both ends.

Only commutativity of the square is used, exactly as for
`AlgebraicGeometry.Scheme.baseChangeNaiveCotangentComplexMap`; cartesianness enters only in
`AlgebraicGeometry.Scheme.isIso_baseChangeNaiveCotangentHomologyZeroMap`. -/
def baseChangeNaiveCotangentHomologyZeroMap (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g) :
    (Modules.pullback g').obj ((naiveCotangentComplex f).homology 0) ⟶
      (naiveCotangentComplex f').homology 0 :=
  (Modules.pullback g').map (naiveCotangentComplexHomologyZeroIso f).hom ≫
    Hom.relativeDifferentialsMap g' f f' g w ≫
      (naiveCotangentComplexHomologyZeroIso f').inv

/-- **The degree-zero isomorphism of Stacks 0FV5, as an isomorphism of sheaves of modules.**
For a cartesian square of schemes, `(g')^*H^0(NL_{X/Y}) ≅ H^0(NL_{X'/Y'})`.  Its underlying
morphism is `AlgebraicGeometry.Scheme.baseChangeNaiveCotangentHomologyZeroMap`, by
`AlgebraicGeometry.Scheme.baseChangeNaiveCotangentHomologyZeroIso_hom`. -/
def baseChangeNaiveCotangentHomologyZeroIso (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (hcart : IsPullback g' f' f g) :
    (Modules.pullback g').obj ((naiveCotangentComplex f).homology 0) ≅
      (naiveCotangentComplex f').homology 0 :=
  ((Modules.pullback g').mapIso (naiveCotangentComplexHomologyZeroIso f)).trans
    ((@asIso _ _ _ _ (Hom.relativeDifferentialsMap g' f f' g hcart.w)
        (Hom.isIso_relativeDifferentialsMap_of_isPullback g' f' f g hcart)).trans
      (naiveCotangentComplexHomologyZeroIso f').symm)

/-- The isomorphism of `AlgebraicGeometry.Scheme.baseChangeNaiveCotangentHomologyZeroIso` has the
canonical map as its underlying morphism. -/
theorem baseChangeNaiveCotangentHomologyZeroIso_hom (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (hcart : IsPullback g' f' f g) :
    (baseChangeNaiveCotangentHomologyZeroIso f g f' g' hcart).hom =
      baseChangeNaiveCotangentHomologyZeroMap f g f' g' hcart.w :=
  rfl

/-- **Stacks Project, Tag 0FV5, the degree-zero isomorphism.**  For a cartesian square of
schemes the canonical map `(g')^*H^0(NL_{X/Y}) ⟶ H^0(NL_{X'/Y'})` is an isomorphism.

The map is `AlgebraicGeometry.Scheme.baseChangeNaiveCotangentHomologyZeroMap`, defined for every
commutative square; cartesianness is used only here, through Stacks 01V0.  See the tag clause
for what this statement does and does not cover. -/
@[stacks 0FV5 "the degree-zero ISOMORPHISM, for a CARTESIAN square, with no hypothesis beyond \
the cartesianness the source itself assumes.  The map is \
`AlgebraicGeometry.Scheme.baseChangeNaiveCotangentHomologyZeroMap`, the canonical map \
`(g')^*Omega_{X/Y} -> Omega_{X'/Y'}` of [Stacks, Tag 01UV] \
(`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap`, characterized there by compatibility \
with the universal derivations) read through the degree-zero identification \
`H^0(NL) = Omega` of [Stacks, Tag 0D0J] \
(`AlgebraicGeometry.Scheme.naiveCotangentComplexHomologyZeroIso`) at both ends.  Like the \
source's own map it is defined from COMMUTATIVITY alone, and cartesianness is used only for \
invertibility, through [Stacks, Tag 01V0] \
(`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_of_isPullback`, which is itself \
proved outright from the cartesian-stalk localization and \
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtalePushout`).  This is a SECOND, \
independent route to the tag's `H^0` clause, through the sheaf of relative differentials.  The \
tag's two clauses for the canonical map of COMPLEXES are proved outright at \
`Stacks.NaiveCotangentBaseChange.isIso_homologyMap_zero_baseChangeMapOfComparison` and \
`Stacks.NaiveCotangentBaseChange.epi_homologyMap_negOne_baseChangeMapOfComparison`, which take \
the same canonical base-ring comparison of the square that [Stacks, Tag 0FJZ] does.  NOT \
covered here: that the map of this statement is the one induced on `H^0` by that map of \
complexes.  Comparing the two needs the identification of Mathlib's \
`AlgebraicGeometry.Scheme.Modules.pullback` -- the functor `Omega` and its canonical maps are \
stated over -- with the inverse-image-then-extend-scalars model that map of complexes is \
stated over, which is the open input recorded at \
`StacksFrontier/AlgebraicGeometry/EtaleAlgebra/FlatBaseChange/StructureSheaf.lean`"]
theorem isIso_baseChangeNaiveCotangentHomologyZeroMap (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (hcart : IsPullback g' f' f g) :
    IsIso (baseChangeNaiveCotangentHomologyZeroMap f g f' g' hcart.w) :=
  Iso.isIso_hom (baseChangeNaiveCotangentHomologyZeroIso f g f' g' hcart)

end AlgebraicGeometry.Scheme

end

end
