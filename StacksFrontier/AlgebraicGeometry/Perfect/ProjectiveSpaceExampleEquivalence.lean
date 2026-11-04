module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryDevissage
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexQuasicoherent
public import StacksFrontier.CategoryTheory.Triangulated.AdjointsForExactFunctors
public import StacksFrontier.CategoryTheory.Triangulated.Generators
public import StacksFrontier.AlgebraicGeometry.RingedSpace.KFlatResolution
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveGeneratorAlgebra
public import StacksCore.Tactic.StacksAttribute

/-!
# Beilinson's example equivalence for projective space

Let `A` be a commutative ring, let `X = ℙⁿ_A` and let
`P = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)` be the twist sum of Tag 0CS8. Writing `E = Hom^{dg}(P, P)`
for the endomorphism differential graded algebra of `P`, the functor

`- ⊗_E^𝐋 P : D(E) ⟶ D(𝒪_X)`

of Tag 09LX is a triangulated equivalence sending the regular module to `P`. This is Beilinson's
equivalence, [Stacks, Tag 0BQU], read with the endomorphism differential graded algebra of `P` in
place of the upper triangular matrix algebra `R` of Tag 0CS9.

The argument is the source's. Full faithfulness is Tag 09LZ, the adjunction with derived Hom is
Tag 09LY, and the equivalence follows from Tag 09J1 once the right adjoint `RHom(P, -)` is shown
to kill no nonzero object — which is what it means for `P` to generate `D(𝒪_X)` weakly, since
`RHom(P, Y) = 0` forces every `Hom(P⟦a⟧, Y)` to vanish by adjunction.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveGenerator.isWeakTriangulatedGenerator_q_regularModule`:
  the image of the regular module in `D(A, d)` is a weak generator, for a differential graded
  algebra whose carrier lies in a universe of its own. This is the shape the endomorphism
  differential graded algebra of a complex of sheaves needs.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.isZero_of_isZero_derivedHom`: on a ringed site,
  if the complex `K` weakly generates `D(𝒪)` then the right adjoint `RHom(K, -)` of Tag 09LY
  kills no nonzero object. This is the hypothesis `hker` of Tag 09J1.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.tensorWithComplexDerived_isEquivalence`: on a
  ringed site, `- ⊗_E^𝐋 K` is a triangulated equivalence as soon as `K` weakly generates
  `D(𝒪)`, `RHom(K, -)` is exact and commutes with direct sums, and `E` computes the ext groups
  of `K`.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.twistSum_tensorDerived_isEquivalence`: the same
  statement at `X = ℙⁿ_A` and `K` the twist sum `P` in degree zero.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.twistSumTensorDerivedObjRegularIso`: the functor
  sends the regular module to `P`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveGenerator.derivedHomWithComplexCommShift`: the commutation
  of `RHom(K, -)` with the translation that the adjunction of Tag 09LY induces from the one on
  `- ⊗_E^𝐋 K`. It is recorded as an instance because the exactness of `RHom(K, -)` cannot be
  stated without it.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.projectiveSpaceSite`: `ℙⁿ_A` read as a ringed
  site, so that the derived tensor construction of Tag 09LX applies to it.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.twistSumComplex`: the twist sum `P` of Tag 0CS8
  placed in cohomological degree zero.

## Implementation notes

*What is proved and what is carried.* The equivalence and its exactness are proved; the image of
the regular module is identified with `P`. Two things of the source's statement are not here.

* The source's source category is `D(R)` for the upper triangular matrix algebra `R` of
  Tag 0CS9, identified with `D(E)` through `E = R`, an identification the sibling module
  `StacksFrontier/AlgebraicGeometry/Perfect/ProjectiveGeneratorAlgebra.lean` explicitly does not
  establish. The category here is therefore `D(E)` for the endomorphism differential graded
  algebra `E = Hom^{dg}(P, P)` of `P`, which is the same functor of the same object but written
  over the algebra the construction of Tag 09LX produces.
* `A`-linearity is not stated. The differential graded category of complexes on a ringed site
  has `ℤ` as its ground ring (Tag 09L9), so the only `Linear` structures this library supplies
  on `D(E)` are over `ℤ`; an `A`-linear structure coming from the central action of `A` on `E`
  is not available, and inventing one here would be stating a different notion.

*Which inputs of Tag 09LZ are discharged.* Four of them, here. The adjunction of Tag 09LY is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_adj_derivedHomWithComplex`, so the right
adjoint is `RHom(K, -)` itself and neither the functor nor the adjunction is a hypothesis, and
its commutation with the translation is the one the adjunction induces
(`Stacks.AlgebraicGeometry.ProjectiveGenerator.derivedHomWithComplexCommShift`). The dévissage
of Tag 0FQE is
`DifferentialGradedModule.General.property_of_coproducts_of_two_out_of_three_of_shifts`, which
is the form of that tag with the carrier of the algebra in a universe of its own, so it applies
to `E`. The direct sums of `D(E)` are
`DifferentialGradedModule.General.hasCoproducts_derivedCategory`, found by instance search in
the same shape. The weak generation of `D(E)` by the regular module is
`Stacks.AlgebraicGeometry.ProjectiveGenerator.isWeakTriangulatedGenerator_q_regularModule`
below, which is the same proof as
`DifferentialGradedModule.isWeakTriangulatedGenerator_q_regularModule` run against the
independent-universe dévissage.

*What is still carried.* Three inputs of Tag 09LZ, and `hKgen`.

* The exactness of `RHom(K, -)`. Mathlib's
  `CategoryTheory.Adjunction.isTriangulated_rightAdjoint` would give it from the exactness of
  `- ⊗_E^𝐋 K`, but that is the second conjunct of the conclusion here, and this library obtains
  it only the other way round, from the exactness of the right adjoint
  (`CategoryTheory.Adjunction.isTriangulated_leftAdjoint`). The independent route,
  `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_isTriangulated`, asks for the exactness
  of `- ⊗_E K` on `K(Mod_(E, d))`, which Tag 09LW supplies as
  `AlgebraicGeometry.RingedSite.tensorWithComplexHomotopy_isTriangulated` only against the
  pretriangulated structure whose distinguished triangles come from admissible short exact
  sequences, whereas `D(E, d)` and the dévissage of Tag 0FQE are read here in the structure whose
  distinguished triangles are the cone triangles. The two classes of triangles agree by
  Tag 09KH, which this library does not formalize.
* The commutation of `RHom(K, -)` with direct sums. This is the only use the source's proof makes
  of its hypothesis (1), that `K` represents a compact object of `D(𝒪)`, and no carrier for it
  is available here.
* `hExt`, hypothesis (2) of Tag 09LZ, that `E` computes the ext groups of `K`.
* `hKgen`, the weak generation of `D(𝒪_X)` by `P`.

*About `hKgen`.* It is literally the conclusion of Tag 0A9V, which this library has as
`Stacks.AlgebraicGeometry.ExampleGenerator.isWeakTriangulatedGenerator_twistSum_of_twists`, and
which is itself conditional: it carries `hvanish`, the vanishing criterion the source obtains
from Tag 0BQR applied to the ample invertible sheaf `𝒪_X(1)` of Tag 01Q2. Tag 0BQR has no
carrier in this library, so `hKgen` is a declared hypothesis instead. Two further mismatches keep
Tag 0A9V from being plugged in directly rather than carried: it is stated for the *locally
small* model of the derived category of
`SheafOfModules (projRingSheaf (polyGrading A n))`, whereas the functor of Tag 09LX is formed in
the standard derived category of the ambient module category of the ringed site; and it is stated
for the whole of `D(𝒪_X)`, whereas the source's statement, and the scope on which `hvanish` is
available from Tag 0BQR, is `D_QCoh(𝒪_X)`. Neither identification is made here, so no transport
of Tag 0A9V is claimed: `hKgen` is taken in the model in which the functor lives.

None of the carried hypotheses is false — each is a theorem of the source, or of this library at
a smaller universe — but none is witnessed here.

## References

* [Stacks Project, Tag 0BQU](https://stacks.math.columbia.edu/tag/0BQU)
* [Stacks Project, Tag 09J1](https://stacks.math.columbia.edu/tag/09J1) for the criterion,
  [Tag 09LX](https://stacks.math.columbia.edu/tag/09LX) for the functor,
  [Tag 09LY](https://stacks.math.columbia.edu/tag/09LY) for the adjunction,
  [Tag 09LZ](https://stacks.math.columbia.edu/tag/09LZ) for full faithfulness,
  [Tag 0FQE](https://stacks.math.columbia.edu/tag/0FQE) for the dévissage,
  [Tag 09LW](https://stacks.math.columbia.edu/tag/09LW) with
  [Tag 09KH](https://stacks.math.columbia.edu/tag/09KH) for the exactness that is carried,
  [Tag 0CS8](https://stacks.math.columbia.edu/tag/0CS8) for `P`,
  [Tag 0CS9](https://stacks.math.columbia.edu/tag/0CS9) for `R`,
  [Tag 0A9V](https://stacks.math.columbia.edu/tag/0A9V) for the generation of `D_QCoh(𝒪_X)`
  by `P`, and [Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR) with
  [Tag 01Q2](https://stacks.math.columbia.edu/tag/01Q2) for the vanishing criterion Tag 0A9V
  carries.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.RingedSite
open DifferentialGradedModule

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

namespace Stacks.AlgebraicGeometry.ProjectiveGenerator

universe u v w t s

/-! ### The regular module generates the derived category at independent universes -/

section Regular

variable {R : Type u} [CommRing R]

/-- **The algebra generates its derived category**, with the carrier of the algebra in a universe
of its own: the image of the regular module `A` in `D(A, d)` is a weak generator, so that an
object of `D(A, d)` receiving only zero morphisms from the shifts `A[k]` is zero.

This is `DifferentialGradedModule.isWeakTriangulatedGenerator_q_regularModule` with the universe
of the base ring and the universe of the carrier of `A` independent of one another, and read in
the pretriangulated structure whose distinguished triangles are the cone triangles. That is the
shape the endomorphism differential graded algebra of a complex of modules on a ringed site
needs: it is an algebra over `ℤ`, whose universe is `0`, with a carrier in the section universe
of the site, and the derived category of Tag 09LX is formed in the cone-triangle structure.

The proof is the one of the single-universe statement, with the dévissage of Tag 0FQE taken in
the matching shape
`DifferentialGradedModule.General.property_of_coproducts_of_two_out_of_three_of_shifts`. The
property "every morphism to a shift of `K` vanishes" is closed under direct sums and satisfies
two-out-of-three in a distinguished triangle, and it holds on every shift of the regular module
because `K` receives no nonzero morphism from one; the dévissage then gives it at `K` itself,
where it says that the identity of `K` is zero. -/
theorem isWeakTriangulatedGenerator_q_regularModule (A : DifferentialGradedAlgebra.{u, v} R) :
    ObjectProperty.IsWeakTriangulatedGenerator (ObjectProperty.singleton
      ((toHomotopyCategory A ⋙ (quasiIsomorphisms.{u, v, v} A).Q).obj (regularModule A))) := by
  set E := (toHomotopyCategory A ⋙ (quasiIsomorphisms.{u, v, v} A).Q).obj (regularModule A)
  intro K hK
  set P : ObjectProperty (DifferentialGradedModule.derivedCategory.{u, v, v} A) :=
    (ObjectProperty.singleton K).shiftClosure ℤ
  have hPK : P K :=
    ⟨K, 0, ((shiftFunctorZero (DifferentialGradedModule.derivedCategory.{u, v, v} A) ℤ).app K).symm,
      (ObjectProperty.singleton_iff K K).2 rfl⟩
  -- the right orthogonal of a shift-stable property is shift-stable
  have hshiftK : ∀ m : ℤ, ((ObjectProperty.singleton E).shiftClosure ℤ).rightOrthogonal
      ((shiftFunctor (DifferentialGradedModule.derivedCategory.{u, v, v} A) m).obj K) :=
    fun m => ((ObjectProperty.singleton E).shiftClosure ℤ).rightOrthogonal.le_shift m _ hK
  have key : ∀ Z, P.leftOrthogonal Z := by
    refine General.property_of_coproducts_of_two_out_of_three_of_shifts A P.leftOrthogonal
      (fun Kf hKf => ?_) (fun Δ hΔ => ⟨?_, ?_, ?_⟩) (fun k => ?_)
    · exact fun Y f hY => Sigma.hom_ext _ _ fun i => by
        rw [comp_zero]; exact hKf i _ hY
    · exact fun h₁ h₂ => P.leftOrthogonal.ext_of_isTriangulatedClosed₃ Δ hΔ h₁ h₂
    · exact fun h₁ h₃ => P.leftOrthogonal.ext_of_isTriangulatedClosed₂ Δ hΔ h₁ h₃
    · exact fun h₂ h₃ => P.leftOrthogonal.ext_of_isTriangulatedClosed₁ Δ hΔ h₂ h₃
    · intro Y f hY
      obtain ⟨K', m, e, hK'⟩ := hY
      rw [ObjectProperty.singleton_iff] at hK'
      subst hK'
      rw [← cancel_mono e.hom, zero_comp]
      exact hshiftK m (f ≫ e.hom) ⟨E, k, Iso.refl _, (ObjectProperty.singleton_iff E E).2 rfl⟩
  exact (IsZero.iff_id_eq_zero K).2 (key K (𝟙 K) hPK)

end Regular

/-! ### The equivalence on a ringed site -/

section Site

variable (X : _root_.AlgebraicGeometry.RingedSite.{u, v, w})
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

/-- **`RHom(K, -)` commutes with the translation**: the `CommShift` structure that the adjunction
of Tag 09LY induces on the right adjoint from the one `- ⊗_E^𝐋 K` carries, and the unique one
compatible with the unit (`CategoryTheory.Adjunction.CommShift.compatibilityUnit_unique_right`).

It is an instance because `Functor.IsTriangulated` takes the commutation with the translation as
a class parameter, so the exactness of `RHom(K, -)` — which
`Stacks.AlgebraicGeometry.ProjectiveGenerator.tensorWithComplexDerived_isEquivalence` carries as
a hypothesis — cannot be stated without it. -/
instance derivedHomWithComplexCommShift :
    (derivedHomWithComplex.{u, v, w, t, s} X K).CommShift ℤ :=
  (tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s} X K).rightAdjointCommShift ℤ

/-- The right adjoint `RHom(K, -)` of Tag 09LY kills no nonzero object, as soon as `K` weakly
generates `D(𝒪)`.

If `RHom(K, Y)` is a zero object then every morphism to it vanishes, so by the adjunction every
morphism `(- ⊗_E^𝐋 K) W ⟶ Y` vanishes; taking `W` to be a shift of the regular module and using
that `- ⊗_E^𝐋 K` sends the regular module to `K` and commutes with the translation, every
morphism from a shift of `K` to `Y` vanishes. That is the orthogonality a weak generator turns
into the vanishing of `Y`. -/
theorem isZero_of_isZero_derivedHom
    {G : DerivedCategory (TensorModO.{u, v, w, t, s} X) ⥤
        DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
          (RingedSite.Rep.{u, v, w, t, s, 0} X ℤ K).algebra}
    (adj : tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⊣ G)
    (hKgen : (ObjectProperty.singleton
      (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))).IsWeakTriangulatedGenerator)
    (Y : DerivedCategory (TensorModO.{u, v, w, t, s} X)) (hY : IsZero (G.obj Y)) :
    IsZero Y := by
  refine hKgen Y ?_
  intro Z g hZ
  obtain ⟨E, a, e, hE⟩ := hZ
  obtain rfl : DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K) = E :=
    (ObjectProperty.singleton_iff _ _).mp hE
  have hzero : ∀ (W : DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
      (RingedSite.Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
      (f : (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj W ⟶ Y), f = 0 := fun W f =>
    (adj.homEquiv W Y).injective (hY.eq_of_tgt _ _)
  have hiso : (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj
        (((quasiIsomorphisms (RingedSite.Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj
          ((toHomotopyCategory (RingedSite.Rep.{u, v, w, t, s, 0} X ℤ K).algebra).obj
            ((RingedSite.Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj
              (liftComplex.{u, v, w, t, s} X K))))⟦a⟧) ≅
      (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))⟦a⟧ :=
    ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).commShiftIso a).app _ ≪≫
      (shiftFunctor (DerivedCategory (TensorModO.{u, v, w, t, s} X)) a).mapIso
        (tensorWithComplexDerivedObjRegularIso.{u, v, w, t, s} X K)
  rw [← cancel_epi (hiso.hom ≫ e.inv), comp_zero, Category.assoc]
  exact hzero _ _

/-- **The derived tensor product with `K` is a triangulated equivalence** as soon as `K` weakly
generates `D(𝒪)`, the right adjoint `RHom(K, -)` is exact and commutes with direct sums, and `E`
computes the ext groups of `K`.

Full faithfulness is Tag 09LZ, exactness follows from exactness of the right adjoint, and the
equivalence is Tag 09J1 applied to the adjunction of Tag 09LY, whose kernel hypothesis is
`Stacks.AlgebraicGeometry.ProjectiveGenerator.isZero_of_isZero_derivedHom`. The adjunction is
the one Tag 09LY constructs,
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_adj_derivedHomWithComplex`, so the right
adjoint is `RHom(K, -)` itself; the dévissage of Tag 0FQE, the direct sums of `D(E, d)` and the
weak generation of `D(E, d)` by the regular module are discharged. The exactness of `RHom(K, -)`
is a hypothesis because the exactness of `- ⊗_E^𝐋 K` is the conclusion; its commutation with
direct sums is the source's compactness hypothesis (1). See the module's implementation notes. -/
theorem tensorWithComplexDerived_isEquivalence
    [(derivedHomWithComplex.{u, v, w, t, s} X K).IsTriangulated]
    [∀ ι : Type (max u v w t s), PreservesColimitsOfShape (Discrete ι)
      (derivedHomWithComplex.{u, v, w, t, s} X K)]
    (hExt : ∀ n : ℤ, Function.Bijective
      (fun f : repRegularDerived.{u, v, w, t, s} X K ⟶
          (repRegularDerived.{u, v, w, t, s} X K)⟦n⟧ =>
        (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).map f))
    (hKgen : (ObjectProperty.singleton
      (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))).IsWeakTriangulatedGenerator) :
    (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).IsEquivalence ∧
      (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).IsTriangulated := by
  let adj := tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s} X K
  have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have hff := tensorWithComplexDerived_fullyFaithful X K adj
    (isWeakTriangulatedGenerator_q_regularModule.{0, max u v w t s}
      (RingedSite.Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
    hExt
    (fun T => General.property_of_coproducts_of_two_out_of_three_of_shifts
      (RingedSite.Rep.{u, v, w, t, s, 0} X ℤ K).algebra T)
  have := hff.full
  have := hff.faithful
  have := adj.isTriangulated_leftAdjoint
  exact ⟨isEquivalence_of_fullyFaithful_of_adjunction_of_ker_eq_zero
    (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K) _ adj
    (isZero_of_isZero_derivedHom.{u, v, w, t, s} X K adj hKgen), inferInstance⟩

end Site

/-! ### The equivalence on projective space -/

section ProjectiveSpace

variable (A : Type u) [CommRing A] (n : ℕ)

/-- `ℙⁿ_A` read as a ringed site: the poset of its open sets with the open-cover topology and
its structure sheaf. This is the shape in which the derived tensor construction of Tag 09LX
applies. -/
def projectiveSpaceSite : _root_.AlgebraicGeometry.RingedSite.{u, u, u} :=
  _root_.AlgebraicGeometry.RingedSpace.ringedSite
    (projectiveSpaceOverRing n (.of A)).toRingedSpace

/-- The twist sum `P = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)` of Tag 0CS8, placed in cohomological
degree zero. -/
def twistSumComplex : CochainComplex (ModO.{u, u, u, u} (projectiveSpaceSite A n)) ℤ :=
  letI : HasZeroObject (ModO.{u, u, u, u} (projectiveSpaceSite A n)) :=
    tensorModOHasZeroObject.{u, u, u, u, u} (projectiveSpaceSite A n)
  (CochainComplex.singleFunctor (ModO.{u, u, u, u} (projectiveSpaceSite A n)) 0).obj
    (twistSum A n)

/-- **Stacks 0BQU**, with the matrix description of the endomorphism algebra and `A`-linearity
omitted and the inputs of Tag 09LZ and Tag 0A9V carried. *"Let `A` be a ring. Let
`X = ℙⁿ_A = Proj(S)` where `S = A[X₀, …, Xₙ]`. With `P` as in Tag 0CS8 and `R` as in Tag 0CS9
the functor `- ⊗_R^𝐋 P : D(R) ⟶ D_QCoh(𝒪_X)` is an `A`-linear equivalence of triangulated
categories sending `R` to `P`."*

What is proved: for `P` the twist sum of Tag 0CS8 on `ℙⁿ_A`, placed in degree zero, and
`E = Hom^{dg}(P, P)` its endomorphism differential graded algebra, the functor `- ⊗_E^𝐋 P` of
Tag 09LX is an equivalence of categories and is exact. The image of the regular module is `P`,
which is
`Stacks.AlgebraicGeometry.ProjectiveGenerator.twistSumTensorDerivedObjRegularIso`.

What is not: the identification `E = R` with the upper triangular matrix algebra of Tag 0CS9,
which this library does not have, so the source category is `D(E)` rather than `D(R)`; and
`A`-linearity, for which the library supplies no `A`-linear structure on `D(E)`. The carried
hypotheses are the three inputs of Tag 09LZ this library does not discharge — the exactness of
`RHom(P, -)`, its commutation with direct sums and `hExt` — together with `hKgen`, the weak
generation of `D(𝒪_X)` by `P`, which is the conclusion of Tag 0A9V; see the module's
implementation notes for why Tag 0A9V is carried rather than applied. The adjunction of
Tag 09LY, the dévissage of Tag 0FQE, the direct sums of `D(E)` and the weak generation of `D(E)`
by the regular module are *not* carried: each is supplied by a carrier of this library. -/
@[stacks 0BQU "RESTRICTED. UNCONDITIONAL HERE is the assembly of Beilinson's argument at \
X = ℙⁿ_A with P the twist sum of Tag 0CS8 placed in degree zero: the adjunction \
- ⊗_E^𝐋 P ⊣ RHom(P, -) of Tag 09LY, supplied by its carrier \
AlgebraicGeometry.RingedSite.tensorWithComplexDerived_adj_derivedHomWithComplex, together with \
the commutation of RHom(P, -) with the translation that the adjunction induces \
(derivedHomWithComplexCommShift); the dévissage of Tag 0FQE, supplied by its carrier \
DifferentialGradedModule.General.property_of_coproducts_of_two_out_of_three_of_shifts; the \
direct sums of D(E), supplied by \
DifferentialGradedModule.General.hasCoproducts_derivedCategory; the weak generation of D(E) by \
the regular module, proved here as isWeakTriangulatedGenerator_q_regularModule, the \
independent-universe cone-triangle form of \
DifferentialGradedModule.isWeakTriangulatedGenerator_q_regularModule; full faithfulness by \
Tag 09LZ; the conversion of the weak-generator property of P into the kernel condition hker of \
Tag 09J1 (isZero_of_isZero_derivedHom); and the conclusion by Tag 09J1 \
that the functor - ⊗_E^𝐋 P of Tag 09LX is an equivalence of categories and is exact. The \
clause 'sending R to P' is twistSumTensorDerivedObjRegularIso. NOT PROVED: the identification \
of E = Hom^dg(P, P) with the upper triangular matrix algebra R of Tag 0CS9, so the source \
category is D(E) and not D(R); and A-linearity, the library supplying no A-linear structure on \
D(E), the ground ring of the differential graded category of complexes on a ringed site being ℤ \
by Tag 09L9. CARRIED HYPOTHESES. (i) hKgen, that P weakly generates D(O_X). This is exactly the \
conclusion of Tag 0A9V, which this library has as \
Stacks.AlgebraicGeometry.ExampleGenerator.isWeakTriangulatedGenerator_twistSum_of_twists and \
which is itself conditional: it carries hvanish, the vanishing criterion the source obtains \
from Tag 0BQR applied to the ample invertible sheaf O_X(1) of Tag 01Q2. Tag 0BQR has no carrier \
in this library, so it is carried as a \
declared hypothesis here and is neither proved nor duplicated. Tag 0A9V is moreover stated for \
the locally small model of the derived category of SheafOfModules (projRingSheaf (polyGrading A \
n)) and for the whole of D(O_X), whereas the functor of Tag 09LX is formed in the standard \
derived category of the ambient module category of the ringed site and the source's statement \
is about D_QCoh(O_X), which is also the scope on which hvanish is available from Tag 0BQR; \
neither identification is made here, so no transport of Tag 0A9V is claimed and hKgen is taken \
in the model in which the functor lives. (ii) The three inputs of Tag 09LZ this library does \
not discharge. The exactness of RHom(P, -): Mathlib's \
CategoryTheory.Adjunction.isTriangulated_rightAdjoint would give it from the exactness of \
- ⊗_E^𝐋 P, but that is the second conjunct of the conclusion here, and the independent route \
AlgebraicGeometry.RingedSite.tensorWithComplexDerived_isTriangulated needs the exactness of \
- ⊗_E P on K(Mod_E), which Tag 09LW supplies only against the pretriangulated structure whose \
distinguished triangles come from admissible short exact sequences, whereas D(E) and the \
dévissage of Tag 0FQE are read in the structure whose distinguished triangles are the cone \
triangles, the two classes agreeing by Tag 09KH, which this library does not formalize. The \
commutation of RHom(P, -) with direct sums, which is the only use the source's proof makes of \
its hypothesis (1) that P represents a compact object of D(O_X). And hExt, hypothesis (2) of \
Tag 09LZ that E computes the ext groups of P"]
theorem twistSum_tensorDerived_isEquivalence
    [(derivedHomWithComplex.{u, u, u, u, u} (projectiveSpaceSite A n)
      (twistSumComplex A n)).IsTriangulated]
    [∀ ι : Type u, PreservesColimitsOfShape (Discrete ι)
      (derivedHomWithComplex.{u, u, u, u, u} (projectiveSpaceSite A n)
        (twistSumComplex A n))]
    (hExt : ∀ m : ℤ, Function.Bijective
      (fun f : repRegularDerived.{u, u, u, u, u} (projectiveSpaceSite A n)
            (twistSumComplex A n) ⟶
          (repRegularDerived.{u, u, u, u, u} (projectiveSpaceSite A n)
            (twistSumComplex A n))⟦m⟧ =>
        (tensorWithComplexDerived.{u, u, u, u, u, 0} (projectiveSpaceSite A n) ℤ
          (twistSumComplex A n)).map f))
    (hKgen : (ObjectProperty.singleton (DerivedCategory.Q.obj
      (liftComplex.{u, u, u, u, u} (projectiveSpaceSite A n)
        (twistSumComplex A n)))).IsWeakTriangulatedGenerator) :
    (tensorWithComplexDerived.{u, u, u, u, u, 0} (projectiveSpaceSite A n) ℤ
        (twistSumComplex A n)).IsEquivalence ∧
      (tensorWithComplexDerived.{u, u, u, u, u, 0} (projectiveSpaceSite A n) ℤ
        (twistSumComplex A n)).IsTriangulated :=
  tensorWithComplexDerived_isEquivalence.{u, u, u, u, u} (projectiveSpaceSite A n)
    (twistSumComplex A n) hExt hKgen

/-- **Stacks 0BQU**, the clause *"sending `R` to `P`"*: the derived tensor product with the twist
sum sends the regular module of its endomorphism differential graded algebra to the twist sum
itself.

This is `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedObjRegularIso` at `X = ℙⁿ_A` and
`K = P`. The source writes the regular module as `R`, which this library does not identify with
the matrix algebra of Tag 0CS9; it is here the regular module over `E = Hom^{dg}(P, P)`. -/
@[stacks 0BQU "the clause 'sending R to P', with the regular module read over E = Hom^dg(P, P) \
rather than over the upper triangular matrix algebra R of Tag 0CS9, the identification E = R \
not being available in this library"]
def twistSumTensorDerivedObjRegularIso :
    (tensorWithComplexDerived.{u, u, u, u, u, 0} (projectiveSpaceSite A n) ℤ
        (twistSumComplex A n)).obj
        ((quasiIsomorphisms (RingedSite.Rep.{u, u, u, u, u, 0} (projectiveSpaceSite A n) ℤ
            (twistSumComplex A n)).algebra).Q.obj
          ((toHomotopyCategory (RingedSite.Rep.{u, u, u, u, u, 0} (projectiveSpaceSite A n) ℤ
              (twistSumComplex A n)).algebra).obj
            ((RingedSite.Rep.{u, u, u, u, u, 0} (projectiveSpaceSite A n) ℤ
                (twistSumComplex A n)).functor.obj
              (liftComplex.{u, u, u, u, u} (projectiveSpaceSite A n)
                (twistSumComplex A n))))) ≅
      DerivedCategory.Q.obj (liftComplex.{u, u, u, u, u} (projectiveSpaceSite A n)
        (twistSumComplex A n)) :=
  tensorWithComplexDerivedObjRegularIso.{u, u, u, u, u} (projectiveSpaceSite A n)
    (twistSumComplex A n)

end ProjectiveSpace

end Stacks.AlgebraicGeometry.ProjectiveGenerator

end
