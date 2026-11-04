module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectDerivedSections
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.RingTheory.Dualizing.Relative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens

/-!
# Relative dualizing complexes on a compatible pair of affine opens

Let `f : X ⟶ S` be flat and locally of finite presentation and let `(K, ξ)` be a relative
dualizing complex for `f`. Let `U ⊆ X` be an affine open lying over an affine open `V ⊆ S`, and
write `R = Γ(S, V)` and `A = Γ(X, U)`; the isomorphisms `Spec A ≅ U` and `Spec R ≅ V` turn the
inclusions of `U` and `V` into the commutative square of open immersions of Stacks 0E2U, and the
equivalence `D(A) ≌ D_QCoh(𝒪_{Spec A})` of Stacks 06Z0 carries `K|_U` to the complex of
`A`-modules `RΓ(U, K)`. Then `RΓ(U, K)` is a relative dualizing complex for `R → A` in the sense
of Stacks 0E2C.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.AffineDiagonalComparison` is the affine comparison
  of the three operations the source's proof invokes — `Δ_*𝒪_X`, `L pr₁^*` and
  `R SheafHom_{𝒪_W}` — at a chart of `W` over `A ⊗_R A`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isRelativeDualizingComplex_derivedSections` is Stacks 0E2U: the
  derived sections of `K` over `U` form a relative dualizing complex for `R → A`.

## Implementation notes

**The correspondence of Stacks 06Z0 is `RΓ(U, -)`.** On an affine open the quasi-inverse of
derived sheafification is derived sections, so the object of `D(A)` the source attaches to `K|_U`
is `AlgebraicGeometry.derivedSectionsUnbounded X U` applied to `K`. This is the same crossing
that the pseudo-coherence clause of Stacks 0DI2 is stated over, so no further comparison
intervenes.

**The pseudo-coherence clause is proved.** A relatively perfect object is pseudo-coherent, hence
has quasi-coherent cohomology by Stacks 08E5, which is what makes the statement meaningful; the
pseudo-coherence of `RΓ(U, K)` over `A` is then the implication `(1) → (2)` of
`AlgebraicGeometry.pseudoCoherent_derivedSections_tfae`, the pseudo-coherence clause of
Stacks 0DI2.

**The Tor-dimension clause is carried, as `hTor`.** Its affine comparison is Stacks 0DHY part
(2), formalized as
`AlgebraicGeometry.AffineRelativeTorAmplitude.locallyHasFiniteTorDimension_relativeComplex_iff`,
but only in the globally affine situation; what is missing is its affine-locality assembly, the
analogue for Tor dimension of the three equivalent forms that Stacks 0DI2 has for
pseudo-coherence, whose absence is recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectDerivedSections`. The hypothesis is that
clause: it is quantified over every object of `D(𝒪_X)` and mentions neither the diagonal, nor
`ξ`, nor the dualizing condition.

**The second condition is proved, by transport along `AffineDiagonalComparison`.** The source's
proof reduces to the affine case and then matches `Δ_*𝒪_X`, `L pr₁^*` and `R SheafHom` with their
algebraic counterparts, which for the last two are Stacks 08DW part (2) and Stacks 0A6H (3)(a) —
the clause for a pseudo-coherent first argument, which is what `Δ_*𝒪_X` is, against a bounded
below second one, which is what `L pr₁^*K|_W` is. Those matchings are the fields of
`AffineDiagonalComparison`, and the condition on `ξ` is carried across them. The comparison of
derived sheaf Hom is required at *every* object, so the data cannot be met by a functor
constant at `A[0]`: at the zero object its two sides would be `A[0]` and `0`. Nothing in it
mentions `A[0]` as a value of the derived Hom, which is the isomorphism the conclusion asserts
and which comes from `ξ` alone.

**The `R`-algebra structure on `A` is the one `f` induces.** It is an instance argument, pinned
to `f.appLE V U` by the equation `_halg`, so the conclusion is about the ring map of the square
and not about some unrelated algebra structure; the equation enters no proof, only the statement,
whence the underscore. Flatness and finite presentation of that ring map, the affine-local
shadows of `Flat f` and `LocallyOfFinitePresentation f`, are instance hypotheses.

## References

* [Stacks Project, Lemma 48.28.2 (Tag 0E2U)](https://stacks.math.columbia.edu/tag/0E2U)
* [Stacks Project, Definition 48.28.1 (Tag 0E2T)](https://stacks.math.columbia.edu/tag/0E2T)
* [Stacks Project, Definition 47.27.1 (Tag 0E2C)](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Lemma 36.3.5 (Tag 06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Lemma 36.35.3 (Tag 0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
* [Stacks Project, Tag 0DHY](https://stacks.math.columbia.edu/tag/0DHY)
* [Stacks Project, Lemma 36.3.8 (Tag 08DW)](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Lemma 36.10.8 (Tag 0A6H)](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Lemma 36.10.1 (Tag 08E5)](https://stacks.math.columbia.edu/tag/08E5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite StrictlyPerfect
open scoped TensorProduct

universe d' u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} {f : X ⟶ S}

namespace DiagonalOpen

variable (D : DiagonalOpen f)

/-! The additivity of `⊗_{𝒪_W}` in each variable and the existence of the total complexes of the
tensor double complexes are proved in
`StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplex`, where they are seated as local
instances because the universes of the site `Opens W` and of the sections of `𝒪_W` coincide and
instance search would have to solve `max ?u ?v =?= u` with both unknown. They are re-seated here
for the same reason. None of them is an assumption. -/

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- **The affine comparison of the diagonal operations at a chart of `W` over `A ⊗_R A`.** For
`U` an affine open of `X` with `A = Γ(X, U)` and `R` a ring acting on `A`, this is a functor
`D(𝒪_W) ⥤ D(A)` — derived sections over the chart of `W` cut out by `U`, read over `A` through
the algebra `Δ_*𝒪_X` — together with the two identifications the source's proof uses: it takes
`Δ_*𝒪_X` to `A` in degree zero, and it takes `R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*E|_W)` to
`R Hom_{A ⊗_R A}(A, RΓ(U, E) ⊗^L_A (A ⊗_R A))` for every object `E` of `D(𝒪_X)`.

The second identification is Stacks 08DW part (2) for `L pr₁^*` followed by Stacks 0A6H (3)(a)
for derived sheaf Hom out of the pseudo-coherent `Δ_*𝒪_X`. -/
structure AffineDiagonalComparison (U : X.Opens) (R : Type u) [CommRing R]
    [Algebra R ↑Γ(X, U)] [Module.Flat R ↑Γ(X, U)] where
  /-- Derived sections over the chart of `W` over `A ⊗_R A`, read as a complex of `A`-modules. -/
  sections : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules D.W.sheaf) ⥤
    DerivedCategory (ModuleCat.{u} ↑Γ(X, U))
  /-- `Δ_*𝒪_X` is `A` placed in degree zero. -/
  diagonalIso : sections.obj D.diagonalObject ≅
    (DerivedCategory.singleFunctor (ModuleCat.{u} ↑Γ(X, U)) 0).obj
      (ModuleCat.of ↑Γ(X, U) ↑Γ(X, U))
  /-- `R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*E|_W)` is `R Hom_{A ⊗_R A}(A, RΓ(U, E) ⊗^L_A (A ⊗_R A))`,
  for every object `E` of `D(𝒪_X)`. -/
  derivedHomIso (E : DerivedCategory X.Modules) :
    sections.obj
        (((Stacks.SheafOfModules.derivedSheafHom D.W.sheaf).obj (op D.diagonalObject)).obj
          (D.derivedPullbackProj E)) ≅
      (Dualizing.derivedHom.{u, u}
        (Algebra.TensorProduct.lmul' R : ↑Γ(X, U) ⊗[R] ↑Γ(X, U) →ₐ[R] ↑Γ(X, U)).toRingHom).obj
          ((Dualizing.diagonalDerivedExtension R ↑Γ(X, U)).obj
            ((derivedSectionsUnbounded X U).obj E))

end DiagonalOpen

variable
  [HasDerivedCategory.{d'}
    (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]
  [∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    HasDerivedCategory.{d'}
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        U.isOpenEmbedding))]

/-- **Stacks 0E2U.** Let `f : X ⟶ S` be flat and locally of finite presentation and let
`(K, ξ)` be a relative dualizing complex for `f` relative to an open `W ⊆ X ×_S X` through which
the relative diagonal factors as a closed immersion. Let `U ⊆ X` be an affine open lying over an
affine open `V ⊆ S`, and put `R = Γ(S, V)` and `A = Γ(X, U)`, an `R`-algebra through `f`. Then
`RΓ(U, K)`, the object of `D(A)` corresponding to `K|_U` under Stacks 06Z0, is a relative
dualizing complex for `R → A` in the sense of Stacks 0E2C.

Two cited inputs are carried. `hTor` is the Tor-dimension clause of Stacks 0DI2, at every object
of `D(𝒪_X)`: the affine comparison of Stacks 0DHY part (2) together with the affine-locality
assembly that the Tor-dimension half of Stacks 0DI2 still lacks. `cmp` is the affine comparison
of `Δ_*𝒪_X`, `L pr₁^*` and `R SheafHom_{𝒪_W}` at a chart of `W` over `A ⊗_R A`, that is
Stacks 08DW part (2) and Stacks 0A6H (3)(a). The pseudo-coherence clause and the condition on
`ξ` are proved. The statement at the source's hypotheses, at the derived tensor product of
Stacks 06YU, is `isRelativeDualizingComplex_derivedSections` in the namespace
`AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex`. -/
@[stacks 0E2U "variant: for an arbitrary family of certified tensorings, given the \
Tor-dimension clause of Tag 0DI2 at every object and an affine diagonal comparison datum; the tag \
is AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex.\
isRelativeDualizingComplex_derivedSections"]
theorem isRelativeDualizingComplex_derivedSections [Flat f] [LocallyOfFinitePresentation f]
    (Dten : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (D : DiagonalOpen f) (K : DerivedCategory X.Modules)
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K)
    (hK : IsRelativeDualizingComplex f Dten D K ξ)
    {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V)
    [Algebra ↑Γ(S, V) ↑Γ(X, U)] [Module.Flat ↑Γ(S, V) ↑Γ(X, U)]
    [Algebra.FinitePresentation ↑Γ(S, V) ↑Γ(X, U)]
    (_halg : algebraMap ↑Γ(S, V) ↑Γ(X, U) = (f.appLE V U hUV).hom)
    (hTor : ∀ E : DerivedCategory X.Modules,
      RingedSpace.LocallyHasFiniteTorDimension
          (RingedSpace.inverseImage S.toRingedSpace f.base) Dten
          ((derivedScalarRestriction f).obj E) →
        StacksDraft.TorAmplitude.HasFiniteTorDimension
          (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct ↑Γ(S, V)).tensor
          (StacksDraft.TorAmplitude.canonicalTensorComparison ↑Γ(S, V))
          (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived ↑Γ(S, V))
          ((ModuleCat.restrictScalars (algebraMap ↑Γ(S, V) ↑Γ(X, U))).mapDerivedCategory.obj
            ((derivedSectionsUnbounded X U).obj E)))
    (cmp : D.AffineDiagonalComparison U ↑Γ(S, V)) :
    Dualizing.IsRelativeDualizingComplex ↑Γ(S, V) ↑Γ(X, U)
      ((derivedSectionsUnbounded X U).obj K) := by
  have hpc := hK.isPerfectRelativeTo.1
  have hE := isQuasicoherentDerived_of_isPseudoCoherent X K hpc
  have hiso : IsIso (D.diagonalAction K ξ) := hK.isIso_diagonalAction
  refine ⟨⟨?_, hTor K hK.isPerfectRelativeTo.2⟩, ?_⟩
  · have h12 := (pseudoCoherent_derivedSections_tfae f K hE).out 1 2
    exact h12.mp hpc U hU V hV hUV
  · exact ⟨(cmp.derivedHomIso K).symm ≪≫
      cmp.sections.mapIso (asIso (D.diagonalAction K ξ)).symm ≪≫ cmp.diagonalIso⟩

end AlgebraicGeometry.Scheme.Hom

end
