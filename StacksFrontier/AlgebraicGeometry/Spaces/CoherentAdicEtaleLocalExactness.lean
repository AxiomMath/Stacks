module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicExactnessLocal

/-!
# An étale local criterion for exactness of coherent adic systems

Let `F` be a Noetherian algebraic space over a scheme `S` and let `𝓘 ⊆ 𝒪_F` be a quasi-coherent
sheaf of ideals.  A short complex `E ⟶ G ⟶ H` in the category
`AlgebraicGeometry.Space.CoherentAdicSystems` of coherent `𝓘`-adic systems on `F` is exact exactly
when the morphism from `E` onto its cycles, the kernel of `G ⟶ H` in `Coh(F, 𝓘)`, is locally
surjective for the small étale topology of `F` at the lowest level of the systems.

The systems are indexed by `ℕᵒᵖ` from `0`: the term at `n` is `E_{n + 1}` in the numbering of
Stacks 089P, so the lowest level is `Opposite.op 0`.

## Main definitions

* `AlgebraicGeometry.Space.coherentAdicCycleLift` — the morphism from the first term of a short
  complex of coherent adic systems onto its cycles, the kernel of the second morphism.
* `AlgebraicGeometry.Space.coherentAdicLeftHomologyData` — the left homology data of a short
  complex of coherent adic systems on a Noetherian algebraic space, with cycles the kernel in
  `Coh(F, 𝓘)` and homology the cokernel of the previous morphism.

## Main results

* `AlgebraicGeometry.Space.hasHomology_shortComplex` — every short complex of coherent adic
  systems on a Noetherian algebraic space has homology.
* `AlgebraicGeometry.Space.exact_iff_epi_coherentAdicCycleLift` — a short complex of coherent
  adic systems is exact exactly when the morphism onto its cycles is surjective.
* `AlgebraicGeometry.Space.exact_iff_isLocallySurjective_coherentAdicCycleLift_app_zero` and
  `AlgebraicGeometry.Space.exact_iff_exists_covering_coherentAdicCycleLift_app_zero` — **the
  criterion**: exactness in `Coh(F, 𝓘)` is equivalent to local surjectivity, at the lowest level,
  of the morphism onto the cycles, in the two spellings of local surjectivity for the small étale
  topology — as `CategoryTheory.Presheaf.IsLocallySurjective`, and as the existence for each
  section of a covering sieve along which it lifts.

## References

* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
* [Stacks Project, Tag 08B3](https://stacks.math.columbia.edu/tag/08B3)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ F)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (T : ShortComplex (CoherentAdicSystems B S hS F hF 𝓘))

/-! ### The cycles of a short complex of coherent adic systems -/

/-- **The morphism from the first term of a short complex of coherent adic systems onto its
cycles**, the kernel of the second morphism in `Coh(F, 𝓘)`. -/
def coherentAdicCycleLift : T.X₁ ⟶ coherentAdicKernel B S hS F hF 𝓘 hZ hN hIcart T.g :=
  (coherentAdicKernelIsLimit B S hS F hF 𝓘 hZ hN hIcart T.g).lift
    (KernelFork.ofι T.f T.zero)

/-- The morphism onto the cycles lies over the first morphism of the complex. -/
theorem coherentAdicCycleLift_comp :
    coherentAdicCycleLift B S hS F hF 𝓘 hZ hN hIcart T ≫
        coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart T.g =
      T.f :=
  (coherentAdicKernelIsLimit B S hS F hF 𝓘 hZ hN hIcart T.g).fac
    (KernelFork.ofι T.f T.zero) WalkingParallelPair.zero

/-- The left homology data of a short complex of coherent adic systems on a Noetherian algebraic
space: the cycles are the kernel of the second morphism in `Coh(F, 𝓘)`, and the homology is the
cokernel of the morphism onto the cycles. -/
def coherentAdicLeftHomologyData : T.LeftHomologyData where
  K := coherentAdicKernel B S hS F hF 𝓘 hZ hN hIcart T.g
  H := cokernel (coherentAdicCycleLift B S hS F hF 𝓘 hZ hN hIcart T)
  i := coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart T.g
  π := cokernel.π _
  wi := coherentAdicKernelι_comp B S hS F hF 𝓘 hZ hN hIcart T.g
  hi := coherentAdicKernelIsLimit B S hS F hF 𝓘 hZ hN hIcart T.g
  wπ := cokernel.condition _
  hπ := cokernelIsCokernel _

/-- The morphism onto the cycles of that left homology data is
`AlgebraicGeometry.Space.coherentAdicCycleLift`. -/
theorem coherentAdicLeftHomologyData_f' :
    (coherentAdicLeftHomologyData B S hS F hF 𝓘 hZ hN hIcart T).f' =
      coherentAdicCycleLift B S hS F hF 𝓘 hZ hN hIcart T :=
  rfl

include hZ hN hIcart in
/-- **Every short complex of coherent adic systems on a Noetherian algebraic space has
homology.** -/
theorem hasHomology_shortComplex : T.HasHomology :=
  let := abelian_coherentAdicSystems B S hS F hF 𝓘 hZ hN hIcart
  inferInstance

/-! ### Exactness is surjectivity onto the cycles -/

/-- **A short complex of coherent adic systems on a Noetherian algebraic space is exact exactly
when the morphism onto its cycles is surjective.** -/
theorem exact_iff_epi_coherentAdicCycleLift :
    T.Exact ↔ Epi (coherentAdicCycleLift B S hS F hF 𝓘 hZ hN hIcart T) :=
  have := hasHomology_shortComplex B S hS F hF 𝓘 hZ hN hIcart T
  (coherentAdicLeftHomologyData B S hS F hF 𝓘 hZ hN hIcart T).exact_iff_epi_f'

/-! ### The étale local criterion -/

/-- **Exactness in `Coh(F, 𝓘)` is local surjectivity onto the cycles.**  A short complex of
coherent adic systems on a Noetherian algebraic space is exact exactly when the component at the
lowest level of the morphism onto its cycles is locally surjective for the small étale topology
of `F`. -/
theorem exact_iff_isLocallySurjective_coherentAdicCycleLift_app_zero :
    T.Exact ↔ Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F)
      ((PresheafOfModules.toPresheaf _).map
        ((coherentAdicCycleLift B S hS F hF 𝓘 hZ hN hIcart T).hom.app (op 0)).val) :=
  (exact_iff_epi_coherentAdicCycleLift B S hS F hF 𝓘 hZ hN hIcart T).trans
    (epi_iff_isLocallySurjective_app_zero B S hS F hF 𝓘 _)

/-- **The criterion spelled out on coverings.**  A short complex of coherent adic systems on a
Noetherian algebraic space is exact exactly when, at the lowest level, every section of its
cycles over an étale chart of `F` is the image of a section of its first term after restriction
along the arrows of some étale covering of that chart. -/
theorem exact_iff_exists_covering_coherentAdicCycleLift_app_zero :
    T.Exact ↔ ∀ (U : SmallEtale B S hS F)
      (s : ((coherentAdicKernel B S hS F hF 𝓘 hZ hN hIcart T.g).obj.obj (op 0)).val.obj (op U)),
      ∃ C : Sieve U, C ∈ SmallEtale.topology B S hS F U ∧
        ∀ ⦃V : SmallEtale B S hS F⦄ (g : V ⟶ U), C g →
          ∃ t : (T.X₁.obj.obj (op 0)).val.obj (op V),
            ((coherentAdicCycleLift B S hS F hF 𝓘 hZ hN hIcart T).hom.app (op 0)).val.app
                (op V) t =
              ((coherentAdicKernel B S hS F hF 𝓘 hZ hN hIcart T.g).obj.obj (op 0)).val.map
                g.op s :=
  (exact_iff_epi_coherentAdicCycleLift B S hS F hF 𝓘 hZ hN hIcart T).trans
    (epi_iff_exists_covering_app_zero B S hS F hF 𝓘 _)

end AlgebraicGeometry.Space

end
