module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicNormalMono

/-!
# Exactness of coherent adic systems on an algebraic space is étale local at the lowest level

Let `F` be an algebraic space over a scheme `S` and let `𝓘 ⊆ 𝒪_F` be a sheaf of ideals on its
small étale ringed site.  This file reduces exactness in the category `Coh(F, 𝓘)` of coherent
adic systems of `AlgebraicGeometry.Space.CoherentAdicSystems` to a condition on an étale
covering, at the single lowest level of the systems.

The reduction has two steps.  Exactness of a short complex is the vanishing of the homology
object of any of its left homology data, equivalently the surjectivity of the induced morphism
from the first term onto the cycles.  That is a surjectivity statement in `Coh(F, 𝓘)`, so
`AlgebraicGeometry.Space.epi_iff_epi_app_zero` — Stacks 08B3 — turns it into surjectivity of a
single morphism of `𝒪_F`-modules, the component at the lowest level.  Surjectivity of a morphism
of `𝒪_F`-modules is in turn local surjectivity for the small étale topology
(`Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective`): every section of the target over
an étale chart is, after restriction along the arrows of some étale covering of that chart, in
the image.

## Main definitions

* `AlgebraicGeometry.Space.leftHomologyDataOfIsCoherentAdicSystemKernel` — the left homology data
  of a short complex of coherent adic systems whose levelwise kernel is a coherent adic system,
  with cycles that levelwise kernel.

## Main results

* `AlgebraicGeometry.Space.hom_eq_zero_iff_sections_eq_zero` and
  `AlgebraicGeometry.Space.comp_eq_zero_iff_sections_eq_zero` — **vanishing of a morphism, and of
  a composite of two morphisms, of coherent adic systems is a chartwise condition**: it is
  checked on the sections over the étale charts of `F`, level by level.
* `AlgebraicGeometry.Space.epi_iff_isLocallySurjective_app_zero` and
  `AlgebraicGeometry.Space.epi_iff_exists_covering_app_zero` — **surjectivity in `Coh(F, 𝓘)` is
  étale local**: a morphism of coherent adic systems is surjective exactly when, at the lowest
  level, every section of the target over an étale chart lifts after passing to an étale
  covering.
* `AlgebraicGeometry.Space.exact_iff_epi_f'_app_zero` — **exactness in `Coh(F, 𝓘)` is a condition
  at the lowest level**: a short complex of coherent adic systems which has homology is exact
  exactly when the component at the lowest level of the morphism onto its cycles is surjective.
* `AlgebraicGeometry.Space.exact_iff_isLocallySurjective_f'_app_zero` and
  `AlgebraicGeometry.Space.exact_iff_exists_covering_f'_app_zero` — **and that condition is
  étale local**, which is the criterion this file is for.
* `AlgebraicGeometry.Space.isLocallySurjective_f'_app_zero_of_exact` — the implication from
  exactness to the étale local condition, which needs no hypothesis beyond exactness itself.
* `AlgebraicGeometry.Space.exact_iff_isLocallySurjective_app_zero_of_g_eq_zero` and
  `AlgebraicGeometry.Space.exact_iff_exists_covering_app_zero_of_g_eq_zero` — **at the right end
  the criterion is unconditional**: a short complex of coherent adic systems whose second
  morphism vanishes is exact exactly when the first is locally surjective at the lowest level.
* `AlgebraicGeometry.Space.exact_of_f_eq_zero_of_mono_app` — at the left end only the sufficiency
  of a levelwise condition is available.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed, as in
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystem`: the term at `n` is the Stacks source's
`E_{n + 1}`, so the "lowest level" below is `Opposite.op 0`.

### Where the tag for Stacks 089P sits, and what the hypotheses are

Part (2) of Stacks 089P asserts that exactness in `Coh(X, 𝓘)` may be checked étale locally, for
`X` a Noetherian algebraic space, meaning that a short complex whose restriction to each member
of an étale covering is exact is itself exact.  **That part is not proved here**: it is
`AlgebraicGeometry.Space.exact_iff_forall_exact_coherentAdicRestrictToChart` of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicEtaleExactnessReflection`, and carries the tag
in the form
`AlgebraicGeometry.Space.exact_iff_forall_exact_coherentAdicChartRestriction` of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicInverseImageIdeal`.  What is proved here is the
criteria below; with the Noetherian data supplied they become
`AlgebraicGeometry.Space.exact_iff_isLocallySurjective_coherentAdicCycleLift_app_zero` and
`AlgebraicGeometry.Space.exact_iff_exists_covering_coherentAdicCycleLift_app_zero` of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicEtaleLocalExactness`: a different test, local
surjectivity of the morphism onto the kernel taken in `Coh(X, 𝓘)`, which is étale local but is
not the reflection statement.  Part (1) of 089P, that `Coh(X, 𝓘)` is abelian, is
`AlgebraicGeometry.Space.abelian_coherentAdicSystems`.

The criteria below are stated with the short complex *having homology*, and with a left homology
datum, as hypotheses.  Neither is a gap: on a Noetherian algebraic space with `𝓘` quasi-coherent
`Coh(F, 𝓘)` is abelian, by
`AlgebraicGeometry.Space.abelian_coherentAdicSystems` in
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicAbelian`, and in a
`CategoryTheory.Abelian` category `CategoryTheory.ShortComplex.HasHomology` is automatic and the
kernel of the second morphism provides the datum.  They are kept as hypotheses here so that the
criteria themselves carry no Noetherian data; discharging them is what the file named above does.
The same remark applies to
`AlgebraicGeometry.Space.leftHomologyDataOfIsCoherentAdicSystemKernel`, which was the only source
of a homology datum before the kernel of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicKernelObject` existed.

The hypothesis is absent at the right end, where exactness of `E ⟶ G ⟶ 0` is surjectivity of the
first morphism and no kernel is involved.  At the left end exactness of `0 ⟶ G ⟶ H` is
injectivity of the second morphism, and a monomorphism of `Coh(F, 𝓘)` is still not known to be
injective level by level — the abelian structure does not make it so, and the implementation
notes of `StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicNormalMono` say why — so only the
implication from a levelwise condition is available there.

The local condition is not the restriction of the complex to an étale chart.  The restriction
functor is `AlgebraicGeometry.Space.restrictToChartSchemeFunctor`, and nothing here says it is
exact or that it reflects exactness jointly over a covering family; the reflection, at the level
of `Coh` and over affine charts, is the business of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicEtaleExactnessReflection` and not of this file.
What replaces it is local surjectivity of one morphism of `𝒪_F`-modules, which is the content of
surjectivity on the small étale site and needs no comparison of sites at all: the objects of the
small étale site of `F` *are* its étale charts, so a condition quantified over them and over
covering sieves of them is already an étale local condition.  Only the lowest level of the
systems is tested.  But this is a different statement from the source's, not a reformulation of
it: the test is local surjectivity of a morphism onto the cycles rather than exactness of a
restricted complex, and neither is known here to imply the other.

Vanishing of a morphism, by contrast, is chartwise with no hypothesis whatever: the objects of the
small étale site *are* the charts, so a morphism of `𝒪_F`-modules is zero as soon as it kills
every section over every chart.  This is what the scheme-level
`Stacks.Coherent.hom_eq_zero_of_restrictFunctor_map_eq_zero_system` has to prove from an open
covering.

## References

* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
* [Stacks Project, Tag 08B3](https://stacks.math.columbia.edu/tag/08B3)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-! ### Vanishing of a morphism is chartwise -/

/-- A morphism of `𝒪_F`-modules vanishes exactly when it kills every section over every étale
chart: the charts are the objects of the small étale site. -/
theorem modules_hom_eq_zero_iff_sections_eq_zero {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N) :
    φ = 0 ↔ ∀ (U : SmallEtale B S hS F) (x : M.val.obj (op U)), φ.val.app (op U) x = 0 := by
  refine ⟨fun h U x => h ▸ rfl, fun h => ?_⟩
  ext X x
  obtain ⟨U⟩ := X
  exact h U x

/-- A morphism of coherent adic systems vanishes exactly when it vanishes at every level:
morphisms of a full subcategory are morphisms of the ambient category, and a morphism of inverse
systems is determined by its components. -/
theorem hom_eq_zero_iff_app_eq_zero {E E' : CoherentAdicSystems B S hS F hF 𝓘} (f : E ⟶ E') :
    f = 0 ↔ ∀ n : ℕᵒᵖ, f.hom.app n = 0 :=
  ⟨fun h _ => h ▸ rfl, fun h =>
    ObjectProperty.hom_ext (IsCoherentAdicSystem B S hS F hF 𝓘) (NatTrans.ext (funext h))⟩

/-- **Vanishing of a morphism of coherent adic systems is a chartwise condition.**  It vanishes
exactly when, at every level, it kills every section of the source over every étale chart of
`F`. -/
theorem hom_eq_zero_iff_sections_eq_zero {E E' : CoherentAdicSystems B S hS F hF 𝓘} (f : E ⟶ E') :
    f = 0 ↔ ∀ (n : ℕᵒᵖ) (U : SmallEtale B S hS F) (x : (E.obj.obj n).val.obj (op U)),
      (f.hom.app n).val.app (op U) x = 0 := by
  rw [hom_eq_zero_iff_app_eq_zero]
  exact forall_congr' fun n => modules_hom_eq_zero_iff_sections_eq_zero B S hS F hF (f.hom.app n)

/-- **Vanishing of a composite of two morphisms of coherent adic systems is a chartwise
condition**, this being the half of an exactness statement which asserts that the pair is a
complex. -/
theorem comp_eq_zero_iff_sections_eq_zero {E G H : CoherentAdicSystems B S hS F hF 𝓘}
    (α : E ⟶ G) (β : G ⟶ H) :
    α ≫ β = 0 ↔ ∀ (n : ℕᵒᵖ) (U : SmallEtale B S hS F) (x : (E.obj.obj n).val.obj (op U)),
      (β.hom.app n).val.app (op U) ((α.hom.app n).val.app (op U) x) = 0 :=
  hom_eq_zero_iff_sections_eq_zero B S hS F hF 𝓘 (α ≫ β)

/-! ### Surjectivity in `Coh(F, 𝓘)` is étale local -/

/-- **Surjectivity in `Coh(F, 𝓘)` is étale local.**  A morphism of coherent adic systems is
surjective exactly when its component at the lowest level is locally surjective for the small
étale topology.

Stacks 08B3 reduces surjectivity to the lowest level, and surjectivity of a morphism of sheaves of
modules is local surjectivity. -/
theorem epi_iff_isLocallySurjective_app_zero {E E' : CoherentAdicSystems B S hS F hF 𝓘}
    (f : E ⟶ E') :
    Epi f ↔ Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F)
      ((PresheafOfModules.toPresheaf _).map (f.hom.app (op 0)).val) :=
  (epi_iff_epi_app_zero B S hS F hF 𝓘 f).trans
    (Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective (f.hom.app (op 0)))

/-- A morphism of `𝒪_F`-modules is surjective exactly when every section of its target over an
étale chart lifts along the arrows of some étale covering of that chart. -/
theorem modules_epi_iff_exists_covering {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N) :
    Epi φ ↔ ∀ (U : SmallEtale B S hS F) (s : N.val.obj (op U)),
      ∃ T : Sieve U, T ∈ SmallEtale.topology B S hS F U ∧
        ∀ ⦃V : SmallEtale B S hS F⦄ (g : V ⟶ U), T g →
          ∃ t : M.val.obj (op V), φ.val.app (op V) t = N.val.map g.op s := by
  refine ⟨fun _ U s => Stacks.SheafOfModules.EpiMono.exists_covering_of_epi φ s, fun h =>
    Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective φ ⟨fun {U} s => ?_⟩⟩
  obtain ⟨T, hT, hlift⟩ := h U s
  exact (SmallEtale.topology B S hS F).superset_covering (fun _ g hg => hlift g hg) hT

/-- **Surjectivity in `Coh(F, 𝓘)` is checked on étale coverings at the lowest level.**  A morphism
of coherent adic systems is surjective exactly when every section of the target over an étale
chart, at the lowest level, lifts along the arrows of some étale covering of that chart. -/
theorem epi_iff_exists_covering_app_zero {E E' : CoherentAdicSystems B S hS F hF 𝓘} (f : E ⟶ E') :
    Epi f ↔ ∀ (U : SmallEtale B S hS F) (s : (E'.obj.obj (op 0)).val.obj (op U)),
      ∃ T : Sieve U, T ∈ SmallEtale.topology B S hS F U ∧
        ∀ ⦃V : SmallEtale B S hS F⦄ (g : V ⟶ U), T g →
          ∃ t : (E.obj.obj (op 0)).val.obj (op V),
            (f.hom.app (op 0)).val.app (op V) t = (E'.obj.obj (op 0)).val.map g.op s := by
  rw [epi_iff_epi_app_zero B S hS F hF 𝓘 f,
    modules_epi_iff_exists_covering B S hS F hF (f.hom.app (op 0))]

/-! ### Exactness in `Coh(F, 𝓘)` -/

section Exactness

variable {T : ShortComplex (CoherentAdicSystems B S hS F hF 𝓘)}

/-- The left homology data of a short complex of coherent adic systems whose levelwise kernel is
a coherent adic system: the cycles are that levelwise kernel, which is the kernel in `Coh(F, 𝓘)`
by `AlgebraicGeometry.Space.hasKernel_of_isCoherentAdicSystem_kernel`, and the homology is the
cokernel of the induced morphism, which exists because `Coh(F, 𝓘)` has all cokernels. -/
def leftHomologyDataOfIsCoherentAdicSystemKernel
    (hker : IsCoherentAdicSystem B S hS F hF 𝓘 (kernel T.g.hom)) : T.LeftHomologyData :=
  haveI := hasKernel_of_isCoherentAdicSystem_kernel B S hS F hF 𝓘 T.g hker
  ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel T

/-- **Exactness in `Coh(F, 𝓘)` is a condition at the lowest level.**  A short complex of coherent
adic systems which has homology is exact exactly when the component at the lowest level of the
induced morphism from its first term onto its cycles is surjective.

Exactness is the surjectivity of that induced morphism, and Stacks 08B3 reads a surjection in
`Coh(F, 𝓘)` off its lowest level. -/
theorem exact_iff_epi_f'_app_zero [T.HasHomology] (h : T.LeftHomologyData) :
    T.Exact ↔ Epi (h.f'.hom.app (op 0)) := by
  rw [h.exact_iff_epi_f', epi_iff_epi_app_zero B S hS F hF 𝓘 h.f']

/-- **Exactness in `Coh(F, 𝓘)` implies an étale local condition at the lowest level**: the
component at the lowest level of the induced morphism onto the cycles is locally surjective for
the small étale topology.

This direction assumes nothing beyond exactness itself. -/
theorem isLocallySurjective_f'_app_zero_of_exact (hT : T.Exact) (h : T.LeftHomologyData) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F)
      ((PresheafOfModules.toPresheaf _).map (h.f'.hom.app (op 0)).val) :=
  (epi_iff_isLocallySurjective_app_zero B S hS F hF 𝓘 h.f').mp (hT.epi_f' h)

/-- **Exactness in `Coh(F, 𝓘)` is étale local at the lowest level.**  A short complex of coherent
adic systems which has homology is exact exactly when the component at the lowest level of the
induced morphism onto its cycles is locally surjective for the small étale topology. -/
theorem exact_iff_isLocallySurjective_f'_app_zero [T.HasHomology] (h : T.LeftHomologyData) :
    T.Exact ↔ Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F)
      ((PresheafOfModules.toPresheaf _).map (h.f'.hom.app (op 0)).val) :=
  (h.exact_iff_epi_f').trans (epi_iff_isLocallySurjective_app_zero B S hS F hF 𝓘 h.f')

/-- **Exactness in `Coh(F, 𝓘)` is checked on étale coverings at the lowest level.**  A short
complex of coherent adic systems which has homology is exact exactly when, at the lowest level,
every section of its cycles over an étale chart is the image of a section of its first term after
restriction along the arrows of some étale covering of that chart. -/
theorem exact_iff_exists_covering_f'_app_zero [T.HasHomology] (h : T.LeftHomologyData) :
    T.Exact ↔ ∀ (U : SmallEtale B S hS F) (s : (h.K.obj.obj (op 0)).val.obj (op U)),
      ∃ C : Sieve U, C ∈ SmallEtale.topology B S hS F U ∧
        ∀ ⦃V : SmallEtale B S hS F⦄ (g : V ⟶ U), C g →
          ∃ t : (T.X₁.obj.obj (op 0)).val.obj (op V),
            (h.f'.hom.app (op 0)).val.app (op V) t = (h.K.obj.obj (op 0)).val.map g.op s :=
  (h.exact_iff_epi_f').trans (epi_iff_exists_covering_app_zero B S hS F hF 𝓘 h.f')

/-! ### Exactness at the two ends -/

/-- **Exactness of a short complex of coherent adic systems whose second morphism vanishes is
étale local at the lowest level, with no hypothesis at all.**  Such a complex is exact exactly
when the component at the lowest level of its first morphism is locally surjective for the small
étale topology.

Exactness of a complex `E ⟶ G ⟶ 0` is surjectivity of its first morphism, which Stacks 08B3 reads
off the lowest level; no kernel in `Coh(F, 𝓘)` is needed, which is why this case is
unconditional. -/
theorem exact_iff_isLocallySurjective_app_zero_of_g_eq_zero (hg : T.g = 0) :
    T.Exact ↔ Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F)
      ((PresheafOfModules.toPresheaf _).map (T.f.hom.app (op 0)).val) :=
  (T.exact_iff_epi hg).trans (epi_iff_isLocallySurjective_app_zero B S hS F hF 𝓘 T.f)

/-- **Exactness of a short complex of coherent adic systems whose second morphism vanishes is
checked on étale coverings at the lowest level**, with no hypothesis at all: at the lowest level
every section of the middle term over an étale chart is the image of a section of the first term
after restriction along the arrows of some étale covering of that chart. -/
theorem exact_iff_exists_covering_app_zero_of_g_eq_zero (hg : T.g = 0) :
    T.Exact ↔ ∀ (U : SmallEtale B S hS F) (s : (T.X₂.obj.obj (op 0)).val.obj (op U)),
      ∃ C : Sieve U, C ∈ SmallEtale.topology B S hS F U ∧
        ∀ ⦃V : SmallEtale B S hS F⦄ (g : V ⟶ U), C g →
          ∃ t : (T.X₁.obj.obj (op 0)).val.obj (op V),
            (T.f.hom.app (op 0)).val.app (op V) t = (T.X₂.obj.obj (op 0)).val.map g.op s :=
  (T.exact_iff_epi hg).trans (epi_iff_exists_covering_app_zero B S hS F hF 𝓘 T.f)

/-- A short complex of coherent adic systems whose first morphism vanishes and whose second
morphism is injective at every level is exact.

Only this implication is available at the left end.  Exactness of a complex `0 ⟶ G ⟶ H` is
injectivity of its second morphism in `Coh(F, 𝓘)`, and a monomorphism of a full subcategory is
tested only against the objects of the subcategory, so it is not known to be injective level by
level; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicNormalMono`. -/
theorem exact_of_f_eq_zero_of_mono_app (hf : T.f = 0)
    (hg : ∀ n : ℕᵒᵖ, Mono (T.g.hom.app n)) : T.Exact :=
  (T.exact_iff_mono hf).mpr (mono_of_mono_app B S hS F hF 𝓘 T.g hg)

end Exactness

end AlgebraicGeometry.Space

end
