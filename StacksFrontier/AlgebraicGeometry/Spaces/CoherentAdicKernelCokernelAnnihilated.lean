module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Annihilator
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AnnihilatedAffineCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicChartTower
public import StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleSectionsInjective

/-!
# Maps of coherent adic systems whose kernel and cokernel are annihilated by a power of an ideal

Let `X` be a Noetherian algebraic space over a scheme `S`, let `𝓘, 𝓚 ⊆ 𝒪_X` be quasi-coherent
sheaves of ideals and let `α : (F_n) ⟶ (G_n)` be a morphism of `Coh(X, 𝓘)`. Stacks 08BA asserts
the equivalence of two conditions:

1. there is an integer `t ≥ 1` such that `Ker(α_n)` and `Coker(α_n)` are annihilated by `𝓚 ^ t`
   for all `n`;
2. for any (or some) surjective étale morphism `U = Spec(A) ⟶ X`, with `I, K ⊆ A` the ideals of
   `𝓘|_U, 𝓚|_U` and `α_U : M ⟶ N` the map of finite `A^∧`-modules attached to `α|_U` by Stacks
   087W, the modules `Ker(α_U)` and `Coker(α_U)` are annihilated by `K ^ t` for some `t ≥ 1`;

and names a morphism satisfying them a *map whose kernel and cokernel are annihilated by a power
of `𝓚`*. This file defines that notion and proves the equivalence, for any and for some chart.

## Main definitions

* `AlgebraicGeometry.Space.IsKernelCokernelAnnihilatedByPower` — condition (1), the notion the
  remark names.
* `AlgebraicGeometry.Space.chartCompletedSectionsMap` — the map `α_U : M ⟶ N` of Stacks 087W over
  an étale chart `U`.
* `AlgebraicGeometry.Space.IsChartKernelCokernelAnnihilated` — condition (2) at one chart.

## Main results

* `AlgebraicGeometry.Space.forall_smul_kernel_eq_zero_iff` and
  `AlgebraicGeometry.Space.forall_smul_cokernel_eq_zero_iff` — the sections of `Ker(f)` over a
  chart, and of `Coker(f)` over an affine chart, for a map `f` of coherent modules, are the kernel
  and the cokernel of the map on sections, as far as annihilation is concerned.
* `AlgebraicGeometry.Space.idealPowerMultiple_eq_bot_iff_of_surjective_affine_chart` — annihilation
  of a quasi-coherent module by `𝓚 ^ t` may be tested on one surjective affine chart.
* `AlgebraicGeometry.Space.isKernelCokernelAnnihilatedByPower_iff_chartSections` — condition (1)
  is the uniform annihilation of the kernels and cokernels of the maps of sections `α_n(U)` over
  one surjective affine chart.
* `AlgebraicGeometry.Space.exists_chartSections_iff_isChartKernelCokernelAnnihilated` — over a
  Noetherian affine chart, that uniform annihilation is condition (2) at `U`.
* `AlgebraicGeometry.Space.isKernelCokernelAnnihilatedByPower_tfae` — **Stacks 08BA**: (1), (2)
  for every surjective affine étale chart, and (2) for some such chart, are equivalent.

## Implementation notes

The source refers the equivalence to the scheme case, Stacks 0888, which is
`Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_tfae`. The proof here runs the same
argument directly on the chart. Its commutative algebra is
`Ideal.exists_pow_le_annihilator_ker_and_coker_mapQ_pow_iff`: for a map `φ : M ⟶ N` of `I`-adically
complete modules, one power of `K` kills the kernels and cokernels of all the reductions
`M / I ⁿ⁺¹ M ⟶ N / I ⁿ⁺¹ N` exactly when one power of `K` kills `Ker(φ)` and `Coker(φ)`. It is
applied to `φ : lim_n F_n(U) ⟶ lim_n G_n(U)`, whose reduction modulo `I ⁿ⁺¹` is `α_n(U)` because
over a Noetherian affine chart the projection `lim_n F_n(U) ⟶ F_n(U)` is surjective with kernel
`I ⁿ⁺¹` times the limit (`AlgebraicGeometry.Space.surjective_chartSectionsLevel`,
`AlgebraicGeometry.Space.ker_chartSectionsLevel`). That identification is the content of Stacks
087W over `U` which the remark uses: `M` is the module whose reductions are the `F_n(U)`.

Two further steps make the condition on sections over `U` into condition (1). Over an affine chart
the sections of `Coker(α_n)` are the cokernel of `α_n(U)`, the image of `α_n` being coherent and so
cartesian on affine charts, and an epimorphism with cartesian source and kernel being surjective
on the sections over an affine chart
(`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_cartesian`).
And annihilation of the quasi-coherent modules `Ker(α_n)`, `Coker(α_n)` by `𝓚 ^ t` holds on every
chart as soon as it holds on the surjective affine chart `U`, by the globalisation step of Stacks
07UK. Neither step needs the Noetherian hypothesis; it enters only to make `𝒪_X(U)` a Noetherian
ring.

The module `M` is taken as the `I`-adic completion of `lim_n F_n(U)` rather than the limit itself:
the limit is `I`-adically complete, so the two are isomorphic as `A`-modules, but only the
completion carries the action of `A^∧` over which it is finite
(`AlgebraicGeometry.Space.moduleFinite_chartCompletedSections`), as in the source. Annihilation by
`K ^ t`, an ideal of `A`, is stated for the `A`-modules underlying `Ker(α_U)` and `Coker(α_U)`.

The systems are indexed from `0`, the term at `n` being the source's term at `n + 1`.

## References

* [Stacks Project, Tag 08BA](https://stacks.math.columbia.edu/tag/08BA)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 07UK](https://stacks.math.columbia.edu/tag/07UK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Sections of a kernel and of a cokernel over a chart -/

/-- An element of the ring of a chart kills every section of `Ker(f)` exactly when it kills every
section of the source sent to zero by `f`. -/
theorem forall_smul_kernel_eq_zero_iff {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N)
    (U : SmallEtale B S hS F) (r : chartRing B S hS F hF U) :
    (∀ z : (kernel f).val.obj (op U), r • z = 0) ↔
      ∀ x : M.val.obj (op U), f.val.app (op U) x = 0 → r • x = 0 := by
  have hex := SheafOfModules.exact_kernel_ι_val_app f (op U)
  constructor
  · intro h x hx
    obtain ⟨z, rfl⟩ := (hex x).1 hx
    rw [← map_smul, h z, map_zero]
  · intro h z
    apply injective_val_app_of_mono B S hS (kernel.ι f) (op U)
    have hs : (kernel.ι f).val.app (op U) (r • z) = r • (kernel.ι f).val.app (op U) z :=
      map_smul _ r z
    exact hs.trans ((h _ ((hex _).2 ⟨z, rfl⟩)).trans (map_zero _).symm)

/-- Over an affine chart, the sections of the cokernel of a map of coherent modules are the
cokernel of the map on sections, so an element of the ring of the chart kills every section of
`Coker(f)` exactly when it carries every section of the target into the image of `f`. -/
theorem forall_smul_cokernel_eq_zero_iff {M N : Modules.{u, u} B S hS F hF}
    (hM : IsCoherent B S hS F hF M) (hN : IsCoherent B S hS F hF N) (f : M ⟶ N)
    {U : SmallEtale B S hS F} (hU : IsAffine (chartScheme U)) (r : chartRing B S hS F hF U) :
    (∀ z : (cokernel f).val.obj (op U), r • z = 0) ↔
      ∀ y : N.val.obj (op U), ∃ x : M.val.obj (op U), f.val.app (op U) x = r • y := by
  have hMc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF M
    hM.toIsQuasicoherentOnSite
  have hNc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF N
    hN.toIsQuasicoherentOnSite
  have hCc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF (cokernel f)
    (isCoherent_cokernel B S hS F hF hM hN f).toIsQuasicoherentOnSite
  have hπ : Function.Surjective ((cokernel.π f).val.app (op U)) :=
    surjective_val_app_of_epi_of_cartesian (cokernel.π f) hNc
      (isCartesianOnAffineCharts_kernel _ hNc hCc) U hU
  have hfπ : ∀ x : M.val.obj (op U),
      (cokernel.π f).val.app (op U) (f.val.app (op U) x) = 0 :=
    fun x => congrArg (fun g : M ⟶ cokernel f => g.val.app (op U) x) (cokernel.condition f)
  have hex : ∀ y : N.val.obj (op U), (cokernel.π f).val.app (op U) y = 0 →
      ∃ x : M.val.obj (op U), f.val.app (op U) x = y := by
    intro y hy
    obtain ⟨w, rfl⟩ := (SheafOfModules.exact_kernel_ι_val_app (cokernel.π f) (op U) y).1 hy
    obtain ⟨x, rfl⟩ := surjective_val_app_of_epi_of_cartesian (Abelian.factorThruImage f) hMc
      (isCartesianOnAffineCharts_kernel_factorThruImage f hMc hNc) U hU w
    exact ⟨x, (congrArg (fun g : M ⟶ N => g.val.app (op U) x) (Abelian.image.fac f)).symm⟩
  have hs : ∀ y : N.val.obj (op U),
      (cokernel.π f).val.app (op U) (r • y) = r • (cokernel.π f).val.app (op U) y :=
    fun y => map_smul _ r y
  refine ⟨fun h y => hex _ ((hs y).trans (h _)), fun h z => ?_⟩
  obtain ⟨y, rfl⟩ := hπ z
  obtain ⟨x, hx⟩ := h y
  exact (hs y).symm.trans (hx ▸ hfπ x)

/-! ### Annihilation by a power of a sheaf of ideals, tested on one surjective affine chart -/

/-- **A quasi-coherent module is annihilated by `𝓚 ^ t` as soon as its sections over one
surjective affine étale chart `U` are annihilated by `𝓚(U) ^ t`.** The converse is immediate. The
nontrivial direction is the globalisation step of Stacks 07UK,
`AlgebraicGeometry.Space.sectionIdeal_pow_smul_top_eq_bot_of_presheafSurjective_affine_chart`. -/
theorem idealPowerMultiple_eq_bot_iff_of_surjective_affine_chart
    (𝓚 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (h𝓚 : 𝓚.toSheafOfModules.IsQuasicoherentOnSite)
    (Q : Modules.{u, u} B S hS F hF) (hQ : Q.IsQuasicoherentOnSite)
    {U : SmallEtale B S hS F} (hU : IsAffine (chartScheme U))
    (hUsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf U.1.hom) (t : ℕ) :
    idealPowerMultiple B S hS F hF 𝓚 t Q = ⊥ ↔
      ∀ r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓚 U ^ t, ∀ z : Q.val.obj (op U), r • z = 0 := by
  rw [idealPowerMultiple_eq_bot_iff]
  refine ⟨fun h r hr z => h U r hr z, fun h W r hr z => ?_⟩
  have hall := sectionIdeal_pow_smul_top_eq_bot_of_presheafSurjective_affine_chart B S hS F hF
    Q hQ 𝓚 h𝓚 U hU hUsurj t
    (le_bot_iff.1 (Submodule.smul_le.2 fun r hr z _ => (Submodule.mem_bot _).2 (h r hr z))) W
  have hmem : r • z ∈ chartSectionIdeal B S hS F hF 𝓚 W ^ t •
      (⊤ : Submodule (chartRing B S hS F hF W) (Q.val.obj (op W))) :=
    Submodule.smul_mem_smul hr Submodule.mem_top
  rwa [hall, Submodule.mem_bot] at hmem

/-! ### Condition (1) -/

/-- **Stacks 08BA, the notion.** A map `α : (F_n) ⟶ (G_n)` of inverse systems of `𝒪_X`-modules
on an algebraic space is a *map whose kernel and cokernel are annihilated by a power of `𝓚`* if
one integer `t ≥ 1` works for every level: `𝓚 ^ t` annihilates `Ker(α_n)` and `Coker(α_n)` for
all `n`. This is condition (1) of the remark; its equivalence with condition (2), which is what
makes the notion the one the remark names, is
`AlgebraicGeometry.Space.isKernelCokernelAnnihilatedByPower_tfae`.

The systems are indexed from `0`, the term at `n` being the source's term at `n + 1`; the
condition quantifies over every level, so this is the source's condition for all `n ≥ 1`. -/
@[stacks 08BA "the notion named by the remark: condition (1), one power of K annihilating every \
levelwise kernel and cokernel"]
def IsKernelCokernelAnnihilatedByPower
    (𝓚 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    {E E' : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (α : E ⟶ E') : Prop :=
  ∃ t : ℕ, 0 < t ∧ ∀ n : ℕ,
    idealPowerMultiple B S hS F hF 𝓚 t (kernel (α.app (op n))) = ⊥ ∧
      idealPowerMultiple B S hS F hF 𝓚 t (cokernel (α.app (op n))) = ⊥

variable (𝓘 𝓚 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- **Condition (1) is read on the sections over one surjective affine chart.** For a morphism of
coherent adic systems and a surjective étale chart `U` with affine underlying scheme, condition
(1) holds exactly when one integer `t ≥ 1` makes `K ^ t = 𝓚(U) ^ t` kill the kernel and the
cokernel of every map of sections `α_n(U) : F_n(U) ⟶ G_n(U)`. -/
theorem isKernelCokernelAnnihilatedByPower_iff_chartSections
    (h𝓚 : 𝓚.toSheafOfModules.IsQuasicoherentOnSite)
    {E E' : CoherentAdicSystems B S hS F hF 𝓘} (α : E ⟶ E')
    {U : SmallEtale B S hS F} (hU : IsAffine (chartScheme U))
    (hUsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf U.1.hom) :
    IsKernelCokernelAnnihilatedByPower B S hS F hF 𝓚 α.hom ↔
      ∃ t : ℕ, 0 < t ∧ ∀ n : ℕ,
        (∀ r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓚 U ^ t, ∀ x : (E.obj.obj (op n)).val.obj (op U),
            (α.hom.app (op n)).val.app (op U) x = 0 → r • x = 0) ∧
          ∀ r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓚 U ^ t, ∀ y : (E'.obj.obj (op n)).val.obj (op U),
            ∃ x : (E.obj.obj (op n)).val.obj (op U),
              (α.hom.app (op n)).val.app (op U) x = r • y := by
  refine exists_congr fun t => and_congr_right fun _ => forall_congr' fun n => and_congr ?_ ?_
  · rw [idealPowerMultiple_eq_bot_iff_of_surjective_affine_chart B S hS F hF 𝓚 h𝓚 _
      (isCoherent_kernel B S hS F hF (E.property.1 n) (E'.property.1 n)
        _).toIsQuasicoherentOnSite hU hUsurj t]
    exact forall₂_congr fun r _ => forall_smul_kernel_eq_zero_iff B S hS F hF _ U r
  · rw [idealPowerMultiple_eq_bot_iff_of_surjective_affine_chart B S hS F hF 𝓚 h𝓚 _
      (isCoherent_cokernel B S hS F hF (E.property.1 n) (E'.property.1 n)
        _).toIsQuasicoherentOnSite hU hUsurj t]
    exact forall₂_congr fun r _ =>
      forall_smul_cokernel_eq_zero_iff B S hS F hF (E.property.1 n) (E'.property.1 n) _ hU r

/-! ### The map `α_U` of Stacks 087W over a chart -/

/-- **The map `α_U : M ⟶ N` of Stacks 087W over an étale chart `U`.** Here `M` is the
`𝓘(U)`-adic completion of `lim_n F_n(U)`, which over a Noetherian affine chart is a finite module
over the completed ring `𝒪_X(U)^∧`
(`AlgebraicGeometry.Space.moduleFinite_chartCompletedSections`), and `α_U` is the map of
completions induced by the maps of sections `α_n(U)`. -/
def chartCompletedSectionsMap {E E' : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (α : E ⟶ E')
    (U : SmallEtale B S hS F) :
    chartCompletedSections B S hS F hF 𝓘 E U →ₗ[AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 U)
      (chartRing B S hS F hF U)] chartCompletedSections B S hS F hF 𝓘 E' U :=
  AdicCompletion.map (chartSectionIdeal B S hS F hF 𝓘 U)
    (chartSectionsLimitMap B S hS F hF α U).hom

/-! ### Condition (2) at one chart -/

/-- **Stacks 08BA, condition (2) at one chart.** For an étale chart `U` of `X`, with ring
`A = 𝒪_X(U)` and ideals `I = 𝓘(U)`, `K = 𝓚(U)`, the kernel and the cokernel of the map
`α_U : M ⟶ N` of Stacks 087W (`AlgebraicGeometry.Space.chartCompletedSectionsMap`) are
annihilated by `K ^ t` for some integer `t ≥ 1`. The modules `M` and `N` are modules over the
completion `A^∧`, and `K ^ t ⊆ A` acts on them through `A ⟶ A^∧`. -/
def IsChartKernelCokernelAnnihilated {E E' : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (α : E ⟶ E')
    (U : SmallEtale B S hS F) : Prop :=
  ∃ t : ℕ, 0 < t ∧
    chartIdeal B S hS ⟨F, hF⟩ 𝓚 U ^ t ≤ Module.annihilator (chartRing B S hS F hF U)
      ↥(LinearMap.ker ((chartCompletedSectionsMap B S hS F hF 𝓘 α U).restrictScalars
        (chartRing B S hS F hF U))) ∧
    chartIdeal B S hS ⟨F, hF⟩ 𝓚 U ^ t ≤ Module.annihilator (chartRing B S hS F hF U)
      (chartCompletedSections B S hS F hF 𝓘 E' U ⧸
        LinearMap.range ((chartCompletedSectionsMap B S hS F hF 𝓘 α U).restrictScalars
          (chartRing B S hS F hF U)))

/-- **The levelwise condition on the sections over a Noetherian affine chart is condition (2)
there.** This is the commutative algebra of the remark,
`Ideal.exists_pow_le_annihilator_ker_and_coker_mapQ_pow_iff`, applied to the map of the
`I`-adically complete modules `lim_n F_n(U) ⟶ lim_n G_n(U)`, whose reduction modulo `I ^ (n + 1)`
is `α_n(U)`; and the passage from these limits to their completions, which they are isomorphic
to. -/
theorem exists_chartSections_iff_isChartKernelCokernelAnnihilated
    (h𝓘 : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {E E' : CoherentAdicSystems B S hS F hF 𝓘} (α : E ⟶ E')
    {U : SmallEtale B S hS F} (hU : IsNoetherianAffineChart B S hS F U) :
    (∃ t : ℕ, 0 < t ∧ ∀ n : ℕ,
        (∀ r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓚 U ^ t, ∀ x : (E.obj.obj (op n)).val.obj (op U),
            (α.hom.app (op n)).val.app (op U) x = 0 → r • x = 0) ∧
          ∀ r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓚 U ^ t, ∀ y : (E'.obj.obj (op n)).val.obj (op U),
            ∃ x : (E.obj.obj (op n)).val.obj (op U),
              (α.hom.app (op n)).val.app (op U) x = r • y) ↔
      IsChartKernelCokernelAnnihilated B S hS F hF 𝓘 𝓚 α.hom U := by
  set I := chartSectionIdeal B S hS F hF 𝓘 U
  set K := chartIdeal B S hS ⟨F, hF⟩ 𝓚 U
  set φ := (chartSectionsLimitMap B S hS F hF α.hom U).hom
  have hEc := isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 E.property h𝓘 hU
  have hE'c := isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 E'.property h𝓘 hU
  -- the reduction of `lim_n G_n(U)` modulo `I ^ (n + 1)` is `G_n(U)`
  let red : ∀ (G : CoherentAdicSystems B S hS F hF 𝓘) (n : ℕ),
      (chartSectionsLimit B S hS F hF G.obj U ⧸
        (I ^ (n + 1) • ⊤ : Submodule (chartRing B S hS F hF U)
          (chartSectionsLimit B S hS F hF G.obj U))) ≃ₗ[chartRing B S hS F hF U]
        (G.obj.obj (op n)).val.obj (op U) := fun G n =>
    (Submodule.quotEquivOfEq _ _
        (ker_chartSectionsLevel B S hS F hF 𝓘 G.property h𝓘 hU n).symm).trans
      (LinearMap.quotKerEquivOfSurjective _
        (surjective_chartSectionsLevel B S hS F hF 𝓘 G.property hU.1 n))
  have hred : ∀ n x, ((α.hom.app (op n)).val.app (op U)).hom (red E n x) =
      red E' n (Submodule.mapQ _ _ φ (Submodule.smul_top_le_comap_smul_top _ φ) x) := by
    intro n x
    induction x using Submodule.Quotient.induction_on with
    | H m =>
      exact (congrArg (fun g => g.hom m)
        (chartSectionsLimitMap_chartSectionsLevel B S hS F hF α.hom U n)).symm
  -- the limits are their own completions
  let cpl : ∀ G : CoherentAdicSystems B S hS F hF 𝓘,
      IsAdicComplete I (chartSectionsLimit B S hS F hF G.obj U) →
      chartSectionsLimit B S hS F hF G.obj U ≃ₗ[chartRing B S hS F hF U]
        chartCompletedSections B S hS F hF 𝓘 G.obj U := fun G hG =>
    LinearEquiv.ofBijective (AdicCompletion.of I _) (AdicCompletion.of_bijective_iff.2 hG)
  have hcpl : ∀ x, ((chartCompletedSectionsMap B S hS F hF 𝓘 α.hom U).restrictScalars
      (chartRing B S hS F hF U)) (cpl E hEc x) = cpl E' hE'c (φ x) :=
    fun x => AdicCompletion.map_of I φ x
  unfold IsChartKernelCokernelAnnihilated
  refine Iff.trans ?_ ((Ideal.exists_pow_le_annihilator_ker_and_coker_mapQ_pow_iff I K φ).trans ?_)
  · refine exists_congr fun t => and_congr_right fun _ => forall_congr' fun n => ?_
    rw [Ideal.le_annihilator_ker_iff, Ideal.le_annihilator_coker_iff]
    exact and_congr
      (Ideal.kernel_annihilation_congr (red E n) (red E' n) _ _ (hred n) (K ^ t))
      (Ideal.cokernel_annihilation_congr (red E n) (red E' n) _ _ (hred n) (K ^ t))
  · refine exists_congr fun t => and_congr_right fun _ => and_congr ?_ ?_
    · exact (Ideal.le_annihilator_ker_iff _ _).trans
        ((Ideal.kernel_annihilation_congr (cpl E hEc) (cpl E' hE'c) φ _ hcpl (K ^ t)).symm.trans
          (Ideal.le_annihilator_ker_iff _ _).symm)
    · exact (Ideal.le_annihilator_coker_iff _ _).trans
        ((Ideal.cokernel_annihilation_congr (cpl E hEc) (cpl E' hE'c) φ _ hcpl (K ^ t)).symm.trans
          (Ideal.le_annihilator_coker_iff _ _).symm)

/-- **Stacks 08BA at one chart.** On a Noetherian algebraic space, for quasi-coherent sheaves of
ideals `𝓘, 𝓚`, a morphism `α` of `Coh(X, 𝓘)` and a surjective étale chart `U` with affine
underlying scheme, condition (1) holds exactly when condition (2) holds at `U`. -/
theorem isKernelCokernelAnnihilatedByPower_iff_isChartKernelCokernelAnnihilated
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ F)
    (h𝓘 : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (h𝓚 : 𝓚.toSheafOfModules.IsQuasicoherentOnSite)
    {E E' : CoherentAdicSystems B S hS F hF 𝓘} (α : E ⟶ E')
    {U : SmallEtale B S hS F} (hU : IsAffine (chartScheme U))
    (hUsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf U.1.hom) :
    IsKernelCokernelAnnihilatedByPower B S hS F hF 𝓚 α.hom ↔
      IsChartKernelCokernelAnnihilated B S hS F hF 𝓘 𝓚 α.hom U := by
  have hLN : IsLocallyNoetherian (chartScheme U) :=
    (exists_atlas_iff_forall_etale B S hS F (fun T : Scheme.{u} => IsLocallyNoetherian T)
      hF).1 hN.2.2 U.obj.left U.obj.hom U.property
  have hUN : IsNoetherianAffineChart B S hS F U :=
    ⟨hU, IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (chartScheme U)⟩⟩
  rw [isKernelCokernelAnnihilatedByPower_iff_chartSections B S hS F hF 𝓘 𝓚 h𝓚 α hU hUsurj]
  exact exists_chartSections_iff_isChartKernelCokernelAnnihilated B S hS F hF 𝓘 𝓚
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF _ h𝓘) α hUN

/-- **Stacks Project, Tag 08BA.** Let `X` be a Noetherian algebraic space over a scheme `S`, let
`𝓘, 𝓚 ⊆ 𝒪_X` be quasi-coherent sheaves of ideals and let `α : (F_n) ⟶ (G_n)` be a morphism of
`Coh(X, 𝓘)`. For a surjective étale morphism `U = Spec(A) ⟶ X` write `I, K ⊆ A` for the ideals of
`𝓘|_U, 𝓚|_U` and `α_U : M ⟶ N` for the map of finite `A^∧`-modules attached to `α|_U` by Stacks
087W. The following are equivalent:

1. there is an integer `t ≥ 1` such that `Ker(α_n)` and `Coker(α_n)` are annihilated by `𝓚 ^ t`
   for all `n`;
2. for any such `U`, the modules `Ker(α_U)` and `Coker(α_U)` are annihilated by `K ^ t` for some
   integer `t ≥ 1`;
3. for some such `U`, the modules `Ker(α_U)` and `Coker(α_U)` are annihilated by `K ^ t` for some
   integer `t ≥ 1`.

A chart `U ⟶ X` is an object of the small étale site of `X`, so étale; "`U = Spec(A)`" is
affineness of its underlying scheme; surjectivity is surjectivity after every representable base
change. Such a chart exists, by
`AlgebraicGeometry.Space.exists_surjective_isNoetherianAffineChart`, which is what makes (3) follow
from (2). -/
@[stacks 08BA "the equivalence of (1) with (2) for any, and for some, surjective etale affine \
chart U = Spec(A), with alpha_U the map of 087W"]
theorem isKernelCokernelAnnihilatedByPower_tfae
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ F)
    (h𝓘 : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (h𝓚 : 𝓚.toSheafOfModules.IsQuasicoherentOnSite)
    {E E' : CoherentAdicSystems B S hS F hF 𝓘} (α : E ⟶ E') :
    List.TFAE
      [IsKernelCokernelAnnihilatedByPower B S hS F hF 𝓚 α.hom,
        ∀ U : SmallEtale B S hS F, IsAffine (chartScheme U) →
          (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf U.1.hom →
          IsChartKernelCokernelAnnihilated B S hS F hF 𝓘 𝓚 α.hom U,
        ∃ U : SmallEtale B S hS F, IsAffine (chartScheme U) ∧
          (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf U.1.hom ∧
          IsChartKernelCokernelAnnihilated B S hS F hF 𝓘 𝓚 α.hom U] := by
  tfae_have 1 → 2 := fun h U hU hUsurj =>
    (isKernelCokernelAnnihilatedByPower_iff_isChartKernelCokernelAnnihilated B S hS F hF 𝓘 𝓚
      hZ hN h𝓘 h𝓚 α hU hUsurj).1 h
  tfae_have 2 → 3 := by
    intro h
    obtain ⟨U, hUN, hUsurj, -⟩ := exists_surjective_isNoetherianAffineChart B S hS hZ ⟨F, hF⟩ hN
    exact ⟨U, hUN.1, hUsurj, h U hUN.1 hUsurj⟩
  tfae_have 3 → 1 := fun ⟨U, hU, hUsurj, h⟩ =>
    (isKernelCokernelAnnihilatedByPower_iff_isChartKernelCokernelAnnihilated B S hS F hF
      𝓘 𝓚 hZ hN h𝓘 h𝓚 α hU hUsurj).2 h
  tfae_finish

end AlgebraicGeometry.Space

end
