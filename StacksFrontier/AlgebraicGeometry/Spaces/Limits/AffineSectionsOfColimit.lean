module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.CategoryTheory.Sites.Modules.ColimitLocalSections

/-!
# Sections over an affine chart of a filtered colimit of modules on an algebraic space

Let `M` be the colimit of a filtered diagram `D` of modules on the small étale site of an
algebraic space.  A section of `M` over an étale chart with *affine* underlying scheme is the
image of a section of a single member of `D`, in two cases:

* the members are subobjects of `M` (the legs of the cocone are monomorphisms), with no further
  hypothesis;
* the members and `M` are quasi-coherent.

The reason is quasi-compactness: a section is locally the image of sections of members, an affine
chart is covered by finitely many charts of any covering, and a filtered diagram absorbs finitely
many indices.  In the quasi-coherent case the passage from the image of a member to the member
itself is Descent, Proposition 03DW, in the form
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite`.

## Main results

* `AlgebraicGeometry.Space.exists_mem_of_directed_of_locally`: a section over an affine chart
  which is locally in the members of a directed family of submodules is in one of them.
* `AlgebraicGeometry.Space.exists_eq_of_isColimit_of_mono`: the subobject case.
* `AlgebraicGeometry.Space.exists_eq_of_isColimit_of_isQuasicoherentOnSite`: the quasi-coherent
  case.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **A section over an affine chart which is locally in the members of a directed family of
submodules is in one of them.**  The covering refines to a finite one, and the family absorbs the
finitely many members used. -/
theorem exists_mem_of_directed_of_locally {M : Modules.{u, u} B S hS F hF} {ι : Type w}
    [Nonempty ι] (N : ι → M.Submodule) (hdir : Directed (· ≤ ·) N) {U : SmallEtale B S hS F}
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)))
    (x : M.val.obj (op U)) {R : Sieve U} (hR : R ∈ SmallEtale.topology B S hS F U)
    (hx : ∀ ⦃V : SmallEtale B S hS F⦄ (g : V ⟶ U), R g →
      ∃ i, M.val.map g.op x ∈ (N i).obj (op V)) :
    ∃ i, x ∈ (N i).obj (op U) := by
  classical
  obtain ⟨n, z, φ, -, hz, hcov, -⟩ :=
    SmallEtale.exists_finite_affine_etale_ofArrows_le B S hS F hU hR
  choose idx hidx using fun i : Fin n => hx (φ i) (hz i)
  obtain ⟨k, hk⟩ := hdir.finset_le (Finset.univ.image idx)
  refine ⟨k, (N k).isSheaf x ((SmallEtale.topology B S hS F).superset_covering
    ((Sieve.generate_le_iff _ _).2 ?_) hcov)⟩
  rintro V g ⟨i⟩
  exact hk (idx i) (Finset.mem_image_of_mem idx (Finset.mem_univ i)) _ (hidx i)

/-- **The subobject case.**  If `M` is a filtered colimit of modules along monomorphisms, a
section of `M` over an affine chart comes from a single member. -/
theorem exists_eq_of_isColimit_of_mono {K : Type w} [Category.{v} K] [IsFiltered K]
    {D : K ⥤ Modules.{u, u} B S hS F hF} {M : Modules.{u, u} B S hS F hF}
    (φ : D ⟶ (Functor.const K).obj M) (hc : IsColimit (Cocone.mk M φ))
    (hmono : ∀ k, Mono (φ.app k)) {U : SmallEtale B S hS F}
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)))
    (x : M.val.obj (op U)) :
    ∃ (k : K) (y : (D.obj k).val.obj (op U)), (φ.app k).val.app (op U) y = x := by
  have : Nonempty K := IsFiltered.nonempty
  let N : K → M.Submodule := fun k => Stacks.SheafOfModules.monoRange (φ.app k) (hmono k)
  have hle : ∀ {k k' : K} (g : k ⟶ k'), N k ≤ N k' := by
    rintro k k' g X x ⟨y, rfl⟩
    refine ⟨(D.map g).val.app X y, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app,
      ← SheafOfModules.comp_val, φ.naturality]
    rfl
  have hdir : Directed (· ≤ ·) N := fun k k' =>
    ⟨IsFiltered.max k k', hle (IsFiltered.leftToMax k k'), hle (IsFiltered.rightToMax k k')⟩
  obtain ⟨k, y, hy⟩ := exists_mem_of_directed_of_locally N hdir hU x
    (SheafOfModules.mem_jointImageSieve_of_isColimit φ hc x)
    (fun V g ⟨k, y, hy⟩ => ⟨k, y, hy⟩)
  exact ⟨k, y, hy⟩

/-- The abelian structure on modules, pinned at the universes in use: instance search otherwise
tries an instance at a module universe it cannot unify with `u` and stops there. -/
noncomputable local instance (priority := high) abelianModules :
    Abelian (Modules.{u, u} B S hS F hF) :=
  SheafOfModules.instAbelian _

set_option synthInstance.maxHeartbeats 200000 in
-- `epi_comp` in the proof needs a longer instance search for its `Epi` arguments
/-- **The quasi-coherent case.**  If a quasi-coherent module `M` is a filtered colimit of
quasi-coherent modules, a section of `M` over an affine chart comes from a single member. -/
theorem exists_eq_of_isColimit_of_isQuasicoherentOnSite {K : Type w} [Category.{v} K]
    [IsFiltered K] {D : K ⥤ Modules.{u, u} B S hS F hF} {M : Modules.{u, u} B S hS F hF}
    (φ : D ⟶ (Functor.const K).obj M) (hc : IsColimit (Cocone.mk M φ))
    (hD : ∀ k, (D.obj k).IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite)
    {U : SmallEtale B S hS F}
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)))
    (x : M.val.obj (op U)) :
    ∃ (k : K) (y : (D.obj k).val.obj (op U)), (φ.app k).val.app (op U) y = x := by
  have : Nonempty K := IsFiltered.nonempty
  let I : K → Subobject M := fun k => imageSubobject (φ.app k)
  let N : K → M.Submodule := fun k => Stacks.SheafOfModules.monoRange (I k).arrow inferInstance
  have hle : ∀ {k k' : K} (g : k ⟶ k'), N k ≤ N k' := by
    rintro k k' g X x ⟨z, rfl⟩
    have hI : I k ≤ I k' := by
      have : φ.app k = D.map g ≫ φ.app k' := by
        rw [φ.naturality]
        exact (Category.comp_id _).symm
      change imageSubobject (φ.app k) ≤ imageSubobject (φ.app k')
      rw [this]
      exact imageSubobject_comp_le _ _
    refine ⟨(Subobject.ofLE _ _ hI).val.app X z, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app,
      ← SheafOfModules.comp_val, Subobject.ofLE_arrow]
  have hdir : Directed (· ≤ ·) N := fun k k' =>
    ⟨IsFiltered.max k k', hle (IsFiltered.leftToMax k k'), hle (IsFiltered.rightToMax k k')⟩
  obtain ⟨k, z, hz⟩ := exists_mem_of_directed_of_locally N hdir hU x
    (SheafOfModules.mem_jointImageSieve_of_isColimit φ hc x)
    (fun V g ⟨k, y, hy⟩ => ⟨k, (factorThruImageSubobject (φ.app k)).val.app _ y, by
      rwa [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app,
        ← SheafOfModules.comp_val, imageSubobject_arrow_comp]⟩)
  -- the image is quasi-coherent, and the factorization onto it is surjective on affine sections
  have hIq : (Subobject.underlying.obj (I k)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_image B S hS F hF
      (isClosedUnderKernels_quasicoherentSheaves B S hS F hF
        (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS F hF))
      (isClosedUnderCokernels_quasicoherentSheaves B S hS F hF) (φ.app k) (hD k) hM
  have hepi : Epi (factorThruImageSubobject (φ.app k)) := by
    dsimp [factorThruImageSubobject]
    apply epi_comp
  obtain ⟨y, hy⟩ := surjective_val_app_of_epi_of_isQuasicoherentOnSite
    (factorThruImageSubobject (φ.app k)) hepi (hD k) hIq U hU z
  refine ⟨k, y, ?_⟩
  rw [← hz, ← hy, ← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, imageSubobject_arrow_comp]

end AlgebraicGeometry.Space

end
