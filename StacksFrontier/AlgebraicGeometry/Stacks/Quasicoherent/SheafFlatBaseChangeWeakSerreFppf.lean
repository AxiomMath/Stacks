module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineFlatBaseChangeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedFlatFppfRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.EtaleComparisonAcyclicity
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfEtaleCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeWeakSerre

/-!
# `LQCoh^fbc(𝒪_𝒳)` is a weak Serre subcategory of `Mod(𝒪_𝒳)`

Let `𝒳` be an algebraic stack and `ε : 𝒳_fppf ⟶ 𝒳_ét` the comparison morphism. Its direct image
`ε_*` (`AlgebraicGeometry.Stack.fppfModulesToEtaleModules`, which is
`AlgebraicGeometry.Stack.etaleComparisonPushforward`) reads an fppf sheaf of modules as an étale
sheaf of modules without changing the underlying presheaf, so it is fully faithful, and
membership in `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` is membership of the image under `ε_*` in
`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒳_ét, 𝒪_𝒳)`. Conversely every member of `LQCoh^fbc(𝒪_𝒳)` in
`Mod(𝒳_ét, 𝒪_𝒳)` is an fppf sheaf, by **Stacks 0771** part (1)
(`AlgebraicGeometry.Stack.fppfModuleOfLqcohSheafFbc`).

This file transports from the étale half of **Stacks 0771** part (2)
(`AlgebraicGeometry.Stack.isWeakSerreClass_lqcohSheafFbcEtaleModules`) the closure properties of
`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`, giving the fppf half of **Stacks 0771** part (2). The étale
kernel (cokernel) of `ε_* f`, for `f` a map between members, is a member, hence lifts to an fppf
module; `ε_*` being fully faithful, the lift is a kernel (cokernel) of `f` in `Mod(𝒪_𝒳)`
(`CategoryTheory.ObjectProperty.isClosedUnderKernels_of_fullyFaithful` and
`CategoryTheory.ObjectProperty.isClosedUnderCokernels_of_fullyFaithful`). For extensions,
`ε_*` keeps a short exact sequence short exact when its first term is a member, since then
`R¹ε_*` vanishes on it (**Stacks 075R** (1)), and the étale closure under extensions applies.

The abelian structure on `Mod(𝒪_𝒳)` is the one coming from the sheafification of abelian
presheaves on the fppf site (`AlgebraicGeometry.Stack.FlatFppf.hasSheafify_fppf_addCommGrpCat`).

## Main results

* `AlgebraicGeometry.Stack.containsZero_lqcohSheafFbcFppfModules`
* `AlgebraicGeometry.Stack.isClosedUnderIsomorphisms_lqcohSheafFbcFppfModules`
* `AlgebraicGeometry.Stack.isClosedUnderKernels_lqcohSheafFbcFppfModules`
* `AlgebraicGeometry.Stack.isClosedUnderCokernels_lqcohSheafFbcFppfModules`
* `AlgebraicGeometry.Stack.isClosedUnderExtensions_lqcohSheafFbcFppfModules`
* `AlgebraicGeometry.Stack.isWeakSerreClass_lqcohSheafFbcFppfModules`: **Stacks 0771** part (2),
  the fppf half.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 075R](https://stacks.math.columbia.edu/tag/075R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {D : Type*} [Category* D] [Abelian D]
  {Φ : C ⥤ D} [Φ.PreservesZeroMorphisms] (hΦ : Φ.FullyFaithful) {P : ObjectProperty C}
  {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms] (hPQ : ∀ X, P X ↔ Q (Φ.obj X))
  (hlift : ∀ Y, Q Y → ∃ X, Nonempty (Φ.obj X ≅ Y))
include hΦ hPQ hlift

/-- Closure under kernels descends along a fully faithful functor `Φ : C ⥤ D` into an abelian
category: if `P` is the inverse image of a property `Q` closed under kernels and every object
with `Q` lifts along `Φ`, then `P` is closed under kernels. -/
theorem isClosedUnderKernels_of_fullyFaithful [Q.IsClosedUnderKernels] :
    P.IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    obtain ⟨K, ⟨e⟩⟩ := hlift _ (Q.prop_kernel (Φ.map f) ((hPQ _).1 hX) ((hPQ _).1 hY))
    let ι : K ⟶ _ := hΦ.preimage (e.hom ≫ kernel.ι (Φ.map f))
    have hι : ι ≫ f = 0 := hΦ.map_injective (by
      rw [Φ.map_comp, hΦ.map_preimage, Category.assoc, kernel.condition, comp_zero,
        Φ.map_zero])
    have hl : IsLimit (KernelFork.ofι ι hι) :=
      KernelFork.IsLimit.ofι _ _
        (fun g hg => hΦ.preimage (kernel.lift (Φ.map f) (Φ.map g)
          (by rw [← Φ.map_comp, hg, Φ.map_zero]) ≫ e.inv))
        (fun g hg => hΦ.map_injective (by simp [ι]))
        (fun g hg m hm => hΦ.map_injective (by
          rw [hΦ.map_preimage, ← cancel_mono (e.hom ≫ kernel.ι (Φ.map f))]
          simp only [Category.assoc, Iso.inv_hom_id_assoc, kernel.lift_ι]
          rw [← hΦ.map_preimage (e.hom ≫ kernel.ι (Φ.map f)), ← Φ.map_comp]
          exact congrArg Φ.map hm))
    exact (hPQ _).2 (Q.prop_of_iso e.symm (Q.prop_kernel _ ((hPQ _).1 hX) ((hPQ _).1 hY)) |>
      Q.prop_of_iso (Φ.mapIso (hl.conePointUniqueUpToIso hk)))

/-- Closure under cokernels descends along a fully faithful functor `Φ : C ⥤ D` into an abelian
category: if `P` is the inverse image of a property `Q` closed under cokernels and every object
with `Q` lifts along `Φ`, then `P` is closed under cokernels. -/
theorem isClosedUnderCokernels_of_fullyFaithful [Q.IsClosedUnderCokernels] :
    P.IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    obtain ⟨K, ⟨e⟩⟩ := hlift _ (Q.prop_cokernel (Φ.map f) ((hPQ _).1 hX) ((hPQ _).1 hY))
    let π : _ ⟶ K := hΦ.preimage (cokernel.π (Φ.map f) ≫ e.inv)
    have hπ : f ≫ π = 0 := hΦ.map_injective (by
      rw [Φ.map_comp, hΦ.map_preimage, ← Category.assoc, cokernel.condition, zero_comp,
        Φ.map_zero])
    have hl : IsColimit (CokernelCofork.ofπ π hπ) :=
      CokernelCofork.IsColimit.ofπ _ _
        (fun g hg => hΦ.preimage (e.hom ≫ cokernel.desc (Φ.map f) (Φ.map g)
          (by rw [← Φ.map_comp, hg, Φ.map_zero])))
        (fun g hg => hΦ.map_injective (by simp [π]))
        (fun g hg m hm => hΦ.map_injective (by
          rw [hΦ.map_preimage, ← cancel_epi (cokernel.π (Φ.map f) ≫ e.inv)]
          simp only [Category.assoc, Iso.inv_hom_id_assoc, cokernel.π_desc]
          rw [← Category.assoc, ← hΦ.map_preimage (cokernel.π (Φ.map f) ≫ e.inv),
            ← Φ.map_comp]
          exact congrArg Φ.map hm))
    exact (hPQ _).2 (Q.prop_of_iso e.symm (Q.prop_cokernel _ ((hPQ _).1 hX) ((hPQ _).1 hY)) |>
      Q.prop_of_iso (Φ.mapIso (hl.coconePointUniqueUpToIso hk)))

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

-- The global instance `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is stated at a module
-- universe which is a `max` of four universe variables; at the module universe `u` of the
-- schemes used here, instance search against it leaves a stuck universe constraint. The instance
-- that applies is Mathlib's `SheafOfModules.instAbelian`.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

/-- The étale category `Mod(𝒳_ét, 𝒪_𝒳)` of an algebraic stack, over the structure sheaf at the
étale topology of the big site, in the spelling of
`AlgebraicGeometry.Stack.lqcohSheafFbcEtaleModules`. It is
`AlgebraicGeometry.Stack.etaleModules` up to unfolding the `AlgebraicGeometry.SiteKind`-indexed
topology, which instance search does not do. -/
abbrev etaleTopologyModules :=
  SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (etaleTopology B) (etaleTopology_le_topology B))

/-- **`ε_* : Mod(𝒪_𝒳) ⥤ Mod(𝒳_ét, 𝒪_𝒳)`**, the direct image of the comparison morphism
`ε : 𝒳_fppf ⟶ 𝒳_ét`, landing in the category on which
`AlgebraicGeometry.Stack.lqcohSheafFbcEtaleModules` is stated. It is
`AlgebraicGeometry.Stack.etaleComparisonPushforward`: neither the underlying presheaf of modules
nor the morphisms change. -/
noncomputable def fppfModulesToEtaleModules :
    fppfModulesUnivLE.{u, w, u} B S hS 𝒳 ⥤ etaleTopologyModules B S hS 𝒳 :=
  etaleComparisonPushforward B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids

/-- `ε_*` is fully faithful. -/
noncomputable def fullyFaithful_fppfModulesToEtaleModules :
    (fppfModulesToEtaleModules B S hS 𝒳).FullyFaithful :=
  Stacks.SheafOfModules.comparisonPushforwardFullyFaithful
    (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale) _

/-- `ε_*` is additive. -/
instance additive_fppfModulesToEtaleModules :
    (fppfModulesToEtaleModules B S hS 𝒳).Additive :=
  Stacks.SheafOfModules.additive_comparisonPushforward
    (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale) _

section Transport

variable {𝒳}

/-- Membership in `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` is membership of the image under `ε_*` in
`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒳_ét, 𝒪_𝒳)`: both are conditions on the same presheaf of modules. -/
theorem lqcohSheafFbcFppfModules_iff (F : fppfModulesUnivLE.{u, w, u} B S hS 𝒳) :
    lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F ↔
      lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒳
        ((fppfModulesToEtaleModules B S hS 𝒳).obj F) :=
  Iff.rfl

end Transport

/-- Every member of `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒳_ét, 𝒪_𝒳)` is, up to isomorphism, the image under `ε_*`
of an fppf module: it is an fppf sheaf by **Stacks 0771** part (1). -/
theorem exists_fppfModulesToEtaleModules_obj_iso (G : etaleTopologyModules B S hS 𝒳)
    (hG : lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒳 G) :
    ∃ F : fppfModulesUnivLE.{u, w, u} B S hS 𝒳,
      Nonempty ((fppfModulesToEtaleModules B S hS 𝒳).obj F ≅ G) :=
  ⟨(fppfModuleOfLqcohSheafFbc B E h S hS 𝒳 G hG).obj, ⟨Iso.refl _⟩⟩

/-- `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` is closed under isomorphisms. -/
instance isClosedUnderIsomorphisms_lqcohSheafFbcFppfModules :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    let := hasSheafify_etaleAssociatedTopology B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    let := wEqualsLocallyBijective_etaleAssociatedTopology B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids
    have := isWeakSerreClass_lqcohSheafFbcEtaleModules B E h S hS 𝒳
    exact (lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒳).prop_of_iso
      ((fppfModulesToEtaleModules B S hS 𝒳).mapIso e) hX

/-- `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` contains a zero object: a zero object of `LQCoh^fbc` in
`Mod(𝒳_ét, 𝒪_𝒳)` is an fppf sheaf by **Stacks 0771** part (1), and stays zero, `ε_*` being
fully faithful. -/
instance containsZero_lqcohSheafFbcFppfModules :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ContainsZero := by
  let := hasSheafify_etaleAssociatedTopology B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
  let := wEqualsLocallyBijective_etaleAssociatedTopology B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  have := isWeakSerreClass_lqcohSheafFbcEtaleModules B E h S hS 𝒳
  obtain ⟨Z, hZ, hLZ⟩ :=
    (lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒳).exists_prop_of_containsZero
  obtain ⟨Z', ⟨e⟩⟩ := exists_fppfModulesToEtaleModules_obj_iso B E h S hS 𝒳 Z hLZ
  let ε := fppfModulesToEtaleModules B S hS 𝒳
  refine ⟨Z', ?_, (lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒳).prop_of_iso e.symm hLZ⟩
  rw [IsZero.iff_id_eq_zero]
  apply (fullyFaithful_fppfModulesToEtaleModules B S hS 𝒳).map_injective
  rw [ε.map_id, ε.map_zero]
  exact (hZ.of_iso e).eq_of_src _ _

/-- **`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` is closed under kernels.** The étale kernel of `ε_* f` lies in
`LQCoh^fbc` (the étale half of **Stacks 0771** part (2)), so it is an fppf sheaf by part (1);
`ε_*` being fully faithful, it is then a kernel of `f` in `Mod(𝒪_𝒳)`. -/
instance isClosedUnderKernels_lqcohSheafFbcFppfModules :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).IsClosedUnderKernels := by
  let := hasSheafify_etaleAssociatedTopology B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
  let := wEqualsLocallyBijective_etaleAssociatedTopology B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  have := isWeakSerreClass_lqcohSheafFbcEtaleModules B E h S hS 𝒳
  exact ObjectProperty.isClosedUnderKernels_of_fullyFaithful
    (fullyFaithful_fppfModulesToEtaleModules B S hS 𝒳)
    (lqcohSheafFbcFppfModules_iff B E h S hS)
    (exists_fppfModulesToEtaleModules_obj_iso B E h S hS 𝒳)

/-- **`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` is closed under cokernels.** The étale cokernel of `ε_* f` lies
in `LQCoh^fbc` (the étale half of **Stacks 0771** part (2)), so it is an fppf sheaf by part (1);
`ε_*` being fully faithful, it is then a cokernel of `f` in `Mod(𝒪_𝒳)`. -/
instance isClosedUnderCokernels_lqcohSheafFbcFppfModules :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).IsClosedUnderCokernels := by
  let := hasSheafify_etaleAssociatedTopology B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
  let := wEqualsLocallyBijective_etaleAssociatedTopology B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  have := isWeakSerreClass_lqcohSheafFbcEtaleModules B E h S hS 𝒳
  exact ObjectProperty.isClosedUnderCokernels_of_fullyFaithful
    (fullyFaithful_fppfModulesToEtaleModules B S hS 𝒳)
    (lqcohSheafFbcFppfModules_iff B E h S hS)
    (exists_fppfModulesToEtaleModules_obj_iso B E h S hS 𝒳)

/-- A member of `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` is cartesian along flat morphisms between objects
lying over affine schemes, in the tensor-product form
`AlgebraicGeometry.FibredSite.IsCartesianAlongFlatAffines`: this is the step R2 of the proof of
**Stacks 0779** (`AlgebraicGeometry.Stack.isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules`),
read through `AlgebraicGeometry.Stack.isCartesianAlongFlatAffines_of_isIso_restrictionBaseChange`.
-/
theorem isCartesianAlongFlatAffines_of_lqcohSheafFbcFppfModules
    (F : fppfModulesUnivLE.{u, w, u} B S hS 𝒳)
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F) :
    FibredSite.IsCartesianAlongFlatAffines B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F :=
  isCartesianAlongFlatAffines_of_isIso_restrictionBaseChange B S hS _ _ F
    (fun φ hφ hz hx =>
      isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules B E h S hS F hF φ hφ hz hx)

/-- **`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` is closed under extensions.** For a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of fppf modules with `F₁` in `LQCoh^fbc`, the sequence `ε_*` of it is
short exact in `Mod(𝒳_ét, 𝒪_𝒳)`, since `R¹ε_*F₁ = 0` (**Stacks 075R** (1), through
`AlgebraicGeometry.Stack.shortExact_map_etaleComparisonPushforward_of_isCartesianAlongFlatAffines`
and the cartesian property of members). The étale half of **Stacks 0771** part (2) then puts
`F₂` in `LQCoh^fbc` when `F₃` is. -/
theorem lqcohSheafFbcFppfModules_X₂_of_shortExact
    {T : ShortComplex (fppfModulesUnivLE.{u, w, u} B S hS 𝒳)} (hT : T.ShortExact)
    (h₁ : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 T.X₁)
    (h₃ : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 T.X₃) :
    lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 T.X₂ := by
  have hT' := shortExact_map_etaleComparisonPushforward_of_isCartesianAlongFlatAffines B S hS 𝒳
    hT (isCartesianAlongFlatAffines_of_lqcohSheafFbcFppfModules B E h S hS 𝒳 T.X₁ h₁)
  let := hasSheafify_etaleAssociatedTopology B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
  let := wEqualsLocallyBijective_etaleAssociatedTopology B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  have := isWeakSerreClass_lqcohSheafFbcEtaleModules B E h S hS 𝒳
  let ε := etaleComparisonPushforward B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
  let T' : ShortComplex (etaleTopologyModules B S hS 𝒳) :=
    ShortComplex.mk (ε.map T.f) (ε.map T.g) (T.map ε).zero
  exact (lqcohSheafFbcFppfModules_iff B E h S hS T.X₂).2
    ((lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒳).prop_X₂_of_shortExact (S := T') hT' h₁ h₃)

/-- `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` is closed under extensions
(`AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules_X₂_of_shortExact`). -/
instance isClosedUnderExtensions_lqcohSheafFbcFppfModules :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hT h₁ h₃ :=
    lqcohSheafFbcFppfModules_X₂_of_shortExact B E h S hS 𝒳 hT h₁ h₃

/-- **Stacks 0771, part (2), the fppf half: `LQCoh^fbc(𝒪_𝒳)` is a weak Serre subcategory of
`Mod(𝒪_𝒳)`**, for an algebraic stack `𝒳`, at module universe `u`, with the abelian structure
coming from the sheafification of abelian presheaves on the fppf site
(`AlgebraicGeometry.Stack.FlatFppf.hasSheafify_fppf_addCommGrpCat`): it contains `0` and is
closed under isomorphisms, kernels, cokernels and extensions (**Stacks 0754**). -/
@[stacks 0771 "part (2), fppf half: LQCoh^fbc is a weak Serre subcategory of Mod(𝒪_𝒳), with the \
  flat base change property of 0762 read on sheaves; modules at the module universe u"]
instance isWeakSerreClass_lqcohSheafFbcFppfModules :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).IsWeakSerreClass where

end AlgebraicGeometry.Stack

end
