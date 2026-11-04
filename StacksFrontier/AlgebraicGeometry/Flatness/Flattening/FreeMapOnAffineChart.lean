module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.StalkOverOpen
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep.FreeMap
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FibreSupportDimension
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StalkIsoSpreadout
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackRestrict
public import StacksFrontier.AlgebraicGeometry.Modules.StalkFreePullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.AffineOpenSurjectiveRestriction

/-!
# The free map on an affine chart of the base

This is the step of [Stacks, Tag 0815] that follows the application of [Stacks, Tag 0811]. Let
`q : Z ⟶ T` be a flat affine morphism, locally of finite presentation, with irreducible fibres, and
let `M` be a quasi-coherent module of finite type on `Z` which is finite locally free on an open
`V ⊆ Z` surjecting onto `T`. Around every point `t` of `T` there is then an affine open `A` on
whose preimage a map `β : 𝒪^r ⟶ M` is defined which is an isomorphism on an open of `q⁻¹(A)`
surjecting onto `A`.

That is the datum the induction step consumes: `β` is universally injective, so its cokernel has
strictly smaller fibre-support dimension and the inductive hypothesis applies to it, while the
short exact sequence `0 → 𝒪^r → M → coker β → 0` transports flatness of the strict transform
back to `M`.

## Main results

* `AlgebraicGeometry.exists_affineOpen_freeMap_isIso_surjective`: the statement above.

## Implementation notes

The construction has four steps. The generic point `z` of the fibre over `t` lies in `V`, because
`V` surjects onto `T` and a nonempty open of an irreducible space contains its generic point
(`AlgebraicGeometry.genericPoint_mem_open_of_surjective_on_base`); there `M` has finite free stalk
and is of finite presentation on a neighbourhood
(`AlgebraicGeometry.free_stalk_finitePresentation_of_isFiniteLocallyFree_over`, applied to the free
neighbourhood of `z` that [Stacks, Tag 0811] supplies — which is finite locally free by
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso`). On an affine open `A₀` around `q z` with
affine preimage, `AlgebraicGeometry.exists_freeMap_isIso_residueField` produces a map `α₀` from a
finite free module which is invertible over the residue field at `z`; Nakayama upgrades that to
invertibility on the stalk and then on a neighbourhood `W₁` of `z`
(`AlgebraicGeometry.isIso_stalk_of_isIso_residuePullback` and
`AlgebraicGeometry.exists_isIso_pullback_open_of_stalk_isIso_on_open`). Finally the base is
shrunk inside `A₀` to an affine `A` over which the image of `W₁` surjects
(`Stacks.Morphisms.exists_affineOpen_le_surjective_on_restriction`), and `α₀` is transported
along the inclusion of `q⁻¹(A)` in `q⁻¹(A₀)`.

The transport is where the composite-pullback isomorphisms are needed: the free module on
`q⁻¹(A₀)` pulls back to the free module on `q⁻¹(A)`, and the pullback of `M` to `q⁻¹(A₀)` pulls
back to the pullback of `M` to `q⁻¹(A)`, so `α₀` becomes a map `β` of the right type.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 01Y3](https://stacks.math.columbia.edu/tag/01Y3)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u v₁ u₁

namespace AlgebraicGeometry

/-- The generating sections of a module isomorphic to a finite free module, obtained by
transporting the standard ones along the inverse of the isomorphism, have invertible structure
map. -/
private theorem isIso_freeGeneratingSections_ofEpi_inv
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R} (I : Type u) (e : M ≅ SheafOfModules.free I) :
    IsIso ((SheafOfModules.free.generatingSections I).ofEpi e.inv).π := by
  rw [SheafOfModules.GeneratingSections.ofEpi_π, SheafOfModules.free.generatingSections_π]
  dsimp [SheafOfModules.free.generatingSections]
  show IsIso (𝟙 (SheafOfModules.free I) ≫ e.inv)
  simpa only [Category.id_comp] using e.isIso_inv

/-- A map of modules conjugated by two isomorphisms stays an isomorphism after pullback to an
open, wherever the map itself does.

Stated separately, for an arbitrary pair of isomorphisms, because inferring it inline on the
transported free map below exhausts the heartbeat budget. -/
private theorem isIso_pullback_map_conj {Y : Scheme.{u}} {G₁ G₂ M₁ M₂ : Y.Modules}
    (e₁ : G₁ ≅ G₂) (α : G₂ ⟶ M₁) (e₂ : M₁ ≅ M₂) (W : Y.Opens)
    (h : IsIso ((Scheme.Modules.pullback W.ι).map α)) :
    IsIso ((Scheme.Modules.pullback W.ι).map (e₁.hom ≫ α ≫ e₂.hom)) := by
  have := h
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **A map from a finite free module transports along an open immersion.** For `j : Y' ⟶ Y` an
open immersion and `α : 𝒪_Y^r ⟶ N`, there is a map `β : 𝒪_{Y'}^r ⟶ N'` — for any module `N'`
identified with the pullback of `N` — which is an isomorphism over every open of `Y'` on which
the pullback of `α` along the composite is.

Stated for an arbitrary open immersion and an arbitrary identification of the pullback rather
than for the inclusion of one preimage in another: specialising it makes the elaborator unfold
`Scheme.homOfLE` inside the coproduct comparison, which exhausts the heartbeat budget. -/
private theorem exists_freeMap_pullback {Y Y' : Scheme.{u}} (j : Y' ⟶ Y) [IsOpenImmersion j]
    {r : ℕ} {N : Y.Modules}
    (α : (∐ fun _ : Fin r => SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ N)
    {N' : Y'.Modules} (ec : (Scheme.Modules.pullback j).obj N ≅ N') :
    ∃ β : (∐ fun _ : Fin r => SheafOfModules.unit Y'.ringCatSheaf : Y'.Modules) ⟶ N',
      ∀ W : Y'.Opens, IsIso ((Scheme.Modules.pullback (W.ι ≫ j)).map α) →
        IsIso ((Scheme.Modules.pullback W.ι).map β) := by
  let P := Scheme.Modules.pullback j
  let eu : P.obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit Y'.ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorIsoPullback j).app _).symm ≪≫
      Scheme.Modules.restrictUnitIso j
  let ef : P.obj (∐ fun _ : Fin r => SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅
      (∐ fun _ : Fin r => SheafOfModules.unit Y'.ringCatSheaf : Y'.Modules) :=
    PreservesCoproduct.iso P _ ≪≫ Sigma.mapIso fun _ ↦ eu
  refine ⟨ef.inv ≫ P.map α ≫ ec.hom, fun W hW ↦ ?_⟩
  exact isIso_pullback_map_conj ef.symm (P.map α) ec W
    ((NatIso.isIso_map_iff (Scheme.Modules.pullbackComp W.ι j) α).mpr hW)

/-- **A free map on an affine chart of the base, invertible on an open surjecting onto that
chart.** Let `q : Z ⟶ T` be a flat affine morphism, locally of finite presentation, with
irreducible fibres, and let `M` be a quasi-coherent module of finite type on `Z` which is free of
some finite rank on a neighbourhood of every point of an open `V` surjecting onto `T`. Every point
`t` of `T` has an affine open neighbourhood `A` carrying a map `β : 𝒪^r ⟶ M|_{q⁻¹A}` from a finite
free module and an open `W₂ ⊆ q⁻¹(A)` surjecting onto `A` on which `β` is an isomorphism. -/
theorem exists_affineOpen_freeMap_isIso_surjective {Z T : Scheme.{u}} (q : Z ⟶ T)
    [IsAffineHom q] [Flat q] [LocallyOfFinitePresentation q]
    [∀ s : T, IrreducibleSpace (q.fiber s)]
    (M : Z.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (V : Z.Opens)
    (hVfree : ∀ z : Z, z ∈ V → ∃ (W : Z.Opens) (n : ℕ), z ∈ W ∧ W ≤ V ∧
      Nonempty (M.over W ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n))))
    (hVsurj : Function.Surjective (V.ι ≫ q).base) (t : T) :
    ∃ (A : T.Opens) (_ : t ∈ A) (_ : IsAffineOpen A) (r : ℕ)
      (β : (∐ fun _ : Fin r => SheafOfModules.unit (q ⁻¹ᵁ A).toScheme.ringCatSheaf :
          (q ⁻¹ᵁ A).toScheme.Modules) ⟶
        (Scheme.Modules.pullback (q ⁻¹ᵁ A).ι).obj M)
      (W₂ : (q ⁻¹ᵁ A).toScheme.Opens),
      Function.Surjective (W₂.ι ≫ (q ∣_ A)).base ∧
        IsIso ((Scheme.Modules.pullback W₂.ι).map β) := by
  -- the generic point of the fibre over `t`, as a point of `Z`
  set z : Z := q.fiberι t (genericPoint (q.fiber t)) with hz
  have hqz : q z = t := by
    have hmem : z ∈ Set.range (q.fiberι t).base := ⟨genericPoint (q.fiber t), rfl⟩
    rw [q.range_fiberι t] at hmem
    exact hmem
  have hzV : z ∈ V := genericPoint_mem_open_of_surjective_on_base q V hVsurj t
  obtain ⟨W₀, n₀, hzW₀, -, ⟨e₀⟩⟩ := hVfree z hzV
  obtain ⟨hzfree, hzfin, V₂, hzV₂, hV₂fp⟩ :=
    free_stalk_finitePresentation_of_generatingSections M W₀
      ((SheafOfModules.free.generatingSections (ULift.{u} (Fin n₀))).ofEpi e₀.inv)
      (isIso_freeGeneratingSections_ofEpi_inv _ e₀)
      (inferInstanceAs (Finite (ULift.{u} (Fin n₀)))) z hzW₀
  -- an affine neighbourhood of `t`, with affine preimage
  obtain ⟨-, ⟨A₀ : T.Opens, hA₀, rfl⟩, htA₀, -⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ t) isOpen_univ
  replace hA₀ : IsAffineOpen A₀ := hA₀
  have hzA₀ : q z ∈ A₀ := hqz ▸ htA₀
  have hz₀ : z ∈ q ⁻¹ᵁ A₀ := hzA₀
  let : IsAffine (q ⁻¹ᵁ A₀).toScheme := hA₀.preimage q
  -- a free map which is an isomorphism at the residue field of `z`
  set N₀ := (Scheme.Modules.pullback (q ⁻¹ᵁ A₀).ι).obj M with hN₀
  let : SheafOfModules.IsQuasicoherent (R := structureSheafRing Z.toRingedSpace) M :=
    inferInstanceAs (SheafOfModules.IsQuasicoherent (R := Z.ringCatSheaf) M)
  have : N₀.IsQuasicoherent :=
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      (q ⁻¹ᵁ A₀).ι.toLRSHom.toShHom M inferInstance
  have : N₀.IsFiniteType :=
    SheafOfModules.pullback_isFiniteType (q ⁻¹ᵁ A₀).ι.toLRSHom.toShHom M
  obtain ⟨r, α₀, hα₀⟩ := exists_freeMap_isIso_residueField N₀ ⟨z, hz₀⟩
  -- it is an isomorphism on the stalk at `z`, hence on an open neighbourhood of `z`
  obtain ⟨hGfree, hGfin⟩ :=
    Stacks.StalkFreeBridge.freeAndFinite_stalk_coproductUnit
      (X := (q ⁻¹ᵁ A₀).toScheme) r ⟨z, hz₀⟩
  have hstalk := isIso_stalk_of_isIso_residuePullback α₀ ⟨z, hz₀⟩ hGfree hGfin
    (Stacks.StalkFreeBridge.free_stalk_pullback (q ⁻¹ᵁ A₀).ι M ⟨z, hz₀⟩ hzfree)
    (Stacks.StalkFreeBridge.finite_stalk_pullback (q ⁻¹ᵁ A₀).ι M ⟨z, hz₀⟩ hzfin) hα₀
  have hGft := Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    (Stacks.StalkFreeBridge.coproductUnitIsoFree (X := (q ⁻¹ᵁ A₀).toScheme) r).symm
  obtain ⟨W₁, hy₀W₁, hα₀W₁⟩ :=
    @exists_isIso_pullback_open_of_stalk_isIso_on_open _ _ _ hGft α₀
      ((q ⁻¹ᵁ A₀).ι ⁻¹ᵁ V₂)
      (Stacks.Modules.isFinitePresentation_pullback_on_preimage (q ⁻¹ᵁ A₀).ι M V₂ hV₂fp)
      ⟨z, hz₀⟩ hzV₂ hstalk
  -- shrink the base inside `A₀` so that the open where `α₀` is an isomorphism surjects
  set W₁' : Z.Opens := (W₁.ι ≫ (q ⁻¹ᵁ A₀).ι).opensRange with hW₁'
  have hzW₁' : z ∈ W₁' := ⟨⟨⟨z, hz₀⟩, hy₀W₁⟩, rfl⟩
  obtain ⟨A, htA, hAA₀, hA, hAsurj⟩ :=
    Stacks.Morphisms.exists_affineOpen_le_surjective_on_restriction
      q q.isOpenMap W₁' z hzW₁' A₀ hzA₀
  rw [hqz] at htA
  -- transport the free map to the chart over the smaller base
  have hle : q ⁻¹ᵁ A ≤ q ⁻¹ᵁ A₀ := fun x hx ↦ hAA₀ hx
  have hj : Z.homOfLE hle ≫ (q ⁻¹ᵁ A₀).ι = (q ⁻¹ᵁ A).ι := Z.homOfLE_ι hle
  obtain ⟨β, hβ⟩ := exists_freeMap_pullback (Z.homOfLE hle) α₀
    ((Scheme.Modules.pullbackComp (Z.homOfLE hle) (q ⁻¹ᵁ A₀).ι).app M ≪≫
      (Scheme.Modules.pullbackCongr hj).app M)
  refine ⟨A, htA, hA, r, β, (q ⁻¹ᵁ A).ι ⁻¹ᵁ W₁', hAsurj, hβ _ ?_⟩
  refine isIso_pullback_map_of_range_le α₀ W₁ hα₀W₁ _ ?_
  rintro _ ⟨w, rfl⟩
  obtain ⟨v, hv⟩ := w.2
  have hvz : (q ⁻¹ᵁ A₀).ι (W₁.ι v) = (q ⁻¹ᵁ A₀).ι (Z.homOfLE hle w.1) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hj]
    exact hv
  have hvj : W₁.ι v = Z.homOfLE hle w.1 := (q ⁻¹ᵁ A₀).ι.isOpenEmbedding.injective hvz
  show (Z.homOfLE hle) w.1 ∈ W₁
  rw [← hvj]
  exact v.2

end AlgebraicGeometry

end
