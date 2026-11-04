module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Automorphisms.PointwiseTrivial
public import StacksFrontier.Topology.Noetherian.LocallyConnected
public import StacksFrontier.Topology.Noetherian.QuasiCompactLocally

/-!
# Pullback of modules by an automorphism trivial on the underlying space

Let `X` be a connected reduced scheme of finite type over an infinite field `k`, and let
`f : X → X` be a `k`-automorphism which fixes every point of the underlying topological space.
Every module on `X` is isomorphic to its pullback along `f`.

The automorphism need not be the identity. A connected `X` is either of positive dimension,
in which case `f` is the identity by `AlgebraicGeometry.eq_id_of_eq_on_points`, or a one-point
scheme, which is the spectrum of a finite extension `L` of `k`; there `f` can act through a
nontrivial `k`-automorphism of `L`, and a module is only noncanonically isomorphic to its twist,
by transport along a basis.

## Main results

* `AlgebraicGeometry.exists_iso_pullback_of_eq_on_points_of_connectedSpace` gives the
  isomorphism of a module with its pullback.

## Implementation notes

The isomorphism is asserted to exist, not chosen canonically, and the statement is for an
arbitrary module rather than only for a coherent one. Finite type is expressed by local finite
type together with quasi-compactness of the structure morphism. Connectedness is an explicit
hypothesis: dropping it needs an isomorphism of modules to be glued from isomorphisms over the
pairwise disjoint open connected components, which is not available here.

## References

* [Stacks Project, Tag 0G05](https://stacks.math.columbia.edu/tag/0G05)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

private theorem subsingleton_of_irreducible_of_dimension_nonpos
    (space : Type*) [TopologicalSpace space] [T0Space space] [IrreducibleSpace space]
    (hdim : topologicalKrullDim space ≤ 0) : Subsingleton space := by
  have hmax := Order.krullDim_nonpos_iff_forall_isMax.mp hdim
  have hclosure (point : space) : closure ({point} : Set space) = Set.univ := by
    let closedPoint : TopologicalSpace.IrreducibleCloseds space :=
      ⟨closure {point}, isIrreducible_singleton.closure, isClosed_closure⟩
    let wholeSpace : TopologicalSpace.IrreducibleCloseds space :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ space, isClosed_univ⟩
    exact congrArg (fun closed : TopologicalSpace.IrreducibleCloseds space =>
      (closed : Set space))
      (le_antisymm (show wholeSpace ≤ closedPoint from hmax closedPoint (Set.subset_univ _))
        (Set.subset_univ _)).symm
  refine ⟨fun first second => ?_⟩
  apply (inseparable_iff_closure_eq.mpr ?_).eq
  rw [hclosure first, hclosure second]

private theorem isOpen_singleton_of_mem_irreducibleComponents
    {space : Type*} [TopologicalSpace space] [TopologicalSpace.NoetherianSpace space]
    (point : space) (hcomponent : ({point} : Set space) ∈ irreducibleComponents space) :
    IsOpen ({point} : Set space) := by
  obtain ⟨neighborhood, hopen, ⟨other, hother⟩, hsubset⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      {point} hcomponent
  have hother_eq : other = point := hsubset hother
  have heq : neighborhood = {point} := by
    apply Set.Subset.antisymm hsubset
    simpa [hother_eq] using Set.singleton_subset_iff.mpr hother
  rwa [heq] at hopen

private theorem isIso_fromTildeΓ_of_field
    (field : Type u) [Field field] (moduleSheaf : (Spec (.of field)).Modules) :
    IsIso moduleSheaf.fromTildeΓ := by
  let : Subsingleton (Spec (.of field)).toTopCat :=
    inferInstanceAs (Subsingleton (PrimeSpectrum field))
  let : IndiscreteTopology (Spec (.of field)).toTopCat := inferInstance
  let : Nonempty (Spec (.of field)).toTopCat := inferInstanceAs (Nonempty (PrimeSpectrum field))
  let : (modulesSpecToSheaf (R := .of field)).ReflectsIsomorphisms :=
    SpecModulesToSheafFullyFaithful.reflectsIsomorphisms
  apply (isIso_iff_of_reflects_iso _ (modulesSpecToSheaf (R := .of field))).mp
  apply (isIso_iff_of_reflects_iso _
    (TopCat.Sheaf.forget (ModuleCat field) (Spec (.of field)).toTopCat)).mp
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  rintro ⟨openSet⟩
  rcases eq_bot_or_eq_top openSet with rfl | rfl
  · let : Subsingleton Γ(moduleSheaf, ⊥) :=
      Module.subsingleton (Γ(Spec (.of field), ⊥)) _
    let : Subsingleton Γ(tilde ((moduleSpecΓFunctor (R := .of field)).obj moduleSheaf), ⊥) :=
      Module.subsingleton (Γ(Spec (.of field), ⊥)) _
    show IsIso ((modulesSpecToSheaf.map moduleSheaf.fromTildeΓ).hom.app (Opposite.op ⊥))
    let : Subsingleton ((modulesSpecToSheaf.obj moduleSheaf).obj.obj (Opposite.op ⊥)) :=
      inferInstanceAs (Subsingleton Γ(moduleSheaf, ⊥))
    let : Subsingleton Γ(tilde (R := CommRingCat.of field)
        ((modulesSpecToSheaf.obj moduleSheaf).presheaf.obj (Opposite.op ⊤)), ⊥) :=
      Module.subsingleton (Γ(Spec (.of field), ⊥)) _
    let : Subsingleton ((modulesSpecToSheaf.obj
        (tilde (R := CommRingCat.of field)
          ((modulesSpecToSheaf.obj moduleSheaf).presheaf.obj (Opposite.op ⊤)))).obj.obj
          (Opposite.op ⊥)) := inferInstanceAs (Subsingleton Γ(tilde
            (R := CommRingCat.of field)
            ((modulesSpecToSheaf.obj moduleSheaf).presheaf.obj (Opposite.op ⊤)), ⊥))
    exact (ModuleCat.isZero_of_subsingleton _).isIso (ModuleCat.isZero_of_subsingleton _) _
  · have comparison := Scheme.Modules.toOpen_fromTildeΓ_app moduleSheaf ⊤
    simp only [homOfLE_refl, CategoryTheory.op_id] at comparison
    let : IsIso (tilde.toOpen (R := CommRingCat.of field)
        ((modulesSpecToSheaf.obj moduleSheaf).presheaf.obj (Opposite.op ⊤)) ⊤) :=
      tilde.isIso_toOpen_top (R := CommRingCat.of field)
    have hcomparison :
        (modulesSpecToSheaf.map moduleSheaf.fromTildeΓ).hom.app (Opposite.op ⊤) =
          inv (tilde.toOpen (R := CommRingCat.of field)
            ((modulesSpecToSheaf.obj moduleSheaf).presheaf.obj (Opposite.op ⊤)) ⊤) :=
      IsIso.eq_inv_of_hom_inv_id
        (comparison.trans ((modulesSpecToSheaf.obj moduleSheaf).obj.map_id _))
    show IsIso ((modulesSpecToSheaf.map moduleSheaf.fromTildeΓ).hom.app (Opposite.op ⊤))
    rw [hcomparison]
    infer_instance

private theorem exists_iso_free_of_field
    (field : Type u) [Field field] (moduleSheaf : (Spec (.of field)).Modules) :
    ∃ index : Type u, Nonempty (moduleSheaf ≅ SheafOfModules.free index) := by
  let globalModule := (moduleSpecΓFunctor (R := .of field)).obj moduleSheaf
  let basis := Module.Free.chooseBasis field globalModule
  let := isIso_fromTildeΓ_of_field field moduleSheaf
  exact ⟨Module.Free.ChooseBasisIndex field globalModule,
    ⟨(asIso moduleSheaf.fromTildeΓ).symm ≪≫ (tilde.functor (.of field)).mapIso
      basis.repr.toModuleIso ≪≫ tildeFinsupp _⟩⟩

private theorem exists_iso_pullback_of_field
    (field : Type u) [Field field] (morphism : Spec (.of field) ⟶ Spec (.of field))
    (moduleSheaf : (Spec (.of field)).Modules) :
    Nonempty ((Scheme.Modules.pullback morphism).obj moduleSheaf ≅ moduleSheaf) := by
  obtain ⟨index, ⟨trivialization⟩⟩ := exists_iso_free_of_field field moduleSheaf
  let : (TopologicalSpace.Opens.map morphism.base).Final :=
    CategoryTheory.final_of_representablyFlat _
  let : (SheafOfModules.pushforward morphism.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs ((Scheme.Modules.pushforward morphism).IsRightAdjoint)
  exact ⟨(Scheme.Modules.pullback morphism).mapIso trivialization ≪≫
    SheafOfModules.pullbackObjFreeIso morphism.toRingCatSheafHom index ≪≫
    trivialization.symm⟩

private theorem exists_iso_pullback_of_iso
    {X Y : Scheme.{u}} (identification : X ≅ Y) (morphism : X ⟶ X)
    (moduleSheaf : X.Modules)
    (hiso : Nonempty ((Scheme.Modules.pullback
      (identification.inv ≫ morphism ≫ identification.hom)).obj
      ((Scheme.Modules.pullback identification.inv).obj moduleSheaf) ≅
      (Scheme.Modules.pullback identification.inv).obj moduleSheaf)) :
    Nonempty ((Scheme.Modules.pullback morphism).obj moduleSheaf ≅ moduleSheaf) := by
  obtain ⟨comparison⟩ := hiso
  have hcancel : identification.hom ≫
      (identification.inv ≫ morphism ≫ identification.hom) ≫ identification.inv = morphism := by
    simp [Category.assoc]
  exact ⟨((Scheme.Modules.pullbackCongr hcancel).app moduleSheaf).symm ≪≫
    ((Scheme.Modules.pullbackComp (identification.hom ≫
      (identification.inv ≫ morphism ≫ identification.hom)) identification.inv).app
      moduleSheaf).symm ≪≫
    ((Scheme.Modules.pullbackComp identification.hom
      (identification.inv ≫ morphism ≫ identification.hom)).app
      ((Scheme.Modules.pullback identification.inv).obj moduleSheaf)).symm ≪≫
    (Scheme.Modules.pullback identification.hom).mapIso comparison ≪≫
    (Scheme.Modules.pullbackComp identification.hom identification.inv).app moduleSheaf ≪≫
    (Scheme.Modules.pullbackCongr identification.hom_inv_id).app moduleSheaf ≪≫
    (Scheme.Modules.pullbackId X).app moduleSheaf⟩

/-- On a nonempty reduced scheme with at most one point, every module is isomorphic to its
pullback along any endomorphism. -/
theorem exists_iso_pullback_of_subsingleton
    {X : Scheme.{u}} [IsReduced X] [Nonempty X] [Subsingleton X]
    (morphism : X ⟶ X) (moduleSheaf : X.Modules) :
    Nonempty ((Scheme.Modules.pullback morphism).obj moduleSheaf ≅ moduleSheaf) := by
  let : IsAffine X := inferInstance
  let : PreirreducibleSpace X := inferInstance
  let : IrreducibleSpace X := ⟨inferInstance⟩
  let : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  let : Field Γ(X, ⊤) := (isField_of_isIntegral_of_subsingleton X).toField
  exact exists_iso_pullback_of_iso X.isoSpec morphism moduleSheaf
    (exists_iso_pullback_of_field Γ(X, ⊤) _ _)

/-- A connected Noetherian $T_0$ space either has at most one point, or each of its irreducible
components has positive Krull dimension. -/
theorem subsingleton_or_irreducibleComponents_positive
    (space : Type*) [TopologicalSpace space] [T0Space space] [ConnectedSpace space]
    [TopologicalSpace.NoetherianSpace space] :
    Subsingleton space ∨ ∀ component : irreducibleComponents space,
      0 < topologicalKrullDim (component : Set space) := by
  classical
  by_cases hsingle : Subsingleton space
  · exact Or.inl hsingle
  right
  intro component
  by_contra hpositive
  let : IrreducibleSpace (component : Set space) :=
    isIrreducible_iff_irreducibleSpace.mp component.property.1
  let : Subsingleton (component : Set space) :=
    subsingleton_of_irreducible_of_dimension_nonpos _ (le_of_not_gt hpositive)
  obtain ⟨point, hpoint⟩ := component.property.1.nonempty
  have heq : (component : Set space) = {point} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨hpoint, fun other hother => congrArg Subtype.val
      (Subsingleton.elim (⟨other, hother⟩ : (component : Set space)) ⟨point, hpoint⟩)⟩
  have hcomponent : ({point} : Set space) ∈ irreducibleComponents space := heq ▸ component.property
  have huniv : ({point} : Set space) = Set.univ :=
    IsClopen.eq_univ
      ⟨isClosed_of_mem_irreducibleComponents _ hcomponent,
        isOpen_singleton_of_mem_irreducibleComponents point hcomponent⟩
      (Set.singleton_nonempty point)
  have hpt (other : space) : other = point := by simpa [← huniv] using Set.mem_univ other
  exact hsingle ⟨fun first second => (hpt first).trans (hpt second).symm⟩

/-- The underlying topological space of a locally Noetherian scheme is locally Noetherian. -/
theorem isLocallyNoetherianSpace_of_isLocallyNoetherian (X : Scheme.{u})
    [IsLocallyNoetherian X] : TopologicalSpace.IsLocallyNoetherianSpace X := by
  intro x
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  let f := X.affineCover.f i
  let : IsNoetherianRing Γ(X, f.opensRange) :=
    IsLocallyNoetherian.component_noetherian ⟨_, isAffineOpen_opensRange f⟩
  refine ⟨_, f.opensRange.2, ⟨y, rfl⟩, ?_⟩
  convert! noetherianSpace_of_isAffineOpen f.opensRange (isAffineOpen_opensRange f)

namespace AlgebraicGeometry

/-- **Stacks 0G05 (1)** for a connected scheme: every module on a connected reduced scheme of
finite type over an infinite field `k` is isomorphic to its pullback along a `k`-automorphism
which fixes every point of the underlying topological space. Coherence is not needed. -/
-- The `@[stacks 0G05]` registration is deliberately absent here: this statement assumes its
-- own input, and eq_id_of_isIso_of_eq_on_points / exists_iso_pullback_of_isIso_of_eq_on_points
-- (PointwiseTrivialAut.lean) assume neither connectedness nor infiniteness.
-- A tag does not go on a declaration proved under hypotheses the source does not make.
theorem exists_iso_pullback_of_eq_on_points_of_connectedSpace
    {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p] [IsReduced X]
    [ConnectedSpace X] (f : X ⟶ X) (hf : f ≫ p = p) (hpoints : ∀ x : X, f x = x)
    (F : X.Modules) :
    Nonempty ((Scheme.Modules.pullback f).obj F ≅ F) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : TopologicalSpace.NoetherianSpace X := noetherianSpace_of_isLocallyNoetherianSpace X
    (isLocallyNoetherianSpace_of_isLocallyNoetherian X)
  rcases subsingleton_or_irreducibleComponents_positive X with hsingle | hpositive
  · let : Subsingleton X := hsingle
    exact exists_iso_pullback_of_subsingleton f F
  · have hfid := eq_id_of_eq_on_points p f hf hpoints (fun Z hZ ↦ hpositive ⟨Z, hZ⟩)
      (Or.inl ‹Infinite k›)
    exact ⟨(Scheme.Modules.pullbackCongr hfid).app _ ≪≫ (Scheme.Modules.pullbackId X).app _⟩

end AlgebraicGeometry

end
