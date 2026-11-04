module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStructureSheaf
public import StacksFrontier.AlgebraicGeometry.GradedLocalization.ModuleMaps

/-!
# Functoriality of the sheaf associated to a graded module

Let `S` be a commutative ring with a nonnegative grading `𝒮 : ℕ → σ`. A degree-preserving
linear map `φ : M →ₗ[S] N` of `ℤ`-graded `S`-modules induces a morphism `M̃ ⟶ Ñ` of the
associated sheaves on `Proj(S)`: in every homogeneous-prime fiber the map is the localization
of `φ`, and the local-fraction condition is preserved because `φ` carries a homogeneous
numerator of degree `n` to one of the same degree.

Under the standard-open identification `Γ(D₊(f), M̃) ≃ M₍f₎` of the associated-sheaf
construction, the induced morphism is the degree-zero part of the localized map
`M_f → N_f`. The construction is functorial, and is bundled as a functor out of a category
`GradedModuleCat` of graded modules and degree-preserving maps.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat`: the category of
  `ℤ`-graded `S`-modules with a chosen decomposition, and degree-preserving linear maps.
* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap`: the morphism
  of associated sheaves induced by a degree-preserving linear map.
* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafFunctor`: the
  bundled associated-sheaf functor.

## Main results

* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap_standardOpen`:
  on a positive-degree standard open the induced morphism is localization of `φ`.
* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap_id` and
  `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap_comp`: the
  functor laws.
* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafFunctor_obj` and
  `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafFunctor_map`: the
  bundled functor is the one just described.

## Implementation notes

The naturality of the stalk and global-sections identifications is
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafMap_stalk` and
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections_naturality`.

Equality on a standard open is stated in the ambient localized module
`LocalizedModule.Away f N`, where the canonical map `LocalizedModule.map` is already
available, rather than in the degree-zero submodule; the two statements are equivalent
because the degree-zero part is a submodule of the ambient localization.

The scalar action of `ℕ`-degrees on `ℤ`-degrees is the scoped instance
`Stacks.GradedLocalization.instVAddNatInt`, with respect to which `SetLike.GradedSMul 𝒮 𝒨`
expresses that a nonnegatively graded ring acts on an integer-graded module.

The associated sheaf is a `SheafOfModules.{max u v}` and not an
`AlgebraicGeometry.Scheme.Modules`: a section over an open of the homogeneous spectrum is a
dependent function on that open, so sections live in `max u v`. Consequently
`GradedModuleCat.{u, v, w}` has its carriers in `Type v` and the functor lands in
`SheafOfModules.{max u v}`.

## References

* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite TopCat DirectSum
open AlgebraicGeometry
open Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjSheafFunctoriality

universe u v w t t'

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- `ℤ`-graded modules over a fixed nonnegatively graded ring, each with a chosen
decomposition into homogeneous pieces. The carrier lives in `Type v`, independently of the
universe `u` of the ring. -/
structure GradedModuleCat {S : Type u} {σ : Type w} [CommRing S]
    [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮] where
  /-- The underlying `S`-module. -/
  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [module : Module S carrier]
  /-- The chosen grading of the carrier by the integers. -/
  grade : ℤ → AddSubgroup carrier
  [decomposition : Decomposition grade]
  [gradedSMul : SetLike.GradedSMul 𝒮 grade]

namespace GradedModuleCat

attribute [instance] addCommGroup module decomposition gradedSMul

/-- A degree-preserving morphism of graded modules: an `S`-linear map of the carriers that
sends each homogeneous piece into the homogeneous piece of the same degree. -/
structure Hom {S : Type u} {σ : Type w} [CommRing S]
    [SetLike σ S] [AddSubgroupClass σ S] {𝒮 : ℕ → σ} [GradedRing 𝒮]
    (M N : GradedModuleCat.{u, v, w} 𝒮) where
  /-- The underlying linear map. -/
  toLinearMap : M.carrier →ₗ[S] N.carrier
  /-- The map preserves every degree. -/
  map_grade : ∀ i (m : M.carrier), m ∈ M.grade i → toLinearMap m ∈ N.grade i

/-- The category of graded modules, with degree-preserving linear maps as morphisms. -/
instance {S : Type u} {σ : Type w} [CommRing S]
    [SetLike σ S] [AddSubgroupClass σ S] {𝒮 : ℕ → σ} [GradedRing 𝒮] :
    Category (GradedModuleCat.{u, v, w} 𝒮) where
  Hom := Hom
  id M := ⟨LinearMap.id, fun _ _ hm => hm⟩
  comp f g := ⟨g.toLinearMap.comp f.toLinearMap,
    fun i m hm => g.map_grade i _ (f.map_grade i m hm)⟩
  id_comp := by intro X Y f; cases f; rfl
  comp_id := by intro X Y f; cases f; rfl
  assoc := by intro W X Y Z f g h; cases f; cases g; cases h; rfl

end GradedModuleCat

variable {S : Type u} {M N : Type v} {σ : Type w} {τ : Type t} {υ : Type t'}
  [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]
  [SetLike υ N] [AddSubgroupClass υ N] (𝒩 : ℤ → υ) [Decomposition 𝒩]
  [SetLike.GradedSMul 𝒮 𝒩]

/-- Localizing away from `f` and then specializing to a fiber agrees with localizing at the
fiber directly, compatibly with a linear map. -/
private theorem moduleToFiber_natural (f : S) (x : ProjectiveSpectrum.basicOpen 𝒮 f)
    (φ : M →ₗ[S] N) (a : LocalizedModule.Away (R := S) f M) :
    ProjectiveSpectrum.Proj.moduleToFiber 𝒮 f x (LocalizedModule.map (Submonoid.powers f) φ a) =
      LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl φ
        (ProjectiveSpectrum.Proj.moduleToFiber (M := M) 𝒮 f x a) := by
  induction a using LocalizedModule.induction_on with
  | h m s => simp [ProjectiveSpectrum.Proj.moduleToFiber_mk, LocalizedModule.map_mk]

/-- The degree-zero part of the localized map `M_f → N_f`. It is the map on sections over
`D₊(f)` under the standard-open identification. -/
private noncomputable def degreeZeroLocalizedMap {f : S} (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) :
    GradedModuleDegreeZeroLocalization 𝒮 𝒨 f →ₗ[HomogeneousLocalization.Away 𝒮 f]
      GradedModuleDegreeZeroLocalization 𝒮 𝒩 f := by
  let T := Submonoid.powers f
  letI := Module.compHom (R := Localization.Away f)
    (LocalizedModule.Away (R := S) f M)
    (algebraMap (HomogeneousLocalization.Away 𝒮 f) (Localization.Away f))
  letI := Module.compHom (R := Localization.Away f)
    (LocalizedModule.Away (R := S) f N)
    (algebraMap (HomogeneousLocalization.Away 𝒮 f) (Localization.Away f))
  let g := LocalizedModule.map T φ
  refine {
    toFun := fun a => ⟨g a.1, ?_⟩
    map_add' a b := Subtype.ext (map_add g a.1 b.1)
    map_smul' := by
      intro c a
      apply Subtype.ext
      change g (algebraMap (HomogeneousLocalization.Away 𝒮 f)
        (Localization.Away f) c • a.1) = _
      rw [g.map_smul]
      rfl
  }
  have hmem (z : LocalizedModule.Away (R := S) f M)
      (hz : z ∈ GradedModuleDegreeZeroLocalization 𝒮 𝒨 f) :
      g z ∈ GradedModuleDegreeZeroLocalization 𝒮 𝒩 f := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨d, n, hf, m, hm, rfl⟩
      apply Submodule.subset_span
      refine ⟨d, n, hf, φ m, hφ (n • (d : ℤ)) m hm, ?_⟩
      simp [g, LocalizedModule.map_mk]
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb => simpa [g] using Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      change g (algebraMap (HomogeneousLocalization.Away 𝒮 f)
        (Localization.Away f) c • a) ∈ _
      rw [g.map_smul]
      exact Submodule.smul_mem _ c ha
  exact hmem a.1 a.2

/-- The map of associated sheaves on `Proj(S)` induced by a degree-preserving linear map
`φ : M →ₗ[S] N`. On the fiber at a homogeneous prime it is the localization of `φ`. -/
noncomputable def associatedModuleSheafMap (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) :
    ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨 ⟶
      ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩 := by
  letI : ∀ U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ,
      Module (((ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj U)
        ((ProjectiveSpectrum.Proj.modulePresheaf 𝒮 𝒨).obj U) :=
    fun U => ProjectiveSpectrum.Proj.modulePresheafModule 𝒮 𝒨 U
  letI : ∀ U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ,
      Module (((ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj U)
        ((ProjectiveSpectrum.Proj.modulePresheaf 𝒮 𝒩).obj U) :=
    fun U => ProjectiveSpectrum.Proj.modulePresheafModule 𝒮 𝒩 U
  let app : ∀ U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ,
      (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj U ⟶
      (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩).val.obj U := fun U => by
    let f : ProjectiveSpectrum.Proj.moduleSections 𝒮 𝒨 U.unop →
        ProjectiveSpectrum.Proj.moduleSections 𝒮 𝒩 U.unop := fun a => by
      refine ⟨fun x =>
        LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl φ (a.1 x), ?_⟩
      intro x
      obtain ⟨V, hxV, i, n, m, s, hm, hs, hn, ha⟩ := a.2 x
      exact ⟨V, hxV, i, n, φ m, s, hφ n m hm, hs, hn, fun y => by
        have hs' : s ∈ y.1.asHomogeneousIdeal.toIdeal.primeCompl := hn y
        have hval : a.1 (i y) = LocalizedModule.mk m ⟨s, hs'⟩ := ha y
        change LocalizedModule.map y.1.asHomogeneousIdeal.toIdeal.primeCompl φ
          (a.1 (i y)) = LocalizedModule.mk (φ m) ⟨s, hs'⟩
        rw [hval]
        simp⟩
    let L : ProjectiveSpectrum.Proj.moduleSections 𝒮 𝒨 U.unop →ₗ[
        (((ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj ⋙
          forget₂ CommRingCat.{u} RingCat.{u}).obj U)]
        ProjectiveSpectrum.Proj.moduleSections 𝒮 𝒩 U.unop := {
      toFun := f
      map_add' := by intro a b; apply Subtype.ext; funext x; simp [f]
      map_smul' := by
        intro r a
        apply Subtype.ext
        funext x
        change LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl φ
          (HomogeneousLocalization.val (r.1 x) • a.1 x) =
          HomogeneousLocalization.val (r.1 x) •
            LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl φ (a.1 x)
        obtain ⟨r', hr'⟩ := HomogeneousLocalization.mk_surjective (r.1 x)
        rw [← hr']
        simp
    }
    exact ModuleCat.ofHom L
  refine ⟨{ app := app, naturality := ?_ }⟩
  intro U V i
  apply ModuleCat.hom_ext
  ext a
  apply Subtype.ext
  funext x
  dsimp [ProjectiveSpectrum.Proj.associatedModuleSheaf, PresheafOfModules.ofPresheaf,
    ProjectiveSpectrum.Proj.modulePresheaf, app]
  rfl

/-- **Stacks Project, Tag 01M7.** On a positive-degree standard open, the induced sheaf map is
the degree-zero part of the localized map `M_f → N_f`, read inside the ambient localization:
the identification `Γ(D₊(f), M̃) = M₍f₎` of the tag is natural in the graded module. -/
theorem associatedModuleSheafMap_standardOpen (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i)
    {f : S} {d : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (s : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f))) :
    ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒩 hf hd
      ((associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ).val.app _ s) :
        GradedModuleDegreeZeroLocalization 𝒮 𝒩 f) :
          LocalizedModule.Away (R := S) f N) =
      LocalizedModule.map (Submonoid.powers f) φ
        (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf hd s :
          GradedModuleDegreeZeroLocalization 𝒮 𝒨 f) := by
  let eM := ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf hd
  let eN := ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒩 hf hd
  let a := eM s
  let b := degreeZeroLocalizedMap 𝒮 𝒨 𝒩 φ hφ a
  have hsec : ProjectiveSpectrum.Proj.degreeZeroToSection 𝒮 𝒩 f b =
      (associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ).val.app _ s := by
    apply Subtype.ext
    funext x
    have hs : ProjectiveSpectrum.Proj.degreeZeroToSection 𝒮 𝒨 f a = s := eM.symm_apply_apply s
    show ProjectiveSpectrum.Proj.moduleToFiber (M := N) 𝒮 f x
        (LocalizedModule.map (Submonoid.powers f) φ a.1) =
      LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl φ (s.1 x)
    rw [← hs]
    exact moduleToFiber_natural 𝒮 f x φ a.1
  have heq : eN ((associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ).val.app _ s) = b := by
    rw [← hsec]
    exact eN.apply_symm_apply b
  exact congrArg Subtype.val heq

omit [Decomposition 𝒨] in
/-- **Stacks Project, Tag 01M7.** The identity graded map induces the identity sheaf morphism:
the first functor law for `M ↦ M̃`. -/
theorem associatedModuleSheafMap_id :
    associatedModuleSheafMap 𝒮 𝒨 𝒨 (LinearMap.id : M →ₗ[S] M)
      (fun _ _ hm => hm) = 𝟙 _ := by
  ext U a
  apply Subtype.ext
  funext x
  simp [associatedModuleSheafMap]
  rfl

omit [Decomposition 𝒨] [Decomposition 𝒩] in
/-- **Stacks Project, Tag 01M7.** Composition of degree-preserving graded maps is preserved by
the associated-sheaf construction: the second functor law for `M ↦ M̃`. -/
theorem associatedModuleSheafMap_comp
    {P : Type v} [AddCommGroup P] [Module S P]
    {ρ : Type*} [SetLike ρ P] [AddSubgroupClass ρ P]
    (𝒬 : ℤ → ρ) [Decomposition 𝒬] [SetLike.GradedSMul 𝒮 𝒬]
    (φ : M →ₗ[S] N) (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i)
    (ψ : N →ₗ[S] P) (hψ : ∀ i (n : N), n ∈ 𝒩 i → ψ n ∈ 𝒬 i) :
    associatedModuleSheafMap 𝒮 𝒨 𝒬 (ψ.comp φ)
      (fun i m hm => hψ i (φ m) (hφ i m hm)) =
    associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ ≫
      associatedModuleSheafMap 𝒮 𝒩 𝒬 ψ hψ := by
  ext U a
  apply Subtype.ext
  funext x
  exact DFunLike.congr_fun
    (IsLocalizedModule.map_comp' x.1.asHomogeneousIdeal.toIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.1.asHomogeneousIdeal.toIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap x.1.asHomogeneousIdeal.toIdeal.primeCompl N)
      (LocalizedModule.mkLinearMap x.1.asHomogeneousIdeal.toIdeal.primeCompl P)
      φ ψ) _

/-- **Stacks Project, Tag 01M7.** The associated-sheaf construction `M ↦ M̃` as a functor from
graded `S`-modules with degree-preserving maps to sheaves of `𝒪_{Proj(S)}`-modules. -/
noncomputable def associatedModuleSheafFunctor :
    GradedModuleCat.{u, v, w} 𝒮 ⥤
      SheafOfModules.{max u v}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (ProjectiveSpectrum.Proj.structureSheaf 𝒮)) where
  obj X := ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 X.grade
  map {X Y} f := associatedModuleSheafMap 𝒮 X.grade Y.grade f.toLinearMap f.map_grade
  map_id X := associatedModuleSheafMap_id 𝒮 X.grade
  map_comp {X Y Z} f g := associatedModuleSheafMap_comp 𝒮
    X.grade Y.grade Z.grade f.toLinearMap f.map_grade g.toLinearMap g.map_grade

/-- The functor sends a graded module to its associated sheaf. -/
theorem associatedModuleSheafFunctor_obj (X : GradedModuleCat.{u, v, w} 𝒮) :
    (associatedModuleSheafFunctor 𝒮).obj X =
      ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 X.grade := rfl

/-- The functor acts on a graded map by the associated-sheaf morphism. -/
theorem associatedModuleSheafFunctor_map
    {X Y : GradedModuleCat.{u, v, w} 𝒮} (φ : X ⟶ Y) :
    (associatedModuleSheafFunctor 𝒮).map φ =
    eqToHom (associatedModuleSheafFunctor_obj 𝒮 X) ≫
        associatedModuleSheafMap 𝒮 X.grade Y.grade φ.toLinearMap φ.map_grade ≫
          eqToHom (associatedModuleSheafFunctor_obj 𝒮 Y).symm := by
  cases associatedModuleSheafFunctor_obj 𝒮 X
  cases associatedModuleSheafFunctor_obj 𝒮 Y
  rfl

end Stacks.AlgebraicGeometry.ProjSheafFunctoriality

end
