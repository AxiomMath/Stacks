module

public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.CohomologyAffineReduction.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.RightDerivedOfDegreeZeroViaDeltaFunctors
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Precomp
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsSheafSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.ModuleCohomologyDeltaFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleSpacePullback.Basic

/-!
# The spellings of the cohomology of a module on a scheme agree as δ-functors

Let `X` be a scheme and `G` an `𝒪_X`-module. The cohomology `Hⁿ(X, G)` has several spellings in
this library: the right derived functors of `R`-linear global sections, for any morphism
`π : X ⟶ Spec R` (`Deformation.Artin.SectionsSheaf.cohomologyDeltaFunctor`, the spelling in which
the obstruction modules of Stacks 07YH are built); the long exact cohomology sequence of the
ringed space `X` (`Stacks.Cohomology.ModuleDelta.cohomologyDeltaFunctor`); and the cohomology of
the underlying abelian sheaf (`Stacks.Cohomology.AbelianColimit.H'deltaFunctor`), which agrees
with the others by Stacks 03FD. Once the module structures of the values are forgotten, all of
them are universal cohomological δ-functors (Stacks 010S) on the category of `𝒪_X`-modules, with
values in abelian groups and with global sections as degree-zero part. By Stacks 010U any two of
them are therefore identified by a unique isomorphism of δ-functors which is the identity on
global sections. In particular `|Hⁿ(X, -)|` does not depend on the affine base `Spec R` over
which `X` is regarded (`spellingIso`).

The same argument identifies the cohomology of `X` along an exact direct image: for a closed
immersion `i : X' ⟶ X` — or any morphism whose direct image of modules is exact —
`G ↦ |Hⁿ(X, i_* G)|` is a universal δ-functor on `𝒪_{X'}`-modules —
`i_*` need not preserve injective objects, but it carries them to modules acyclic for global
sections (Stacks 01EX, part (2)), which is all that universality needs — and the canonical
comparison `|Hⁿ(X, i_* G)| ≅ |Hⁿ(X', G)|` is the unique isomorphism of δ-functors that is the
identity `Γ(X, i_* G) = Γ(X', G)` in degree zero (`thickeningIso`).

Forgetting module structures uses one general construction: a cohomological δ-functor followed
by an exact functor is a cohomological δ-functor (`CategoryTheory.DeltaFunctor.postcomp`).

## Main definitions

* `CategoryTheory.DeltaFunctor.postcomp`: the δ-functor `n ↦ Fⁿ ⋙ Φ` for an exact functor `Φ`,
  with `postcompHom` and `postcompIso` on morphisms and isomorphisms.
* `Deformation.Artin.SectionsSheaf.abCohomology`: `|Hⁿ(X, -)|`, the cohomology δ-functor of
  `X` over `Spec R` with values in abelian groups, and `abCohomologyZeroIso`, its identification
  with global sections in degree zero.
* `Deformation.Artin.SectionsSheaf.moduleDeltaIso` and `abelianIso`: the comparisons with the
  cohomology of the ringed space `X` and with the cohomology of the underlying abelian sheaf
  (Stacks 03FD), as isomorphisms of δ-functors.
* `Deformation.Artin.SectionsSheaf.spellingIso`: the comparison of the cohomologies of `X` over
  two affine bases.
* `Deformation.Artin.SectionsSheaf.abCohomologyPushforward`: `G ↦ |Hⁿ(X, i_* G)|`, and
  `Deformation.Artin.SectionsSheaf.thickeningIso`, the comparison `|Hⁿ(X, i_* G)| ≅ |Hⁿ(X', G)|`.

## Main results

* `CategoryTheory.DeltaFunctor.hom_inv_id_app_app` and `inv_hom_id_app_app`: the components of
  an isomorphism of δ-functors cancel, objectwise.
* `CategoryTheory.DeltaFunctor.Effaceable.postcomp`: postcomposition with an exact functor
  preserves effaceability, hence (Stacks 010T) yields a universal δ-functor.
* `Deformation.Artin.SectionsSheaf.isUniversal_abCohomology`,
  `isUniversal_abCohomologyPushforward`: the δ-functors compared are universal.
* `Deformation.Artin.SectionsSheaf.spellingIso_refl`, `spellingIso_trans`, `spellingIso_symm`
  and `spellingIso_eq_abelianIso`: the comparisons between affine bases are coherent, and all
  factor through the cohomology of the underlying abelian sheaf, which involves no base.
* `Deformation.Artin.SectionsSheaf.thickeningIso_hom_app_zero_apply`,
  `thickeningIso_hom_comp_δ` (and its form on elements, `thickeningIso_hom_app_δ_apply`) and
  `thickeningIso_unique`: the comparison along `i` is the identity on sections in degree zero,
  commutes with every connecting morphism, and is the only morphism of δ-functors with the first
  property.

## Implementation notes

The comparisons are made with values in abelian groups because that is the only common target:
the `R`-linear and the `R'`-linear cohomologies of `X` land in different module categories, and
the cohomology of the underlying abelian sheaf carries no module structure at all.

Each comparison is pinned in degree zero only, as Stacks 010U pins it; no formula is claimed for
its positive-degree components.

`AlgebraicGeometry.Scheme.Modules` is a semireducible definition with its own `Category`
instance, so instances stated for functors between categories `Scheme.Modules _` are not found
for the same functors between the categories `SheafOfModules _.ringCatSheaf` in which the
cohomology δ-functors are stated. `modulesPushforward` is `Scheme.Modules.pushforward` with source
and target spelled `SheafOfModules`, and carries its additivity and exactness instances, so that
`ShortComplex.map` and `CategoryTheory.DeltaFunctor.precomp` elaborate along it. The identity
`Γ(X, i_* G) = Γ(X', G)` holds by unfolding the direct image; it is crossed once, in
`pushforwardSecFIso`, so that every other statement is well typed without unfolding.

For the same reason `abelianZeroIso` is written with source the degree-zero part of
`Stacks.Cohomology.AbelianColimit.H'deltaFunctor` on the nose, through the corepresentation of
global sections, rather than as `Stacks.Cohomology.ModuleSpacePullback.H'functorZeroIso`
whiskered: the two agree by `rfl` (`abelianZeroIso_hom_app_apply`), but the kernel checks that
agreement at the level of functors only by unfolding `Ext`, which takes about twenty
seconds per declaration that relies on it.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 010S](https://stacks.math.columbia.edu/tag/010S)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 010U](https://stacks.math.columbia.edu/tag/010U)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe v₁ u₁ v₂ u₂ v₃ u₃ u

/-! ### Components of an isomorphism of δ-functors -/

namespace CategoryTheory.DeltaFunctor

section IsoApp

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B] {F G : DeltaFunctor A B}

/-- For an isomorphism `e : F ≅ G` of δ-functors, the degree-`n` component of `e.hom` at `X`
followed by that of `e.inv` is the identity of `Fⁿ(X)`. -/
@[reassoc (attr := simp)]
theorem hom_inv_id_app_app (e : F ≅ G) (n : ℕ) (X : A) :
    (e.hom.app n).app X ≫ (e.inv.app n).app X = 𝟙 _ :=
  (isoApp e n).hom_inv_id_app X

/-- For an isomorphism `e : F ≅ G` of δ-functors, the degree-`n` component of `e.inv` at `X`
followed by that of `e.hom` is the identity of `Gⁿ(X)`. -/
@[reassoc (attr := simp)]
theorem inv_hom_id_app_app (e : F ≅ G) (n : ℕ) (X : A) :
    (e.inv.app n).app X ≫ (e.hom.app n).app X = 𝟙 _ :=
  (isoApp e n).inv_hom_id_app X

end IsoApp

/-! ### Postcomposing a δ-functor with an exact functor -/

section

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C]
  (Φ : B ⥤ C) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

/-- **A cohomological δ-functor followed by an exact functor is a cohomological δ-functor.**
Its degree-`n` component is `Fⁿ ⋙ Φ` and its connecting morphism at a short exact sequence `S`
is the image `Φ(δ)` of the connecting morphism of `F` at `S`. The long exact sequence of the
result is the image under `Φ` of that of `F`, which is exact because `Φ` is. -/
def postcomp (F : DeltaFunctor A B) : DeltaFunctor A C where
  functor n := F.functor n ⋙ Φ
  additive _ := inferInstance
  δ hS n := Φ.map (F.δ hS n)
  map_g_δ hS n := by
    rw [Functor.comp_map, ← Φ.map_comp, F.map_g_δ, Φ.map_zero]
  δ_map_f hS n := by
    rw [Functor.comp_map, ← Φ.map_comp, F.δ_map_f, Φ.map_zero]
  mono_map_f hS := by
    have := F.mono_map_f hS
    exact Φ.map_mono _
  exact_map hS n := (F.exact_map hS n).map Φ
  exact_δ₁ hS n := (F.exact_δ₁ hS n).map Φ
  exact_δ₂ hS n := (F.exact_δ₂ hS n).map Φ
  δ_naturality hS hT φ n := by
    rw [Functor.comp_map, Functor.comp_map, ← Φ.map_comp, ← Φ.map_comp,
      F.δ_naturality hS hT φ n]

variable (F : DeltaFunctor A B)

/-- The component functors of the postcomposed δ-functor. -/
@[simp]
theorem postcomp_functor (n : ℕ) : (F.postcomp Φ).functor n = F.functor n ⋙ Φ := rfl

/-- The connecting morphism of the postcomposed δ-functor is the image of the original one. -/
@[simp]
theorem postcomp_δ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (F.postcomp Φ).δ hS n = Φ.map (F.δ hS n) := rfl

/-- **A morphism of δ-functors postcomposes to a morphism of the postcomposed δ-functors.** Its
degree-`n` component is the whiskering of the degree-`n` component by `Φ`. -/
@[simps]
def postcompHom {F G : DeltaFunctor A B} (η : F ⟶ G) : F.postcomp Φ ⟶ G.postcomp Φ where
  app n := Functor.whiskerRight (η.app n) Φ
  comm hS n := (Φ.map_comp _ _).symm.trans
    ((congrArg Φ.map (η.comm hS n)).trans (Φ.map_comp _ _))

/-- Postcomposition sends the identity of a δ-functor to the identity. -/
@[simp]
theorem postcompHom_id : postcompHom Φ (𝟙 F) = 𝟙 (F.postcomp Φ) := by
  ext n X
  simp

/-- Postcomposition is compatible with composition of morphisms of δ-functors. -/
@[simp]
theorem postcompHom_comp {F G H : DeltaFunctor A B} (η : F ⟶ G) (γ : G ⟶ H) :
    postcompHom Φ (η ≫ γ) = postcompHom Φ η ≫ postcompHom Φ γ := by
  ext n X
  simp

/-- An isomorphism of δ-functors postcomposes to an isomorphism of the postcomposed
δ-functors. -/
@[simps]
def postcompIso {F G : DeltaFunctor A B} (e : F ≅ G) : F.postcomp Φ ≅ G.postcomp Φ where
  hom := postcompHom Φ e.hom
  inv := postcompHom Φ e.inv
  hom_inv_id := by rw [← postcompHom_comp, e.hom_inv_id, postcompHom_id]
  inv_hom_id := by rw [← postcompHom_comp, e.inv_hom_id, postcompHom_id]

end

section Effaceable

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C]
  (Φ : B ⥤ C) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  (F : DeltaFunctor A B)

/-- An effacement for `F` is an effacement for `F` followed by `Φ`: `Φ` carries the zero map
`Fⁿ⁺¹(ι) = 0` to zero. -/
def Effacement.postcomp {X : A} {n : ℕ} (e : F.Effacement X n) :
    (F.postcomp Φ).Effacement X n where
  I := e.I
  ι := e.ι
  map_ι := by rw [postcomp_functor, Functor.comp_map, e.map_ι, Φ.map_zero]

/-- **The postcomposition of an effaceable δ-functor with an exact functor is effaceable.** -/
instance Effaceable.postcomp [F.Effaceable] : (F.postcomp Φ).Effaceable where
  nonempty X n := ⟨(Effaceable.effacement F X n).postcomp Φ F⟩

end Effaceable

end CategoryTheory.DeltaFunctor

/-! ### Cohomology with values in abelian groups -/

namespace Deformation.Artin.SectionsSheaf

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Abelian

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R)

/-- The cohomology δ-functor of `X` with `R`-linear values is effaceable: the higher right
derived functors vanish on injective objects. -/
instance effaceable_cohomologyDeltaFunctor : (cohomologyDeltaFunctor π).Effaceable :=
  DeltaFunctor.Effaceable.of_isZero_injective _ fun n I _ =>
    (sectionsOverBase π).isZero_rightDerived_obj_injective_succ n I

/-- **The cohomology of `X` with values in abelian groups**, `|Hⁿ(X, -)|`: the cohomology
δ-functor of `X` over `Spec R` followed by the exact functor forgetting the `R`-module
structure. -/
def abCohomology : DeltaFunctor (SheafOfModules.{u} X.ringCatSheaf) AddCommGrpCat.{u} :=
  (cohomologyDeltaFunctor π).postcomp (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

/-- The degree-`n` component of `abCohomology π` is `Hⁿ(X, -)` with the `R`-module structure
forgotten. -/
theorem abCohomology_functor (n : ℕ) :
    (abCohomology π).functor n =
      (cohomologyDeltaFunctor π).functor n ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} :=
  rfl

/-- The connecting morphism of `abCohomology π` is that of the cohomology δ-functor, with the
`R`-module structure forgotten. -/
theorem abCohomology_δ {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)}
    (hS : S.ShortExact) (n : ℕ) :
    (abCohomology π).δ hS n =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map ((cohomologyDeltaFunctor π).δ hS n) :=
  rfl

/-- `|Hⁿ(X, -)|` is effaceable: forgetting module structures carries the effacements of the
cohomology δ-functor to effacements. -/
instance effaceable_abCohomology : (abCohomology π).Effaceable :=
  DeltaFunctor.Effaceable.postcomp _ _

/-- **`|Hⁿ(X, -)|` is a universal δ-functor** (Stacks 010T). -/
instance isUniversal_abCohomology : (abCohomology π).IsUniversal :=
  DeltaFunctor.isUniversal_of_effaceable _

/-- **`|H⁰(X, -)|` is the functor of abelian global sections.** This is the identification
`H⁰(X, -) ≅ Γ(X, -)` of `zeroIsoSections`, with the `R`-module structure forgotten; that
`R`-linear global sections with the module structure forgotten are abelian global sections holds
by definition. -/
def abCohomologyZeroIso : (abCohomology π).functor 0 ≅ secF X.ringCatSheaf ⊤ :=
  Functor.isoWhiskerRight (zeroIsoSections π) (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

/-- The inverse of `abCohomologyZeroIso` is the canonical map from global sections to their
zeroth right derived functor, with the `R`-module structure forgotten. -/
theorem abCohomologyZeroIso_inv_app (G : SheafOfModules.{u} X.ringCatSheaf) :
    (abCohomologyZeroIso π).inv.app G =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((sectionsOverBase π).toRightDerivedZero.app G) :=
  rfl

/-- The components of `abCohomologyZeroIso` are those of `zeroIsoSections`, with the `R`-module
structure forgotten. -/
theorem abCohomologyZeroIso_hom_app (G : SheafOfModules.{u} X.ringCatSheaf) :
    (abCohomologyZeroIso π).hom.app G =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map ((zeroIsoSections π).hom.app G) :=
  rfl

/-- **`|H⁰(X, -)|` is global sections, on elements**: a global section `s` of `G` is carried to
the class of `s` in `H⁰(X, G)` given by the canonical map from a functor to its zeroth right
derived functor. -/
theorem abCohomologyZeroIso_inv_app_apply (G : SheafOfModules.{u} X.ringCatSheaf)
    (s : ((secF X.ringCatSheaf ⊤).obj G : Type u)) :
    (abCohomologyZeroIso π).inv.app G s = (sectionsOverBase π).toRightDerivedZero.app G s :=
  rfl

/-! #### Comparison with the module cohomology of the ringed space -/

/-- In degree zero, the long exact cohomology sequence of the ringed space `X` is global
sections: `H⁰(X, -)` is the zeroth right derived functor of the left exact functor `Γ(X, -)`. -/
def moduleDeltaZeroIso (X : Scheme.{u}) :
    (Stacks.Cohomology.ModuleDelta.cohomologyDeltaFunctor X.ringCatSheaf ⊤).functor 0 ≅
      secF X.ringCatSheaf ⊤ :=
  (secF X.ringCatSheaf ⊤).rightDerivedZeroIsoSelf

/-- **`|Hⁿ(X, -)|` is the cohomology of the ringed space `X`.** The unique isomorphism of
cohomological δ-functors between the abelian-group cohomology of `X` over `Spec R` and
`Stacks.Cohomology.ModuleDelta.cohomologyDeltaFunctor`, the long exact cohomology sequence of
`X` as a ringed space, that is the identity on global sections in degree zero. Both are
universal, so this exists and is unique by Stacks 010U. -/
def moduleDeltaIso :
    abCohomology π ≅ Stacks.Cohomology.ModuleDelta.cohomologyDeltaFunctor X.ringCatSheaf ⊤ :=
  DeltaFunctor.IsUniversal.isoOfIso (abCohomologyZeroIso π ≪≫ (moduleDeltaZeroIso X).symm)

/-- In degree zero, `moduleDeltaIso` is the identity on global sections. -/
@[simp]
theorem moduleDeltaIso_hom_app_zero :
    (moduleDeltaIso π).hom.app 0 = (abCohomologyZeroIso π).hom ≫ (moduleDeltaZeroIso X).inv :=
  DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero _

/-- In degree zero, the inverse of `moduleDeltaIso` is the identity on global sections. -/
@[simp]
theorem moduleDeltaIso_inv_app_zero :
    (moduleDeltaIso π).inv.app 0 = (moduleDeltaZeroIso X).hom ≫ (abCohomologyZeroIso π).inv :=
  DeltaFunctor.IsUniversal.isoOfIso_inv_app_zero _

/-- `moduleDeltaIso` is the only isomorphism of δ-functors that is the identity on global
sections in degree zero. -/
theorem moduleDeltaIso_unique
    (e : abCohomology π ≅ Stacks.Cohomology.ModuleDelta.cohomologyDeltaFunctor X.ringCatSheaf ⊤)
    (he : e.hom.app 0 = (abCohomologyZeroIso π).hom ≫ (moduleDeltaZeroIso X).inv) :
    e = moduleDeltaIso π :=
  DeltaFunctor.IsUniversal.iso_ext (he.trans (moduleDeltaIso_hom_app_zero π).symm)

/-! #### Comparison with the cohomology of the underlying abelian sheaf (Stacks 03FD) -/

section Underlying

open Stacks.Cohomology.AbelianColimit

variable (X) in
/-- **`G ↦ H'ⁿ(X, G_ab)` is effaceable**: the higher cohomology of the underlying abelian sheaf
of an injective `𝒪_X`-module vanishes. This is the acyclicity input of Stacks 03FD,
`ModuleSheafCohomology.ext_eq_zero_of_injective_toSheaf`. -/
instance effaceable_H'deltaFunctor_precomp_toSheaf :
    ((H'deltaFunctor (⊤ : TopologicalSpace.Opens X)).precomp
      (SheafOfModules.toSheaf X.ringCatSheaf)).Effaceable :=
  DeltaFunctor.Effaceable.precomp _ _ fun G =>
    ⟨Injective.under G, Injective.ι G, inferInstance, fun n => by
      refine AddCommGrpCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩
      rw [ModuleSheafCohomology.ext_eq_zero_of_injective_toSheaf (Opens.grothendieckTopology X)
          X.ringCatSheaf (Injective.under G) ⊤ n a,
        ModuleSheafCohomology.ext_eq_zero_of_injective_toSheaf (Opens.grothendieckTopology X)
          X.ringCatSheaf (Injective.under G) ⊤ n b]⟩

variable (X) in
/-- **`G ↦ H'ⁿ(X, G_ab)` is a universal δ-functor** (Stacks 010T). -/
instance isUniversal_H'deltaFunctor_precomp_toSheaf :
    ((H'deltaFunctor (⊤ : TopologicalSpace.Opens X)).precomp
      (SheafOfModules.toSheaf X.ringCatSheaf)).IsUniversal :=
  DeltaFunctor.isUniversal_of_effaceable _

variable (X) in
/-- In degree zero, the cohomology of the underlying abelian sheaf is global sections:
`H'⁰(X, G_ab) = Ext⁰(ℤ_X, G_ab) ≅ Γ(X, G)`, the sheaf `ℤ_X` corepresenting global sections. This
is `Stacks.Cohomology.ModuleSpacePullback.H'functorZeroIso` (`abelianZeroIso_hom_app_apply`),
written so that its source is literally the degree-zero part of the δ-functor. -/
def abelianZeroIso :
    ((H'deltaFunctor (⊤ : TopologicalSpace.Opens X)).precomp
      (SheafOfModules.toSheaf X.ringCatSheaf)).functor 0 ≅ secF X.ringCatSheaf ⊤ :=
  Functor.isoWhiskerLeft (SheafOfModules.toSheaf X.ringCatSheaf)
    (Functor.leftUnitor _ ≪≫ ModuleSheafCohomology.extZeroIsoCoyoneda (freeOfOpen ⊤) ≪≫
      (ModuleSheafCohomology.evaluationRepresentation (Opens.grothendieckTopology X) ⊤).symm)

/-- `abelianZeroIso` is `Stacks.Cohomology.ModuleSpacePullback.H'functorZeroIso`, on elements. -/
theorem abelianZeroIso_hom_app_apply (G : SheafOfModules.{u} X.ringCatSheaf)
    (x : ((((H'deltaFunctor (⊤ : TopologicalSpace.Opens X)).precomp
      (SheafOfModules.toSheaf X.ringCatSheaf)).functor 0).obj G : Type u)) :
    (abelianZeroIso X).hom.app G x =
      (Stacks.Cohomology.ModuleSpacePullback.H'functorZeroIso ⊤).hom.app
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj G) x :=
  rfl

/-- The inverse of `abelianZeroIso` is that of
`Stacks.Cohomology.ModuleSpacePullback.H'functorZeroIso`, on elements. -/
theorem abelianZeroIso_inv_app_apply (G : SheafOfModules.{u} X.ringCatSheaf)
    (s : ((secF X.ringCatSheaf ⊤).obj G : Type u)) :
    (abelianZeroIso X).inv.app G s =
      (Stacks.Cohomology.ModuleSpacePullback.H'functorZeroIso ⊤).inv.app
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj G) s :=
  rfl

/-- **Stacks 03FD as an isomorphism of δ-functors**: the abelian-group cohomology of `X` over
`Spec R` is the cohomology of the underlying abelian sheaf, `|Hⁿ(X, G)| ≅ H'ⁿ(X, G_ab)`, by the
unique isomorphism of cohomological δ-functors that is the identity on global sections in
degree zero. -/
def abelianIso :
    abCohomology π ≅
      (H'deltaFunctor (⊤ : TopologicalSpace.Opens X)).precomp
        (SheafOfModules.toSheaf X.ringCatSheaf) :=
  DeltaFunctor.IsUniversal.isoOfIso (abCohomologyZeroIso π ≪≫ (abelianZeroIso X).symm)

/-- In degree zero, `abelianIso` is the identity on global sections. -/
@[simp]
theorem abelianIso_hom_app_zero :
    (abelianIso π).hom.app 0 = (abCohomologyZeroIso π).hom ≫ (abelianZeroIso X).inv :=
  DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero _

/-- In degree zero, the inverse of `abelianIso` is the identity on global sections. -/
@[simp]
theorem abelianIso_inv_app_zero :
    (abelianIso π).inv.app 0 = (abelianZeroIso X).hom ≫ (abCohomologyZeroIso π).inv :=
  DeltaFunctor.IsUniversal.isoOfIso_inv_app_zero _

/-- `abelianIso` is the only isomorphism of δ-functors that is the identity on global sections in
degree zero. -/
theorem abelianIso_unique
    (e : abCohomology π ≅
      (H'deltaFunctor (⊤ : TopologicalSpace.Opens X)).precomp
        (SheafOfModules.toSheaf X.ringCatSheaf))
    (he : e.hom.app 0 = (abCohomologyZeroIso π).hom ≫ (abelianZeroIso X).inv) :
    e = abelianIso π :=
  DeltaFunctor.IsUniversal.iso_ext (he.trans (abelianIso_hom_app_zero π).symm)

/-- **`abelianIso` commutes with the connecting morphisms**: for a short exact sequence `S` of
`𝒪_X`-modules, it carries the connecting morphism of `|H(X, -)|` at `S` to the connecting
morphism of the cohomology of abelian sheaves at the underlying sequence `S_ab`, which is
`Stacks.Cohomology.AbelianColimit.H'δ` (`Stacks.Cohomology.AbelianColimit.H'deltaFunctor_δ`). -/
theorem abelianIso_hom_comp_δ {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)}
    (hS : S.ShortExact) (n : ℕ) :
    ((abelianIso π).hom.app n).app S.X₃ ≫
        (H'deltaFunctor (⊤ : TopologicalSpace.Opens X)).δ
          (hS.map_of_exact (SheafOfModules.toSheaf X.ringCatSheaf)) n =
      (abCohomology π).δ hS n ≫ ((abelianIso π).hom.app (n + 1)).app S.X₁ :=
  (abelianIso π).hom.comm hS n

end Underlying

/-- **The higher cohomology of a module with acyclic global sections vanishes.** If the module
`G` is acyclic for global sections `Γ(X, -)` (valued in `Γ(X, 𝒪_X)`-modules), then
`|Hⁿ⁺¹(X, G)| = 0`, whichever affine base `X` is regarded over: forgetting module structures is
exact, so it commutes with the right derived functors on both sides. -/
theorem isZero_abCohomology_obj_of_rightAcyclic {G : SheafOfModules.{u} X.ringCatSheaf}
    (hG : (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightAcyclic G) (n : ℕ) :
    IsZero (((abCohomology π).functor (n + 1)).obj G) := by
  have h₁ := (Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived _ G).1 hG (n + 1)
    n.succ_pos
  have h₂ : IsZero (((secF X.ringCatSheaf ⊤).rightDerived (n + 1)).obj G) :=
    IsZero.of_iso ((forget₂ _ AddCommGrpCat.{u}).map_isZero h₁)
      ((Functor.rightDerivedCompIso (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
        (forget₂ _ AddCommGrpCat.{u}) (n + 1)).app G)
  exact IsZero.of_iso h₂
    ((Functor.rightDerivedCompIso (sectionsOverBase π)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (n + 1)).app G).symm

end Abelian

/-! ### Independence of the affine base -/

section Spelling

variable {R R' R'' : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R) (π' : X ⟶ Spec R')
  (π'' : X ⟶ Spec R'')

/-- **The abelian-group cohomology of a scheme does not depend on the affine base it is regarded
over.** For two structure morphisms `π : X ⟶ Spec R` and `π' : X ⟶ Spec R'`, the unique
isomorphism of cohomological δ-functors `|Hⁿ_π(X, -)| ≅ |Hⁿ_{π'}(X, -)|` that is the identity on
global sections in degree zero (Stacks 010U). -/
def spellingIso : abCohomology π ≅ abCohomology π' :=
  DeltaFunctor.IsUniversal.isoOfIso (abCohomologyZeroIso π ≪≫ (abCohomologyZeroIso π').symm)

/-- In degree zero, `spellingIso` is the identity on global sections. -/
@[simp]
theorem spellingIso_hom_app_zero :
    (spellingIso π π').hom.app 0 = (abCohomologyZeroIso π).hom ≫ (abCohomologyZeroIso π').inv :=
  DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero _

/-- In degree zero, the inverse of `spellingIso` is the identity on global sections. -/
@[simp]
theorem spellingIso_inv_app_zero :
    (spellingIso π π').inv.app 0 = (abCohomologyZeroIso π').hom ≫ (abCohomologyZeroIso π).inv :=
  DeltaFunctor.IsUniversal.isoOfIso_inv_app_zero _

/-- `spellingIso` is the only isomorphism of δ-functors that is the identity on global sections
in degree zero. -/
theorem spellingIso_unique (e : abCohomology π ≅ abCohomology π')
    (he : e.hom.app 0 = (abCohomologyZeroIso π).hom ≫ (abCohomologyZeroIso π').inv) :
    e = spellingIso π π' :=
  DeltaFunctor.IsUniversal.iso_ext (he.trans (spellingIso_hom_app_zero π π').symm)

/-- The comparison of a base with itself is the identity. -/
@[simp]
theorem spellingIso_refl : spellingIso π π = Iso.refl _ :=
  (spellingIso_unique π π _ (by simp)).symm

/-- The comparisons between three bases are compatible. -/
@[simp]
theorem spellingIso_trans : spellingIso π π' ≪≫ spellingIso π' π'' = spellingIso π π'' :=
  spellingIso_unique π π'' _ (by simp)

/-- The inverse of the comparison of `π` with `π'` is the comparison of `π'` with `π`. -/
@[simp]
theorem spellingIso_symm : (spellingIso π π').symm = spellingIso π' π :=
  spellingIso_unique π' π _ (by simp)

/-- **`spellingIso` passes through the cohomology of the ringed space `X`**, which involves no
base: it is `moduleDeltaIso π` followed by the inverse of `moduleDeltaIso π'`. -/
theorem spellingIso_eq_moduleDeltaIso :
    spellingIso π π' = moduleDeltaIso π ≪≫ (moduleDeltaIso π').symm := by
  refine (spellingIso_unique π π' _ ?_).symm
  simp

/-- **`spellingIso` passes through the cohomology of the underlying abelian sheaf**, which
involves no base: it is `abelianIso π` followed by the inverse of `abelianIso π'`. -/
theorem spellingIso_eq_abelianIso :
    spellingIso π π' = abelianIso π ≪≫ (abelianIso π').symm := by
  refine (spellingIso_unique π π' _ ?_).symm
  simpa using Iso.inv_hom_id_assoc (abelianZeroIso X) (abCohomologyZeroIso π').inv

end Spelling

/-! ### Cohomology along an exact direct image -/

section Pushforward

variable {R R' : CommRingCat.{u}} {X X' : Scheme.{u}} (π : X ⟶ Spec R) (i : X' ⟶ X)
  (π' : X' ⟶ Spec R')

/-- **The direct image `i_*` of sheaves of modules along a morphism of schemes**, with source and
target spelled `SheafOfModules _.ringCatSheaf` rather than `Scheme.Modules`. It is
`Scheme.Modules.pushforward i`; see the implementation notes for why the spelling matters. -/
abbrev modulesPushforward :
    SheafOfModules.{u} X'.ringCatSheaf ⥤ SheafOfModules.{u} X.ringCatSheaf :=
  Scheme.Modules.pushforward i

/-- Direct image of sheaves of modules is additive. -/
instance additive_modulesPushforward : (modulesPushforward i).Additive :=
  Stacks.SchemeCohomology.pushforward_additive i

/-- Direct image of sheaves of modules is left exact, being a right adjoint. -/
instance preservesFiniteLimits_modulesPushforward :
    PreservesFiniteLimits (modulesPushforward i) :=
  Stacks.SchemeCohomology.pushforward_preservesFiniteLimits i

/-- Direct image of sheaves of modules along a closed immersion is right exact. -/
instance preservesFiniteColimits_modulesPushforward [IsClosedImmersion i] :
    PreservesFiniteColimits (modulesPushforward i) :=
  Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward_of_isClosedImmersion i

/-- **Global sections of a direct image are global sections**: `Γ(X, i_* G) = Γ(X', G)`, by
definition of the direct image, `i⁻¹(X)` being `X'`. -/
def pushforwardSecFIso :
    modulesPushforward i ⋙ secF X.ringCatSheaf ⊤ ≅ secF X'.ringCatSheaf ⊤ :=
  Iso.refl _

/-- `pushforwardSecFIso` is the identity on sections. -/
@[simp]
theorem pushforwardSecFIso_hom_app_apply (G : SheafOfModules.{u} X'.ringCatSheaf)
    (s : ((secF X'.ringCatSheaf ⊤).obj G : Type u)) :
    (pushforwardSecFIso i).hom.app G s = s :=
  rfl

/-- The inverse of `pushforwardSecFIso` is the identity on sections. -/
@[simp]
theorem pushforwardSecFIso_inv_app_apply (G : SheafOfModules.{u} X'.ringCatSheaf)
    (s : ((secF X'.ringCatSheaf ⊤).obj G : Type u)) :
    (pushforwardSecFIso i).inv.app G s = s :=
  rfl

/-- **Stacks 01EX, part (2)**: the direct image of an injective `𝒪_{X'}`-module is acyclic for
global sections on `X`, for an arbitrary morphism of schemes. -/
theorem rightAcyclic_modulesPushforward_obj (I : SheafOfModules.{u} X'.ringCatSheaf)
    [Injective I] :
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightAcyclic ((modulesPushforward i).obj I) :=
  Stacks.SchemeCohomology.rightAcyclic_schemePushforward_obj i ⊤ I ‹_›

variable [PreservesFiniteColimits (modulesPushforward i)]

/-- **`G ↦ |Hⁿ(X, i_* G)|` as a cohomological δ-functor**, for a morphism `i : X' ⟶ X` whose
direct image of modules is exact (a closed immersion, for instance): the abelian-group
cohomology of `X` precomposed with `i_*`. -/
def abCohomologyPushforward :
    DeltaFunctor (SheafOfModules.{u} X'.ringCatSheaf) AddCommGrpCat.{u} :=
  (abCohomology π).precomp (modulesPushforward i)

/-- The degree-`n` component of `abCohomologyPushforward π i` is `G ↦ |Hⁿ(X, i_* G)|`. -/
theorem abCohomologyPushforward_functor (n : ℕ) :
    (abCohomologyPushforward π i).functor n =
      modulesPushforward i ⋙ (abCohomology π).functor n :=
  rfl

/-- The connecting morphism of `abCohomologyPushforward` at a short exact sequence `S` is that of
`abCohomology` at its direct image. -/
theorem abCohomologyPushforward_δ {S : ShortComplex (SheafOfModules.{u} X'.ringCatSheaf)}
    (hS : S.ShortExact)
    (hpS : (S.map (modulesPushforward i)).ShortExact) (n : ℕ) :
    (abCohomologyPushforward π i).δ hS n = (abCohomology π).δ hpS n :=
  rfl

/-- **`G ↦ |Hⁿ(X, i_* G)|` is effaceable.** An injective `𝒪_{X'}`-module `I` need not have an
injective direct image, but `i_* I` is acyclic for global sections (Stacks 01EX part (2),
`rightAcyclic_modulesPushforward_obj`), and that is all effaceability asks:
`|Hⁿ⁺¹(X, i_* I)| = 0`. -/
instance effaceable_abCohomologyPushforward : (abCohomologyPushforward π i).Effaceable :=
  DeltaFunctor.Effaceable.precomp _ _ fun G =>
    ⟨Injective.under G, Injective.ι G, inferInstance, fun n =>
      isZero_abCohomology_obj_of_rightAcyclic π
        (rightAcyclic_modulesPushforward_obj i (Injective.under G)) n⟩

/-- **`G ↦ |Hⁿ(X, i_* G)|` is a universal δ-functor** (Stacks 010T). -/
instance isUniversal_abCohomologyPushforward : (abCohomologyPushforward π i).IsUniversal :=
  DeltaFunctor.isUniversal_of_effaceable _

/-- The degree-zero identification `|H⁰(X, i_* G)| ≅ |H⁰(X', G)|`: both are global sections,
and `Γ(X, i_* G) = Γ(X', G)` (`pushforwardSecFIso`). -/
def thickeningZeroIso : (abCohomologyPushforward π i).functor 0 ≅ (abCohomology π').functor 0 :=
  Functor.isoWhiskerLeft (modulesPushforward i) (abCohomologyZeroIso π) ≪≫
    pushforwardSecFIso i ≪≫ (abCohomologyZeroIso π').symm

/-- **The canonical comparison `Hⁿ(X, i_* G) ≅ Hⁿ(X', G)`**, for `i : X' ⟶ X` with exact direct
image of modules (a closed immersion, in particular a thickening), with values in abelian
groups: the unique isomorphism of cohomological δ-functors in `G` that restricts in degree zero
to the identity `Γ(X, i_* G) = Γ(X', G)` (Stacks 010U). Its two characterizing properties —
the identity on sections in degree zero (`thickeningIso_hom_app_zero_apply`) and the
compatibility with every connecting morphism (`thickeningIso_hom_comp_δ`) — are exactly
`pushCohomologyIso_zero` and `pushCohomologyIso_boundary` of the statement of Stacks 07YH. -/
def thickeningIso : abCohomologyPushforward π i ≅ abCohomology π' :=
  DeltaFunctor.IsUniversal.isoOfIso (thickeningZeroIso π i π')

/-- In degree zero, `thickeningIso` is the identity on global sections. -/
@[simp]
theorem thickeningIso_hom_app_zero :
    (thickeningIso π i π').hom.app 0 = (thickeningZeroIso π i π').hom :=
  DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero _

/-- In degree zero, the inverse of `thickeningIso` is the identity on global sections. -/
@[simp]
theorem thickeningIso_inv_app_zero :
    (thickeningIso π i π').inv.app 0 = (thickeningZeroIso π i π').inv :=
  DeltaFunctor.IsUniversal.isoOfIso_inv_app_zero _

/-- The components of `thickeningZeroIso`. -/
theorem thickeningZeroIso_hom_app (G : SheafOfModules.{u} X'.ringCatSheaf) :
    (thickeningZeroIso π i π').hom.app G =
      (abCohomologyZeroIso π).hom.app ((modulesPushforward i).obj G) ≫
        (pushforwardSecFIso i).hom.app G ≫ (abCohomologyZeroIso π').inv.app G :=
  rfl

/-- **`thickeningIso` is the identity on global sections in degree zero**: the class in
`|H⁰(X, i_* G)|` of a global section of `i_* G` is carried to the class in `|H⁰(X', G)|` of the
same section of `G`. -/
@[reassoc]
theorem abCohomologyZeroIso_inv_app_comp_thickeningIso_hom_app
    (G : SheafOfModules.{u} X'.ringCatSheaf) :
    (abCohomologyZeroIso π).inv.app ((modulesPushforward i).obj G) ≫
        ((thickeningIso π i π').hom.app 0).app G =
      (pushforwardSecFIso i).hom.app G ≫ (abCohomologyZeroIso π').inv.app G := by
  rw [thickeningIso_hom_app_zero, thickeningZeroIso_hom_app, Iso.inv_hom_id_app_assoc]

/-- **`thickeningIso` is the identity on global sections in degree zero**, on elements. -/
theorem thickeningIso_hom_app_zero_apply (G : SheafOfModules.{u} X'.ringCatSheaf)
    (s : ((secF X'.ringCatSheaf ⊤).obj G : Type u)) :
    ((thickeningIso π i π').hom.app 0).app G
        ((abCohomologyZeroIso π).inv.app ((modulesPushforward i).obj G) s) =
      (abCohomologyZeroIso π').inv.app G s :=
  ConcreteCategory.congr_hom (abCohomologyZeroIso_inv_app_comp_thickeningIso_hom_app π i π' G) s

/-- **`thickeningIso` commutes with the connecting morphisms.** For a short exact sequence `S`
of `𝒪_{X'}`-modules, the comparison carries the connecting morphism of `|H(X, -)|` at the
direct image `i_* S` to that of `|H(X', -)|` at `S`. -/
theorem thickeningIso_hom_comp_δ {S : ShortComplex (SheafOfModules.{u} X'.ringCatSheaf)}
    (hS : S.ShortExact)
    (hpS : (S.map (modulesPushforward i)).ShortExact) (n : ℕ) :
    ((thickeningIso π i π').hom.app n).app S.X₃ ≫ (abCohomology π').δ hS n =
      (abCohomology π).δ hpS n ≫ ((thickeningIso π i π').hom.app (n + 1)).app S.X₁ :=
  (thickeningIso π i π').hom.comm hS n

/-- `thickeningIso` commutes with the connecting morphisms, in the form in which the connecting
morphism of `|H(X', -)|` is computed on `X` and read back on `X'`. -/
@[reassoc]
theorem thickeningIso_inv_app_comp_δ_comp_hom_app
    {S : ShortComplex (SheafOfModules.{u} X'.ringCatSheaf)} (hS : S.ShortExact)
    (hpS : (S.map (modulesPushforward i)).ShortExact) (n : ℕ) :
    ((thickeningIso π i π').inv.app n).app S.X₃ ≫ (abCohomology π).δ hpS n ≫
        ((thickeningIso π i π').hom.app (n + 1)).app S.X₁ =
      (abCohomology π').δ hS n :=
  (congrArg (((thickeningIso π i π').inv.app n).app S.X₃ ≫ ·)
    (thickeningIso_hom_comp_δ π i π' hS hpS n).symm).trans
    (DeltaFunctor.inv_hom_id_app_app_assoc _ _ _ _)

/-- **`thickeningIso` commutes with the connecting morphisms**, on elements: the connecting
morphism of `|H(X', -)|` at `S` is that of `|H(X, -)|` at `i_* S`, conjugated by
`thickeningIso`. -/
theorem thickeningIso_hom_app_δ_apply {S : ShortComplex (SheafOfModules.{u} X'.ringCatSheaf)}
    (hS : S.ShortExact) (hpS : (S.map (modulesPushforward i)).ShortExact) (n : ℕ)
    (x : (((abCohomology π').functor n).obj S.X₃ : Type u)) :
    ((thickeningIso π i π').hom.app (n + 1)).app S.X₁
        ((abCohomology π).δ hpS n (((thickeningIso π i π').inv.app n).app S.X₃ x)) =
      (abCohomology π').δ hS n x :=
  ConcreteCategory.congr_hom (thickeningIso_inv_app_comp_δ_comp_hom_app π i π' hS hpS n) x

/-- **`thickeningIso` is unique**: a morphism of δ-functors `|H(X, i_* -)| ⟶ |H(X', -)|` whose
degree-zero component is the identity on global sections is `thickeningIso`. -/
theorem thickeningIso_unique (η : abCohomologyPushforward π i ⟶ abCohomology π')
    (hη : η.app 0 = (thickeningZeroIso π i π').hom) : η = (thickeningIso π i π').hom :=
  DeltaFunctor.IsUniversal.hom_ext_zero _ (hη.trans (thickeningIso_hom_app_zero π i π').symm)

end Pushforward

end Deformation.Artin.SectionsSheaf

end
