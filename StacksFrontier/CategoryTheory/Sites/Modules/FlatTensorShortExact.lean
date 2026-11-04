module

public import StacksFrontier.CategoryTheory.Functor.Bifunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.FlatCover
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroGenerators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-!
# Tensoring a short exact sequence with a flat cokernel

A short exact sequence of sheaves of modules on a ringed small site whose final term is flat
stays short exact after tensoring with an arbitrary sheaf of modules.

## Main results

* `Stacks.SheafOfModules.FlatTensorShortExact.isFlat_extensionByZero_unit`: the extension by
  zero `j_{U!}O_U` of the structure sheaf of `U` is flat.
* `Stacks.SheafOfModules.FlatTensorShortExact.exists_epi_from_flat`: every sheaf of `O`-modules
  is a quotient of a flat sheaf of `O`-modules.
* `Stacks.SheafOfModules.FlatTensorShortExact.mono_app_map_f`: tensoring with any sheaf of
  modules keeps the left-hand map a monomorphism.
* `Stacks.SheafOfModules.FlatTensorShortExact.sheafTensorRight_shortExact_of_flat`: the
  tensored sequence is short exact.

## Implementation notes

Right exactness of `· ⊗_O ·` in each variable holds because `Mod(O)` is symmetric monoidal
closed, so each `M ⊗_O ·` is a left adjoint. It remains to show that the left-hand map stays a
monomorphism.

Resolve `G` by a flat `G'`, so that with `K = ker(G' → G)` there is a 3x3 diagram of tensor
products `S.Xᵢ ⊗_O G_j`. Its `G'` row is short exact because `G'` is flat, its `S.X₃` column is
short exact because `S.X₃` is flat, and every other row and column is right exact. The snake
lemma applied to the columns at `S.X₂` and `S.X₃` shows that their kernel row is exact; the four
lemma against the `S.X₁` column then gives the monomorphism. Flatness of `S.X₃` is used only as
exactness of `· ⊗_O S.X₃` on the kernel presentation of `G`, transported to `S.X₃ ⊗_O ·` by the
symmetry `flipIso`.

The site is small and all universes are equal to its object universe.

## References

* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace Stacks.SheafOfModules.FlatTensorShortExact

/-- In an abelian category: if `P ⟶ X ⟶ Y` is exact, `ι : Z ⟶ X` is a monomorphism killed by
`X ⟶ Y`, and `k : P ⟶ Z` factors `P ⟶ X` through `ι`, then `k` is an epimorphism. -/
lemma epi_of_exact_of_mono_fac {A : Type*} [Category* A] [Abelian A] {P X Y Z : A}
    (u : P ⟶ X) (g : X ⟶ Y) (hu : u ≫ g = 0)
    (hex : (ShortComplex.mk u g hu).Exact)
    (ι : Z ⟶ X) (hmono : Mono ι) (hι : ι ≫ g = 0) (k : P ⟶ Z) (hk : k ≫ ι = u) : Epi k := by
  have := hmono
  exact ShortComplex.epi_of_mono_of_epi_of_mono
    (R₁ := ShortComplex.mk u g hu) (R₂ := ShortComplex.mk ι g hι)
    { τ₁ := k, τ₂ := 𝟙 _, τ₃ := 𝟙 _
      comm₁₂ := by simpa using hk
      comm₂₃ := by simp }
    hex inferInstance inferInstance inferInstance

/-- `Mono` is closed under composition, with every argument explicit. -/
lemma mono_comp' {A : Type*} [Category* A] {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Mono f) (hg : Mono g) : Mono (f ≫ g) := by
  have := hf
  have := hg
  exact mono_comp f g

/-- `Mono` descends along a factorization, with every argument explicit. -/
lemma mono_of_fac {A : Type*} [Category* A] [Abelian A] {X Y Z : A}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hf : f ≫ g = h) (hh : Mono h) : Mono f := by
  have : Mono (f ≫ g) := by rwa [hf]
  exact mono_of_mono f g

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

attribute [local instance] _root_.SheafOfModules.monoidalCategory
  _root_.SheafOfModules.symmetricCategory

/-- A functor preserving finite colimits sends a short exact sequence to an exact sequence
with epimorphic last map. -/
private theorem exact_and_epi_map_of_shortExact {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    {T : ShortComplex A} (hT : T.ShortExact) : (T.map F).Exact ∧ Epi (F.map T.g) :=
  (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F).1 inferInstance T hT

/-- The functor `M ⊗_O -` preserves finite colimits. -/
instance preservesFiniteColimits_sheafTensor_obj
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) :
    PreservesFiniteColimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj M) :=
  ⟨fun _ _ _ ↦ ⟨inferInstance⟩⟩

/-- The functor `- ⊗_O M` preserves finite colimits. -/
instance preservesFiniteColimits_sheafTensor_flip_obj
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) :
    PreservesFiniteColimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.obj M) :=
  ⟨fun _ _ _ ↦ ⟨inferInstance⟩⟩

/-- The symmetry isomorphism of functors `M ⊗_O - ≅ - ⊗_O M`. -/
def flipIso (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj M ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.obj M :=
  ((SheafOfModules.sheafTensorNatIso R).app M).symm ≪≫
    BraidedCategory.tensorLeftIsoTensorRight M ≪≫
    ((flipFunctor _ _ _).mapIso (SheafOfModules.sheafTensorNatIso R)).app M

/-- For a flat sheaf of modules `F`, the functor `- ⊗_O F` preserves finite limits. -/
lemma preservesFiniteLimits_sheafTensor_flip_obj_of_isFlat
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) F) :
    PreservesFiniteLimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.obj F) :=
  (Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor.{u, u} R F |>.1 hF).1

/-- For a flat sheaf of modules `F`, the functor `F ⊗_O -` preserves finite limits. -/
lemma preservesFiniteLimits_sheafTensor_obj_of_isFlat
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) F) :
    PreservesFiniteLimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj F) :=
  ((exactFunctor _ _).prop_of_iso (flipIso R F).symm
    (Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor.{u, u} R F
      |>.1 hF)).1

/-- The extension by zero `j_{U!}O_U` of the structure sheaf of `U` is a flat sheaf of
`O`-modules. -/
theorem isFlat_extensionByZero_unit (U : C) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R)
      ((SheafOfModules.extensionByZero (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) U).obj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).over U))) := by
  have hinj : Presheaf.IsLocallyInjective J
      (AlgebraicGeometry.SheafOfModules.associatedRingMap J (𝟙 R.obj)) :=
    Presheaf.isLocallyInjective_of_injective J _ (fun _ _ _ h ↦ h)
  have hsurj : Presheaf.IsLocallySurjective J
      (AlgebraicGeometry.SheafOfModules.associatedRingMap J (𝟙 R.obj)) :=
    Presheaf.isLocallySurjective_of_surjective J _ (fun _ x ↦ ⟨x, rfl⟩)
  have hsheaf : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R)
      (SheafOfModules.sheafifiedFreeYoneda
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) U) :=
    Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification J
      (O := R.obj) (Osharp := R)
      (AlgebraicGeometry.SheafOfModules.associatedRingMap J (𝟙 R.obj)) _
      (Stacks.PresheafOfModules.FlatFreeYoneda.isFlat_freeYoneda R.obj U)
  exact (Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor.{u, u} R _).2
    ((exactFunctor _ _).prop_of_iso
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.mapIso
        (SheafOfModules.extensionByZeroIsoSheafifiedFreeYoneda
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) U).symm)
      ((Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor.{u, u} R _).1
        hsheaf))

/-- Every sheaf of `O`-modules is a quotient of a flat sheaf of `O`-modules. -/
theorem exists_epi_from_flat
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) :
    ∃ (P : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) (π : P ⟶ M),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) P ∧ Epi π :=
  ⟨_, SheafOfModules.fromGenerators (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) M,
    Stacks.SheafOfModules.FlatCoproduct.isFlat_coproduct.{u, u} _
      (fun i ↦ isFlat_extensionByZero_unit R i.1),
    SheafOfModules.epi_fromGenerators _ M⟩

section Main

variable
  {S : ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))}
  {G G' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)}

omit [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- For an epimorphism `π : G' ⟶ G`, the sequence `0 → ker π → G' → G → 0` is short exact. -/
lemma shortExact_kernelSequence (π : G' ⟶ G) [Epi π] :
    (ShortComplex.kernelSequence π).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact π) inferInstance
    (inferInstance : Epi π)

/-- The morphism `S.X₂ ⊗_O (ker π → G' → G) ⟶ S.X₃ ⊗_O (ker π → G' → G)` induced by `S.g`. -/
abbrev vmap (π : G' ⟶ G) :
    (ShortComplex.kernelSequence π).map
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj S.X₂) ⟶
      (ShortComplex.kernelSequence π).map
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj S.X₃) :=
  (ShortComplex.kernelSequence π).mapNatTrans
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).map S.g)

/-- The morphism `S.X₁ ⊗_O (ker π → G' → G) ⟶ S.X₂ ⊗_O (ker π → G' → G)` induced by `S.f`. -/
abbrev umap (π : G' ⟶ G) :
    (ShortComplex.kernelSequence π).map
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj S.X₁) ⟶
      (ShortComplex.kernelSequence π).map
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj S.X₂) :=
  (ShortComplex.kernelSequence π).mapNatTrans
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).map S.f)

/-- The composite `umap ≫ vmap` is zero. -/
lemma umap_comp_vmap (π : G' ⟶ G) : umap R (S := S) π ≫ vmap R (S := S) π = 0 := by
  apply ShortComplex.hom_ext <;>
    simp only [ShortComplex.comp_τ₁, ShortComplex.comp_τ₂, ShortComplex.comp_τ₃,
      ShortComplex.mapNatTrans_τ₁, ShortComplex.mapNatTrans_τ₂, ShortComplex.mapNatTrans_τ₃,
      ShortComplex.zero_τ₁, ShortComplex.zero_τ₂, ShortComplex.zero_τ₃,
      ← NatTrans.comp_app, ← Functor.map_comp, S.zero, Functor.map_zero,
      NatTrans.app_zero]

/-- The two tensored maps of `S` at a fixed `M` compose to zero. -/
lemma app_comp_app_zero
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).map S.f).app M ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).map S.g).app M = 0 := by
  rw [← NatTrans.comp_app, ← Functor.map_comp, S.zero, Functor.map_zero, NatTrans.app_zero]

/-- If `S` is short exact, then `S.X₁ ⊗_O M ⟶ S.X₂ ⊗_O M ⟶ S.X₃ ⊗_O M` is exact. -/
lemma exact_row (hS : S.ShortExact)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) :
    (ShortComplex.mk _ _ (app_comp_app_zero R (S := S) M)).Exact :=
  (exact_and_epi_map_of_shortExact
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.obj M) hS).1

/-- If `S` is short exact and `M` is flat, then `S.f ⊗_O M` is a monomorphism. -/
lemma mono_row_f_of_isFlat (hS : S.ShortExact)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) M) :
    Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).map S.f).app M) :=
  have _ := preservesFiniteLimits_sheafTensor_flip_obj_of_isFlat R M hM
  (ShortComplex.ShortExact.map_of_exact hS
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.obj M)).mono_f

/-- If `S.X₃` is flat and `π : G' ⟶ G` is an epimorphism, then
`0 → S.X₃ ⊗_O ker π → S.X₃ ⊗_O G' → S.X₃ ⊗_O G → 0` is short exact. -/
lemma shortExact_map_tensor_X₃
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) S.X₃)
    (π : G' ⟶ G) [Epi π] :
    ((ShortComplex.kernelSequence π).map
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj S.X₃)).ShortExact := by
  have _ := preservesFiniteLimits_sheafTensor_obj_of_isFlat R S.X₃ hflat
  exact ShortComplex.ShortExact.map_of_exact (shortExact_kernelSequence R π) _

/-- The snake input formed by `vmap`, its kernel and its cokernel, whose middle rows are
`S.X₂ ⊗_O (ker π → G' → G)` and `S.X₃ ⊗_O (ker π → G' → G)`. -/
def snakeInput
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) S.X₃)
    (π : G' ⟶ G) [Epi π] :
    ShortComplex.SnakeInput
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) where
  L₀ := kernel (vmap R (S := S) π)
  L₁ := (ShortComplex.kernelSequence π).map
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj S.X₂)
  L₂ := (ShortComplex.kernelSequence π).map
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj S.X₃)
  L₃ := cokernel (vmap R (S := S) π)
  v₀₁ := kernel.ι _
  v₁₂ := vmap R (S := S) π
  v₂₃ := cokernel.π _
  w₀₂ := kernel.condition _
  w₁₃ := cokernel.condition _
  h₀ := kernelIsKernel _
  h₃ := cokernelIsCokernel _
  L₁_exact :=
    ((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj S.X₂)).1 inferInstance _
        (shortExact_kernelSequence R π)).1
  epi_L₁_g :=
    ((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj S.X₂)).1 inferInstance _
        (shortExact_kernelSequence R π)).2
  L₂_exact := (shortExact_map_tensor_X₃ R hflat π).exact
  mono_L₂_f := (shortExact_map_tensor_X₃ R hflat π).mono_f

/-! ### The kernel of `vmap` -/

/-- If `S.X₃` is flat, the kernel of `vmap` is an exact short complex. -/
lemma exact_kernel_vmap
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) S.X₃)
    (π : G' ⟶ G) [Epi π] : (kernel (vmap R (S := S) π)).Exact :=
  (snakeInput R (S := S) hflat π).L₀_exact

/-- The first component of the kernel inclusion of `vmap` is a monomorphism. -/
lemma mono_kernelι_vmap_τ₁
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) S.X₃)
    (π : G' ⟶ G) [Epi π] : Mono (kernel.ι (vmap R (S := S) π)).τ₁ :=
  (snakeInput R (S := S) hflat π).mono_v₀₁_τ₁

/-- The third component of the kernel inclusion of `vmap` is a monomorphism. -/
lemma mono_kernelι_vmap_τ₃
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) S.X₃)
    (π : G' ⟶ G) [Epi π] : Mono (kernel.ι (vmap R (S := S) π)).τ₃ :=
  (snakeInput R (S := S) hflat π).mono_v₀₁_τ₃

/-- The first component of the kernel inclusion of `vmap`, followed by `S.g ⊗_O ker π`, is
zero. -/
lemma kernelι_vmap_comp_τ₁
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) S.X₃)
    (π : G' ⟶ G) [Epi π] :
    (kernel.ι (vmap R (S := S) π)).τ₁ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).map S.g).app
        (ShortComplex.kernelSequence π).X₁ = 0 :=
  (snakeInput R (S := S) hflat π).w₀₂_τ₁

/-! ### The comparison map from the `S.X₁` column into the kernel row -/

/-- The morphism from `S.X₁ ⊗_O (ker π → G' → G)` to the kernel of `vmap` induced by `umap`. -/
noncomputable def cmp (π : G' ⟶ G) :
    (ShortComplex.kernelSequence π).map
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj S.X₁) ⟶
      kernel (vmap R (S := S) π) :=
  kernel.lift (vmap R (S := S) π) (umap R (S := S) π) (umap_comp_vmap R π)

/-- The comparison map followed by the kernel inclusion of `vmap` is `umap`. -/
lemma cmp_comp_kernelι (π : G' ⟶ G) :
    cmp R (S := S) π ≫ kernel.ι (vmap R (S := S) π) = umap R (S := S) π :=
  kernel.lift_ι _ _ _

/-- In the first component, the comparison map followed by the kernel inclusion of `vmap` is
`S.f ⊗_O ker π`. -/
lemma cmp_τ₁ (π : G' ⟶ G) :
    (cmp R (S := S) π).τ₁ ≫ (kernel.ι (vmap R (S := S) π)).τ₁ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).map S.f).app
        (ShortComplex.kernelSequence π).X₁ := by
  rw [← ShortComplex.comp_τ₁, cmp_comp_kernelι, ShortComplex.mapNatTrans_τ₁]

/-- In the second component, the comparison map followed by the kernel inclusion of `vmap` is
`S.f ⊗_O G'`. -/
lemma cmp_τ₂ (π : G' ⟶ G) :
    (cmp R (S := S) π).τ₂ ≫ (kernel.ι (vmap R (S := S) π)).τ₂ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).map S.f).app
        (ShortComplex.kernelSequence π).X₂ := by
  rw [← ShortComplex.comp_τ₂, cmp_comp_kernelι, ShortComplex.mapNatTrans_τ₂]

/-- In the third component, the comparison map followed by the kernel inclusion of `vmap` is
`S.f ⊗_O G`. -/
lemma cmp_τ₃ (π : G' ⟶ G) :
    (cmp R (S := S) π).τ₃ ≫ (kernel.ι (vmap R (S := S) π)).τ₃ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).map S.f).app
        (ShortComplex.kernelSequence π).X₃ := by
  rw [← ShortComplex.comp_τ₃, cmp_comp_kernelι, ShortComplex.mapNatTrans_τ₃]

/-- The comparison map `cmp` is an epimorphism in degree one. -/
lemma epi_cmp_τ₁ (hS : S.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) S.X₃)
    (π : G' ⟶ G) [Epi π] : Epi (cmp R (S := S) π).τ₁ :=
  epi_of_exact_of_mono_fac
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).map S.f).app
      (ShortComplex.kernelSequence π).X₁)
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).map S.g).app
      (ShortComplex.kernelSequence π).X₁)
    (app_comp_app_zero R (S := S) _) (exact_row R hS _)
    ((kernel.ι (vmap R (S := S) π)).τ₁) (mono_kernelι_vmap_τ₁ R hflat π)
    (kernelι_vmap_comp_τ₁ R hflat π)
    (cmp R (S := S) π).τ₁ (cmp_τ₁ R π)

/-- If `G'` is flat, the comparison map `cmp` is a monomorphism in degree two. -/
lemma mono_cmp_τ₂ (hS : S.ShortExact) (π : G' ⟶ G)
    (hG'flat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R)
      (ShortComplex.kernelSequence π).X₂) :
    Mono (cmp R (S := S) π).τ₂ :=
  mono_of_fac _ _ _ (cmp_τ₂ R π) (mono_row_f_of_isFlat R hS _ hG'flat)

/-- The morphism `S.X₁ ⊗_O G' ⟶ S.X₁ ⊗_O G` induced by `π` is an epimorphism. -/
lemma epi_map_tensor_X₁_g (π : G' ⟶ G) [Epi π] :
    Epi ((ShortComplex.kernelSequence π).map
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj S.X₁)).g :=
  (exact_and_epi_map_of_shortExact
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj S.X₁)
      (shortExact_kernelSequence R π)).2

/-- If `G'` is flat, the comparison map `cmp` is a monomorphism in degree three. -/
lemma mono_cmp_τ₃ (hS : S.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) S.X₃)
    (π : G' ⟶ G) [Epi π]
    (hG'flat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R)
      (ShortComplex.kernelSequence π).X₂) :
    Mono (cmp R (S := S) π).τ₃ :=
  ShortComplex.mono_of_epi_of_epi_of_mono (cmp R (S := S) π)
    (exact_kernel_vmap R hflat π) (epi_map_tensor_X₁_g R π)
    (epi_cmp_τ₁ R hS hflat π) (mono_cmp_τ₂ R hS π hG'flat)

/-- If `S` is short exact and `S.X₃` is flat, then `S.f ⊗_O G` is a monomorphism for every sheaf
of modules `G`. -/
theorem mono_app_map_f (hS : S.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) S.X₃)
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) :
    Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).map S.f).app G) := by
  obtain ⟨G', π, hG'flat, hπ⟩ := exists_epi_from_flat R G
  have _ := hπ
  have hfin : Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).map S.f).app
      (ShortComplex.kernelSequence π).X₃) := by
    rw [← cmp_τ₃ R π]
    exact mono_comp' _ _ (mono_cmp_τ₃ R hS hflat π hG'flat) (mono_kernelι_vmap_τ₃ R hflat π)
  exact hfin

/-- If `S` is short exact and `S.X₃` is flat, then `S ⊗_O G` is short exact for every sheaf of
modules `G`. -/
theorem shortExact_map_sheafTensor_flip (hS : S.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) S.X₃)
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) :
    (S.map
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.obj G)).ShortExact := by
  obtain ⟨hGexact, hGepi⟩ := exact_and_epi_map_of_shortExact
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.obj G) hS
  exact ShortComplex.ShortExact.mk' hGexact (mono_app_map_f R hS hflat G) hGepi

/-! ### Short exactness of the tensored sequence -/

/-- If the final term of a short exact sequence of sheaves of modules on a small site is flat,
tensoring the sequence with any sheaf of modules gives a short exact sequence of sheaves. -/
theorem sheafTensorRight_shortExact_of_flat (hS : S.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) S.X₃)
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) :
    ∃ h : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.obj G)).map S.f ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.obj G)).map S.g = 0,
      (ShortComplex.mk
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.obj G)).map S.f)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.obj G)).map S.g)
        h).ShortExact :=
  ⟨(S.map ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.obj G)).zero,
    shortExact_map_sheafTensor_flip R hS hflat G⟩

end Main

end Stacks.SheafOfModules.FlatTensorShortExact
