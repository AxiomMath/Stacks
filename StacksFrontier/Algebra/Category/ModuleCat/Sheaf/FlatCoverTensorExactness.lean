module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ObjectwiseFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-! # Flat covers of sheaves of modules, and Stacks 03EX (2) with the site universes free

Let `(C, J)` be a site and `O` a sheaf of commutative rings on it, with the universe of the
sections of `O` independent of the two universes of the site. This file proves Stacks 03EX
part (2) in that generality: if `0 → F'' → F' → F → 0` is a short exact sequence of
`O`-modules whose third term `F` is flat, then tensoring with any `O`-module `G` keeps the
sequence short exact.

The proof is the one in the source, and it is the same proof as that of
`Stacks.SheafOfModules.FlatTensorShortExact.sheafTensorRight_shortExact_of_flat`: pick a flat
`G'` with an epimorphism onto `G`,
let `G''` be its kernel, and feed the three rows `(-) ⊗ G''`, `(-) ⊗ G'`, `(-) ⊗ G` of the
resulting diagram to the snake lemma. What is new here is twofold.

* The **flat cover** of `G` is produced differently, and that is what frees the universes. The
  proof there gets it from Stacks 03EW (3) in the shape of a direct sum of extensions by zero
  of structure sheaves of slices, which is available only for a site whose objects, morphisms
  and sections share one universe, because the comparison of the two descriptions of an
  extension by zero (Stacks 03EJ) is. Here the flat cover is instead the sheafification of the
  *free* presheaf of modules on the presheaf of sets of sections of `G`: its sections are free
  modules, hence flat, so it is a flat presheaf of modules by Stacks 03ES, and the
  sheafification of a flat presheaf of modules is a flat sheaf of modules by Stacks 03ET —
  both of which are available with all universes independent.
* The three rows are tensored on the **right** by the coefficient, which is the order in which
  flatness of a sheaf of modules is defined (Stacks 03ER (3)), so the middle row is short exact
  by the definition of flatness and no braiding is needed there. The braiding is needed
  instead for the vanishing of the third term of the kernel row, where `exactness of (-) ⊗ F`
  has to be read as left exactness of `F ⊗ (-)`.

## Main definitions

* `Stacks.SheafOfModules.FlatCover.freeCover` and
  `Stacks.SheafOfModules.FlatCover.freeCoverπ`: the free presheaf of modules on the sections of
  a sheaf of modules, and the canonical morphism from it.
* `Stacks.SheafOfModules.FlatCover.valPresheaf`: the underlying presheaf of modules of a sheaf
  of modules, at the reducible spelling of the ring presheaf.

## Main results

* `Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat`: Stacks 03EW (3) in the form its
  clients want — every sheaf of modules receives an epimorphism from a flat one — with the
  module, ring and site universes independent except that the module universe equals the ring
  universe.
* `Stacks.SheafOfModules.FlatCover.shortExact_map_sheafTensorFlipObj`: Stacks 03EX (2) for the
  tensor bifunctor of Stacks 06YM, with the coefficient as the right tensor factor.
* `Stacks.SheafOfModules.FlatCover.sheafTensorRight_shortExact_of_isFlat_X₃`: the same
  statement with the composite-is-zero witness carried explicitly, so that no
  zero-morphism-preservation hypothesis appears in the statement.

## Implementation notes

The module universe is equal to the universe of the sections of the structure sheaf. That is
forced, not chosen: the flat cover is a free module on the set of sections of `G`, and the
carrier of a free module on a set in `Type z` over a ring in `Type w` lies in
`Type (max w z)`. So no flat object of `SheafOfModules.{z}` can surject onto a general
`G` when `z` is strictly below `w` — indeed the structure sheaf itself is then not an object
of that category — and the source's argument has no purchase there.

All sheaf-level constructions use the canonical coefficient sheaf
`Stacks.SheafOfModules.Tensor.ringSheaf O`. Its underlying presheaf is
`O.obj ⋙ forget₂ CommRingCat RingCat`, which is also the `ringPresheaf O.obj` used by the
presheaf-level free-module construction. No comparison of coefficient sheaves is required.
The local sheaf-composition instance keeps the site universes independent of the sections
universe when applying the flatness interface.

Preservation of zero morphisms by the two tensor functors is read off their preservation of
finite colimits — a functor preserving the initial object preserves zero morphisms — rather than
proved by hand on pure tensors. That is shorter than a computation on sections.

## References

* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 03ES](https://stacks.math.columbia.edu/tag/03ES)
* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 05NJ](https://stacks.math.columbia.edu/tag/05NJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace Stacks.SheafOfModules.FlatCover

open AlgebraicGeometry.SheafOfModules (ringPresheaf)

section Free

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (O : Sheaf J CommRingCat.{w})

/-- The presheaf of modules underlying a sheaf of modules, spelled over `ringPresheaf O.obj`
rather than over `(Stacks.SheafOfModules.Tensor.ringSheaf O).obj`. -/
abbrev valPresheaf (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    PresheafOfModules.{w} (ringPresheaf O.obj) := M.val

/-- The free presheaf of `O`-modules on the presheaf of sets of sections of `M`. -/
def freeCover (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    PresheafOfModules.{w} (ringPresheaf O.obj) :=
  PresheafOfModules.freeObj ((valPresheaf O M).presheaf ⋙ forget AddCommGrpCat)

/-- The canonical morphism from the free presheaf of modules on the sections of `M` to `M`,
sending the generator indexed by a section to that section. -/
def freeCoverπ (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    freeCover O M ⟶ valPresheaf O M :=
  PresheafOfModules.freeObjDesc (𝟙 _)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Every section of `M` is in the image of `freeCoverπ`, being the image of the generator it
indexes. -/
lemma freeCoverπ_surjective (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (U : Cᵒᵖ) : Function.Surjective ((freeCoverπ O M).app U) :=
  fun x => ⟨ModuleCat.freeMk x, ModuleCat.freeDesc_apply _ x⟩

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The free presheaf of modules on the sections of `M` is a flat presheaf of modules: its
sections are free modules, hence flat, and objectwise flatness suffices (Stacks 03ES). -/
lemma freeCover_isFlat (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    AlgebraicGeometry.SheafOfModules.PresheafOfModules.IsFlat (O := O.obj) (freeCover O M) :=
  AlgebraicGeometry.SheafOfModules.PresheafOfModules.isFlat_of_objectwise_flat _ fun U =>
    inferInstanceAs (Module.Flat (O.obj.obj U)
      (((valPresheaf O M).presheaf ⋙ forget AddCommGrpCat).obj U →₀ O.obj.obj U))

end Free

section FlatCover

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (O : Sheaf J CommRingCat.{w})

/-- **Stacks 03EW (3) in flat form.** Every sheaf of modules receives an epimorphism from a
*flat* sheaf of modules, namely from the sheafification of the free presheaf of modules on its
presheaf of sets of sections. -/
theorem exists_epi_from_isFlat (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    ∃ (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (p : N ⟶ M),
      AlgebraicGeometry.SheafOfModules.IsFlat (O := O) N ∧ Epi p := by
  let a : ringPresheaf O.obj ⟶ (Stacks.SheafOfModules.Tensor.ringSheaf O).obj := 𝟙 _
  have hli : Presheaf.IsLocallyInjective J a :=
    Presheaf.isLocallyInjective_of_injective J a fun _ _ _ h => h
  have hls : Presheaf.IsLocallySurjective J a :=
    Presheaf.isLocallySurjective_of_surjective J a fun _ x => ⟨x, rfl⟩
  have hepi : Epi (freeCoverπ O M) :=
    PresheafOfModules.epi_of_surjective (f := freeCoverπ O M)
      (fun {U} => freeCoverπ_surjective O M U)
  have hiso : IsIso ((PresheafOfModules.sheafificationAdjunction a).counit.app M) :=
    NatIso.isIso_app_of_isIso _ M
  have h1 : Epi ((PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O) a).map (freeCoverπ O M)) :=
    Functor.map_epi _ _
  have h2 : Epi ((PresheafOfModules.sheafificationAdjunction a).counit.app M) :=
    @IsIso.epi_of_iso _ _ _ _ _ hiso
  -- The two morphisms are given opaque names: the middle object of the composite has two
  -- spellings, `valPresheaf O M` and `(restrictScalars a).obj M.val`, and instance search
  -- finds neither `Epi` hypothesis once the composite is formed with both of them in play.
  obtain ⟨p1, hp1⟩ : ∃ p1 : (PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O) a).obj (freeCover O M) ⟶
      (PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O) a).obj
        (valPresheaf O M), Epi p1 := ⟨_, h1⟩
  obtain ⟨p2, hp2⟩ : ∃ p2 : (PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O) a).obj (valPresheaf O M) ⟶ M, Epi p2 :=
    ⟨_, h2⟩
  refine ⟨(PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O) a).obj
      (freeCover O M), p1 ≫ p2, ?_, ?_⟩
  · exact Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification J
      (O := O.obj) (Osharp := O) a (F := freeCover O M) (freeCover_isFlat O M)
  · exact epi_comp _ _

end FlatCover

section Snake

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

-- The objectwise tensor product `tensorObj` and its restriction map `tensorMap` are
-- semireducible, so the comparison of the tensor bifunctor of Tag 06YM with the tensor functors
-- of Tag 03ER does not go through at instance transparency; they are made reducible locally, as
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/FlatnessAndRightExactness.lean`
-- does for the same comparison.
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.sheafTensor
  PresheafOfModules.tensorBifunctor
  AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj
  AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorMap

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (O : Sheaf J CommRingCat.{w})

/-- Tensoring on the left with a fixed sheaf of modules preserves zero morphisms, being right
exact. -/
local instance preservesZeroMorphisms_tensorObj
    (Y : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor O).obj Y).PreservesZeroMorphisms := by
  have := preservesFiniteColimits_sheafTensorObj O Y
  infer_instance

/-- Tensoring on the right with a fixed sheaf of modules preserves zero morphisms, being right
exact. -/
local instance preservesZeroMorphisms_tensorFlipObj
    (Y : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj Y).PreservesZeroMorphisms := by
  have := preservesFiniteColimits_sheafTensorFlipObj O Y
  infer_instance

/-- The tensor bifunctor is zero-morphism-preserving in the right variable: a zero morphism of
coefficients induces the zero natural transformation of tensor functors. -/
local instance preservesZeroMorphisms_tensorFlip :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip).PreservesZeroMorphisms where
  map_zero X Y := by
    refine NatTrans.ext ?_
    funext Z
    exact ((Stacks.SheafOfModules.Tensor.sheafTensor O).obj Z).map_zero X Y

/-- Tensoring on the right with a fixed `Y` sends two maps of coefficients with zero composite
to maps with zero composite. -/
private lemma sheafTensorFlip_map_app_comp_eq_zero
    {A B D : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {q : A ⟶ B} {r : B ⟶ D} (h : q ≫ r = 0)
    (Y : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.map q).app Y ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.map r).app Y = 0 := by
  rw [← NatTrans.comp_app, ← Functor.map_comp, h, Functor.map_zero, zero_app]

variable (S : ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)))

/-- Tensoring a short exact sequence on the right with `Y` gives an exact sequence whose last
map is an epimorphism, because `(-) ⊗ Y` is right exact. -/
private lemma exact_and_epi_map_sheafTensorFlipObj (hS : S.ShortExact)
    (Y : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (S.map ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj Y)).Exact ∧
      Epi (((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj Y).map S.g) := by
  have := preservesFiniteColimits_sheafTensorFlipObj O Y
  have := hS.epi_g
  exact ⟨hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance,
    preserves_epi_of_preservesColimit _ S.g⟩

/-- The comparison between two rows of the snake diagram, induced by a map of the sheaves one
tensors with. -/
private def tensorRowMap
    {A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (q : A ⟶ B) :
    S.map ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj A) ⟶
      S.map ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj B) :=
  S.mapNatTrans ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.map q)

/-- Two consecutive comparisons of rows compose to zero when the two maps of coefficients do. -/
private lemma tensorRowMap_comp
    {A B D : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (q : A ⟶ B) (r : B ⟶ D) (h : q ≫ r = 0) :
    tensorRowMap O S q ≫ tensorRowMap O S r = 0 := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_ <;>
    simpa only [tensorRowMap, ShortComplex.comp_τ₁, ShortComplex.comp_τ₂, ShortComplex.comp_τ₃,
      ShortComplex.mapNatTrans_τ₁, ShortComplex.mapNatTrans_τ₂, ShortComplex.mapNatTrans_τ₃,
      ShortComplex.zero_τ₁, ShortComplex.zero_τ₂, ShortComplex.zero_τ₃] using
      sheafTensorFlip_map_app_comp_eq_zero O h _

variable {M M' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (p : M' ⟶ M)

/-- Each column of the snake diagram is a cokernel presentation, because tensoring is right
exact in the coefficient variable. -/
private noncomputable def isColimit_tensorColumn (hp : Epi p)
    (Y : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    IsColimit (CokernelCofork.ofπ (((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.map p).app Y)
      (sheafTensorFlip_map_app_comp_eq_zero O (kernel.condition p) Y)) := by
  have hker : (ShortComplex.kernelSequence p).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact p) inferInstance hp
  have := preservesFiniteColimits_sheafTensorObj O Y
  exact CokernelCofork.mapIsColimit _ hker.gIsCokernel
    ((Stacks.SheafOfModules.Tensor.sheafTensor O).obj Y)

/-- The snake diagram of the source's proof: the rows are the sequence tensored with the kernel
of `p`, with its source, and with its target. -/
private noncomputable def tensorSnakeInput (hS : S.ShortExact) (hp : Epi p)
    (hM'flat : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) M') :
    ShortComplex.SnakeInput
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) := by
  have hT'ex : exactFunctor _ _ ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj M') :=
    exactFunctor_sheafTensorFlip_of_isFlat O M' hM'flat
  have hT'lim := ((exactFunctor_iff _).1 hT'ex).1
  have hT'col := ((exactFunctor_iff _).1 hT'ex).2
  have hcolK := preservesFiniteColimits_sheafTensorFlipObj O (kernel p)
  exact
    { L₀ := kernel (tensorRowMap O S (kernel.ι p))
      L₁ := S.map ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj (kernel p))
      L₂ := S.map ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj M')
      L₃ := S.map ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj M)
      v₀₁ := kernel.ι (tensorRowMap O S (kernel.ι p))
      v₁₂ := tensorRowMap O S (kernel.ι p)
      v₂₃ := tensorRowMap O S p
      w₀₂ := kernel.condition _
      w₁₃ := tensorRowMap_comp O S (kernel.ι p) p (kernel.condition p)
      h₀ := kernelIsKernel _
      h₃ := by
        refine ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ ShortComplex.π₁).symm
            (isColimit_tensorColumn O p hp S.X₁)
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ ShortComplex.π₂).symm
            (isColimit_tensorColumn O p hp S.X₂)
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ ShortComplex.π₃).symm
            (isColimit_tensorColumn O p hp S.X₃)
      L₁_exact := (exact_and_epi_map_sheafTensorFlipObj O S hS (kernel p)).1
      epi_L₁_g := (exact_and_epi_map_sheafTensorFlipObj O S hS (kernel p)).2
      L₂_exact := (hS.map_of_exact ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj M')).exact
      mono_L₂_f := (hS.map_of_exact ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj
        M')).mono_f }

/-- The third term of the kernel row of `tensorSnakeInput` vanishes, because `S.X₃ ⊗ -` is exact
when `S.X₃` is flat and `kernel.ι p` is a monomorphism. -/
private lemma isZero_tensorSnakeInput_L₀_X₃ (hS : S.ShortExact) (hp : Epi p)
    (hM'flat : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) M')
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) S.X₃) :
    IsZero (tensorSnakeInput O S p hS hp hM'flat).L₀.X₃ := by
  have hex : exactFunctor _ _ ((Stacks.SheafOfModules.Tensor.sheafTensor O).obj S.X₃) :=
    exact_sheafTensorObj_of_isFlat O hflat
  have : PreservesFiniteLimits ((Stacks.SheafOfModules.Tensor.sheafTensor O).obj S.X₃) :=
    ((exactFunctor_iff _).1 hex).1
  have hmono₃ : Mono (ShortComplex.π₃.map (tensorRowMap O S (kernel.ι p))) :=
    preserves_mono_of_preservesLimit ((Stacks.SheafOfModules.Tensor.sheafTensor O).obj S.X₃)
      (kernel.ι p)
  exact KernelFork.IsLimit.isZero_of_mono
    (KernelFork.mapIsLimit _ (kernelIsKernel (tensorRowMap O S (kernel.ι p)))
      ShortComplex.π₃)

/-- **Stacks 03EX, part (2)** for the tensor bifunctor of Tag 06YM, the coefficient being the
right tensor factor: tensoring a short exact sequence of sheaves of modules whose third term is
flat with any sheaf of modules gives a short exact sequence. -/
theorem shortExact_map_sheafTensorFlipObj (hS : S.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) S.X₃)
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (S.map ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj G)).ShortExact := by
  classical
  obtain ⟨G', q, hG'flat, hq⟩ := exists_epi_from_isFlat O G
  obtain ⟨hexT, hepiT⟩ := exact_and_epi_map_sheafTensorFlipObj O S hS G
  have hmono : Mono (S.map ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj G)).f :=
    (ShortComplex.exact_iff_mono _
        ((isZero_tensorSnakeInput_L₀_X₃ O S q hS hq hG'flat hflat).eq_of_src _ _)).1
      (tensorSnakeInput O S q hS hq hG'flat).L₂'_exact
  exact ShortComplex.ShortExact.mk' hexT hmono hepiT

end Snake

section TensorExactness

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Stacks Project, Tag 03EX, sheaf case.** If the final term of a short exact sequence of
sheaves of modules is flat, tensoring the sequence with any sheaf of modules gives a short exact
sequence.

This is `shortExact_map_sheafTensorFlipObj` with the composite-is-zero witness carried
explicitly, so that the statement does not mention the zero-morphism-preservation instance of
the tensor functor.

Taking the site to be the site of opens of a topological space and `O` its structure sheaf,
this is **Stacks Tag 05NJ**: a short exact sequence `0 → ℱ'' → ℱ' → ℱ → 0` of `𝒪_X`-modules on
a ringed space with `ℱ` flat stays short exact after `- ⊗_{𝒪_X} 𝒢`. -/
@[stacks 05NJ "ringed spaces, as the special case of a general site"]
theorem sheafTensorRight_shortExact_of_isFlat_X₃
    (O : Sheaf J CommRingCat.{w})
    (S : ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hS : S.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) S.X₃) :
    ∃ h : ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj G).map S.f ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj G).map S.g = 0,
      (ShortComplex.mk (((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj G).map S.f)
        (((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj G).map S.g) h).ShortExact :=
  ⟨_, shortExact_map_sheafTensorFlipObj O S hS hflat G⟩

end TensorExactness

end Stacks.SheafOfModules.FlatCover

end
