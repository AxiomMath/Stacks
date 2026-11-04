module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatTwoOutOfThree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafFlatCover
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatResolution.PresheafFlatQuotient
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorColimits
public import StacksFrontier.Homology.CyclesShortComplex
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Tensoring by a flat presheaf or sheaf of modules

Let `(C, O)` be a ringed site.  Tensoring a short exact sequence of presheaves of `O`-modules
whose third term is flat with an arbitrary presheaf of `O`-modules leaves it short exact; and if

`… ⟶ F₂ ⟶ F₁ ⟶ F₀ ⟶ Q ⟶ 0`

is an exact complex of presheaves, respectively sheaves, of `O`-modules in which `Q` and every
`Fᵢ` is flat, then tensoring it with an arbitrary presheaf, respectively sheaf, of `O`-modules
leaves it exact.

The displayed complex is an `ℕ`-indexed chain complex with `Q` in degree `0` and `Fᵢ` in degree
`i + 1`; its exactness is `HomologicalComplex.Acyclic`, which in degree `0` is surjectivity of
`F₀ ⟶ Q`.  The hypothesis that `Q` and every `Fᵢ` is flat is then simply that every term of the
complex is flat.

## Main results

* `Stacks.SheafOfModules.FlatResolution.Presheaf.shortExact_map_tensorRight`: the short exact
  sequence statement for presheaves of modules, on an arbitrary category and over a presheaf of
  commutative rings.
* `Stacks.SheafOfModules.FlatResolution.Presheaf.acyclic_map_tensorRight_of_isFlat`: the
  resolution statement for presheaves of modules.
* `Stacks.SheafOfModules.FlatResolution.acyclic_map_sheafTensorRight_of_isFlat`: the resolution
  statement for sheaves of modules.

## Implementation notes

The short exact sequence statement for presheaves is the source's argument, with no site in
sight.  Right exactness of the objectwise tensor product in each variable already gives
exactness in the middle and an epimorphism on the right, so the content is injectivity on the
left; and that is the diagram chase `Stacks.mono_of_threeByThree` applied to the 3-by-3 diagram
obtained by resolving the second tensor factor `G` by a flat presheaf of modules, which is
Stacks 03EW part (2) in the form
`Stacks.SheafOfModules.FlatResolution.exists_epi_from_flat_presheaf`.  Right exactness in the
*second* variable is right exactness in the first one transported along the symmetry of the
tensor product, `AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorLeftIsoTensorRight`,
and so is left exactness of tensoring with the flat third term; the symmetry is used only
through that pair of transports and through the one lemma
`tensorLeft_map_comp_tensorRight_map` that commutes the two variables.

`Stacks.SheafOfModules.FlatTwoOutOfThree.Presheaf.shortExact_map_tensorRight` is the same
statement for a small site with all four universes equal, obtained instead by transporting the
sheaf case along the trivial topology; it is what the presheaf case of Stacks 03EY is proved
from, and it cannot be replaced by the statement here because
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatTwoOutOfThree.lean` is imported by this file
and not the other way round.

Neither resolution proof touches the tensor product.  Both are instances of
`ChainComplex.acyclic_mapHomologicalComplex_of_prop`, which needs exactly two facts about
flatness, and both are already available: two out of three for flatness of Stacks 03EY part
(2) says that the class of flat modules contains the first term of a short exact sequence whose
other two terms are flat, so all the cycles of the complex are flat; and Stacks 03EX says that
tensoring keeps a short exact sequence with flat third term short exact, so the cycles
sequences of the complex stay short exact after tensoring.

**Universes.** The presheaf short exact sequence statement leaves the object universe `u`, the
morphism universe `v` and the universe `w` of the sections of `O` independent, and its module
universe is `max u v w z` with `z` free.  The inequality `max u v ≤ max u v w z` is forced and
`max u v w z` is its general solution: what forces it is the flat cover, a direct sum indexed by
all pairs `(U, s)` with `s` a section of the module over `U`, which is an object of
`PresheafOfModules.{z'}` only when `max u v w ≤ z'`.

The sheaf resolution statement leaves `u`, `v` and `w` independent, the module universe being
`w`.  That is inherited from the inputs rather than chosen: Stacks 03EX is available at those
universes as `Stacks.SheafOfModules.FlatCover.sheafTensorRight_shortExact_of_isFlat_X₃`, and
Stacks 03EY as `Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_left_of_shortExact`; the module
universe is forced equal to `w` by that form of 03EX, whose flat covers are free modules on the
sections of the object they cover.

The presheaf resolution statement still pins a small site with all universes equal, again
inherited: the presheaf case of Stacks 03EY is deduced in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatTwoOutOfThree.lean` from the sheaf case for
the trivial topology, and that deduction needs sheafification for `⊥`, which Mathlib supplies
only for a small site.

## References

* [Stacks Project, Tag 03EZ](https://stacks.math.columbia.edu/tag/03EZ)
* [Stacks Project, Tag 03EP](https://stacks.math.columbia.edu/tag/03EP)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
* [Stacks Project, Tag 03EY](https://stacks.math.columbia.edu/tag/03EY)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w z

namespace Stacks.SheafOfModules.FlatResolution

/-! ### Sheaves of modules -/

section Sheaf

-- The sections universe `w` is independent of the two site universes, so Mathlib's
-- size-restricted instances do not supply the sheaf-condition composition through which
-- `Stacks.SheafOfModules.Tensor.ringSheaf` and `IsFlat` are stated.
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

-- `Functor.mapHomologicalComplex` asks for preservation of zero morphisms already in the
-- statement, and the additivity of `sheafTensorRight` that instance search uses for it is
-- available only when the module universe dominates the site.
attribute [local instance]
  Stacks.SheafOfModules.FlatSheafification.sheafTensorRight_preservesZeroMorphisms

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})

/-- **Stacks 03EZ, sheaf case.** An exact `ℕ`-indexed complex of sheaves of modules all of
whose terms are flat stays exact after tensoring with an arbitrary sheaf of modules.

This is also **Stacks 05NL**, the same statement for a ringed space: a ringed space is the
ringed site of its lattice of opens, its `O_X`-modules are the sheaves of modules over the
structure ring sheaf of that site, and the tensor product is `sheafTensorRight`.  The
site-level statement is recorded against the ringed-space tag for the same reason that the
site-level flatness of Stacks 03ER(3) is recorded against Stacks 05ND in
`StacksFrontier/CategoryTheory/Sites/Modules/Flat.lean`. -/
@[stacks 03EZ "sheaves",
  stacks 05NL "ringed spaces, as the special case of a general site",
  ega "IV 2.1.10" "Absolute case f = id"]
theorem acyclic_map_sheafTensorRight_of_isFlat
    (K : ChainComplex
      (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℕ)
    (hK : K.Acyclic)
    (hflat : ∀ i, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) (K.X i))
    (G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    ((Functor.mapHomologicalComplex
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).flip.obj G)
      (ComplexShape.down ℕ)).obj K).Acyclic :=
  ChainComplex.acyclic_mapHomologicalComplex_of_prop
    (fun M ↦ AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) M)
    (fun S hS h₂ h₃ ↦ FlatTwoOutOfThree.isFlat_left_of_shortExact R S hS h₂ h₃)
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).flip.obj G))
    (fun S hS h₃ ↦
      (FlatCover.sheafTensorRight_shortExact_of_isFlat_X₃ R S G hS h₃).choose_spec)
    K hK hflat

end Sheaf

/-! ### Presheaves of modules -/

namespace Presheaf

open AlgebraicGeometry.SheafOfModules

section TensorShortExact

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- Tensoring presheaves of modules on the left by a fixed one is right exact, being
objectwise a left adjoint. -/
instance preservesFiniteColimits_tensorLeft
    (F : _root_.PresheafOfModules.{z} (ringPresheaf O)) :
    PreservesFiniteColimits (PresheafOfModules.tensorLeft F) :=
  @PreservesColimitsOfSize.preservesFiniteColimits _ _ _ _ (PresheafOfModules.tensorLeft F)
    (PresheafOfModules.tensorLeft_preservesColimits.{u, v, w, z, z} F)

/-- Tensoring presheaves of modules on the right by a fixed one is right exact: it is
tensoring on the left, read through the symmetry of the tensor product. -/
@[sga "4 IV 12.9" "special case"]
instance preservesFiniteColimits_tensorRight
    (F : _root_.PresheafOfModules.{z} (ringPresheaf O)) :
    PreservesFiniteColimits (PresheafOfModules.tensorRight F :
      _root_.PresheafOfModules.{z} (ringPresheaf O) ⥤ _) :=
  preservesFiniteColimits_of_natIso (PresheafOfModules.tensorLeftIsoTensorRight F)

/-- A right exact functor between abelian categories is additive. -/
instance additive_tensorRight (F : _root_.PresheafOfModules.{z} (ringPresheaf O)) :
    (PresheafOfModules.tensorRight F :
      _root_.PresheafOfModules.{z} (ringPresheaf O) ⥤ _).Additive :=
  (additiveFunctor_iff _).1 (rightExactFunctor_le_additiveFunctor _ _ _
    ((rightExactFunctor_iff _).2 inferInstance))

/-- A right exact functor between abelian categories is additive. -/
instance additive_tensorLeft (F : _root_.PresheafOfModules.{z} (ringPresheaf O)) :
    (PresheafOfModules.tensorLeft F).Additive :=
  (additiveFunctor_iff _).1 (rightExactFunctor_le_additiveFunctor _ _ _
    ((rightExactFunctor_iff _).2 inferInstance))

/-- Tensoring in the first variable and tensoring in the second variable commute: both
composites send a pure tensor `x ⊗ y` to `φ x ⊗ α y`. -/
lemma tensorLeft_map_comp_tensorRight_map
    {M M' : _root_.PresheafOfModules.{z} (ringPresheaf O)} (φ : M ⟶ M')
    {N N' : _root_.PresheafOfModules.{z} (ringPresheaf O)} (α : N ⟶ N') :
    (PresheafOfModules.tensorLeft M).map α ≫ (PresheafOfModules.tensorRight N').map φ =
      (PresheafOfModules.tensorRight N).map φ ≫ (PresheafOfModules.tensorLeft M').map α := by
  apply _root_.PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  rfl

/-- A right exact functor between abelian categories preserves exactness and epimorphisms of a
short exact sequence. -/
private theorem exact_and_epi_map {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F] {T : ShortComplex A} (hT : T.ShortExact) :
    (T.map F).Exact ∧ Epi (F.map T.g) :=
  (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi (F := F)).1 inferInstance T hT

/-- A left exact functor between abelian categories preserves the monomorphism of a short exact
sequence. -/
private theorem mono_map_f {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] {T : ShortComplex A} (hT : T.ShortExact) :
    Mono (F.map T.f) :=
  ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono (F := F)).1 inferInstance T hT).2

/-- **Stacks 03EX, part (1).** If the third term of a short exact sequence of presheaves of
modules is flat, then tensoring the sequence with an arbitrary presheaf of modules gives a
short exact sequence.

The proof is the source's.  Right exactness of the objectwise tensor product gives exactness in
the middle and an epimorphism on the right, so the content is injectivity on the left.  For
that, resolve the second tensor factor `G` by a flat presheaf of modules `P` (Stacks 03EW part
(2)), let `K` be the kernel of `P ⟶ G`, and chase the 3-by-3 diagram whose columns are the
sequence tensored with `K`, `P` and `G` and whose rows are `K ⟶ P ⟶ G` tensored with the three
terms of the sequence: the first column and the second row are exact because tensoring is right
exact in each variable, the second column is left exact because `P` is flat, and the bottom row
is left exact because the third term of the sequence is flat. -/
@[stacks 03EX "part (1)",
  ega "IV 2.1.10" "special case",
  sga "1 IV 1.1" "more general",
  sga "4 XVII 4.1.1" "(ii), special case"]
theorem shortExact_map_tensorRight
    {S : ShortComplex (_root_.PresheafOfModules.{max u v w z} (ringPresheaf O))}
    (hS : S.ShortExact) (h₃ : PresheafOfModules.IsFlat S.X₃)
    (G : _root_.PresheafOfModules.{max u v w z} (ringPresheaf O)) :
    (S.map (PresheafOfModules.tensorRight G)).ShortExact := by
  obtain ⟨P, hP, p, hp⟩ := exists_epi_from_flat_presheaf.{v, u, w, z} O G
  have := hp
  let E : ShortComplex (_root_.PresheafOfModules.{max u v w z} (ringPresheaf O)) :=
    ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  have hE : E.ShortExact := ⟨ShortComplex.exact_kernel p⟩
  have hcol := fun N => exact_and_epi_map (PresheafOfModules.tensorRight N) hS
  have hrow := fun M => exact_and_epi_map (PresheafOfModules.tensorLeft M) hE
  have : Epi (E.map (PresheafOfModules.tensorLeft S.X₁)).g := (hrow S.X₁).2
  have : PreservesFiniteLimits (PresheafOfModules.tensorRight E.X₂ :
      _root_.PresheafOfModules.{max u v w z} (ringPresheaf O) ⥤ _) := hP.1
  have : PreservesFiniteLimits (PresheafOfModules.tensorRight S.X₃ :
      _root_.PresheafOfModules.{max u v w z} (ringPresheaf O) ⥤ _) := h₃.1
  have : PreservesFiniteLimits (PresheafOfModules.tensorLeft S.X₃) :=
    preservesFiniteLimits_of_natIso (PresheafOfModules.tensorLeftIsoTensorRight S.X₃).symm
  have : Mono (S.map (PresheafOfModules.tensorRight E.X₂)).f :=
    mono_map_f (PresheafOfModules.tensorRight E.X₂) hS
  have : Mono ((PresheafOfModules.tensorLeft S.X₃).map E.f) :=
    mono_map_f (PresheafOfModules.tensorLeft S.X₃) hE
  have hmono : Mono ((PresheafOfModules.tensorRight E.X₃).map S.f) :=
    Stacks.mono_of_threeByThree
      (S.map (PresheafOfModules.tensorRight E.X₁)).zero (hcol E.X₁).1
      (E.map (PresheafOfModules.tensorLeft S.X₂)).zero (hrow S.X₂).1
      (E.map (PresheafOfModules.tensorLeft S.X₁)).zero
      (S.map (PresheafOfModules.tensorRight E.X₂)).zero
      (tensorLeft_map_comp_tensorRight_map S.f E.f)
      (tensorLeft_map_comp_tensorRight_map S.f E.g)
      (tensorLeft_map_comp_tensorRight_map S.g E.f)
  exact { exact := (hcol G).1, mono_f := hmono, epi_g := (hcol G).2 }

end TensorShortExact

variable {C : Type u} [SmallCategory.{u} C] {O : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- **Stacks 03EZ, presheaf case.** An exact `ℕ`-indexed complex of presheaves of modules all
of whose terms are flat stays exact after tensoring with an arbitrary presheaf of modules. -/
@[stacks 03EZ "presheaves", ega "IV 2.1.10" "special case"]
theorem acyclic_map_tensorRight_of_isFlat
    (K : ChainComplex (_root_.PresheafOfModules.{u} (ringPresheaf O)) ℕ)
    (hK : K.Acyclic)
    (hflat : ∀ i, PresheafOfModules.IsFlat (K.X i))
    (G : _root_.PresheafOfModules.{u} (ringPresheaf O)) :
    (((PresheafOfModules.tensorRight G).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj K).Acyclic := by
  let : (PresheafOfModules.tensorRight.{u, u, u, u, u} G).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  exact ChainComplex.acyclic_mapHomologicalComplex_of_prop
    (fun M ↦ PresheafOfModules.IsFlat M)
    (fun S hS h₂ h₃ ↦ FlatTwoOutOfThree.Presheaf.isFlat_left_of_shortExact S hS h₂ h₃)
    (PresheafOfModules.tensorRight G)
    (fun _ hS h₃ ↦ FlatTwoOutOfThree.Presheaf.shortExact_map_tensorRight hS h₃ G)
    K hK hflat

end Presheaf

end Stacks.SheafOfModules.FlatResolution

end

end
