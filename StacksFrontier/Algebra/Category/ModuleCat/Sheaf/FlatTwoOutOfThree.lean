module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverTensorExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatTensorShortExact
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Two out of three for flatness of presheaves and sheaves of modules

Let `(C, O)` be a ringed site and let `0 → F₂ → F₁ → F₀ → 0` be a short exact sequence of
presheaves, respectively sheaves, of `O`-modules.  If `F₂` and `F₀` are flat, so is `F₁`; and if
`F₁` and `F₀` are flat, so is `F₂`.

## Main results

* `Stacks.SheafOfModules.FlatTwoOutOfThree.Presheaf.isFlat_middle_of_shortExact`:
  **Tag 03EY, part (1) for presheaves.**
* `Stacks.SheafOfModules.FlatTwoOutOfThree.Presheaf.isFlat_left_of_shortExact`:
  **Tag 03EY, part (2) for presheaves.**
* `Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_middle_of_shortExact`:
  **Tag 03EY, part (1) for sheaves.**
* `Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_left_of_shortExact`:
  **Tag 03EY, part (2) for sheaves.**

Two results of independent interest are proved on the way:

* `Stacks.SheafOfModules.FlatTwoOutOfThree.Presheaf.shortExact_map_tensorRight` is Tag 03EX for
  *presheaves* of modules, obtained from the sheaf case for the trivial topology, on which
  sheafification is an equivalence.  It carries no tag: its clause belongs to Tag 03EX.
* `Stacks.SheafOfModules.FlatTwoOutOfThree.Presheaf.botEquiv` identifies presheaves and sheaves
  of modules for the trivial topology.

## Implementation notes

Flatness of `F` is exactness of `· ⊗_O F`.  Right exactness of a tensor functor is automatic
(from monoidal closedness for presheaves, from Tag 05NB in the form
`Stacks.SheafOfModules.preservesColimits_sheafTensorObj` for sheaves), so the whole content is
preservation of monomorphisms, and the source's appeal to the snake lemma is the four lemma
`ShortComplex.mono_of_mono_of_mono_of_mono` for part (1) and a single factorization for
part (2).

For a monomorphism `ι : A ⟶ B`, the two rows `Fᵢ ⊗ A` and `Fᵢ ⊗ B` are short exact by Tag 03EX
and the flatness of `F₀`, and the three vertical maps are `Fᵢ ⊗ ι`.  Part (1) reads off the
middle vertical map from the outer two; part (2) reads off the left one from the naturality
square of `F₂ ⊗ · ⟶ F₁ ⊗ ·` at `ι`, which exhibits `(F₂ ⊗ ι) ≫ (F₁ ⊗ ι)`-at-`B` as the
composite of a monomorphism by Tag 03EX with a monomorphism by the flatness of `F₁`.

Both arguments are carried out in the tensor order `F ⊗ ·`, which is the order in which Tag
03EX's short exactness is stated in the *other* variable, and transported to the order `· ⊗ F`
that the definition of flatness uses by a single braiding at the very end
(`Stacks.SheafOfModules.FlatTwoOutOfThree.Presheaf.flipIso`,
`Stacks.SheafOfModules.Tensor.sheafTensorBraiding`).  This keeps the symmetry of the tensor
product to a single use.

**Universes.** The sheaf statements leave the object universe `u`, the morphism universe `v`
and the universe `w` of the sections of the structure sheaf independent; the module universe is
`w`, which is forced by Tag 03EX and not chosen here (see
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatCoverTensorExactness.lean`: the flat cover of
a sheaf of modules is a free module on its sections, so it is an object of `SheafOfModules.{z}`
only when `w ≤ z`).  The 03EX input is
`Stacks.SheafOfModules.FlatCover.sheafTensorRight_shortExact_of_isFlat_X₃`, whose flat covers
are sheafified free presheaves of modules rather than direct sums of extensions by zero, and
which is therefore free of the small-site pin of
`Stacks.SheafOfModules.FlatTensorShortExact.sheafTensorRight_shortExact_of_flat`.

The presheaf statements still pin a small site with all four universes equal.  They are deduced
from the sheaf case for the trivial topology, and that route needs weak sheafification and local
bijectivity for `⊥`, which Mathlib's instances supply only for a small site; the pin is
therefore in the *deduction*, not in Tag 03EX.

## References

* [The Stacks Project, Tag 03EY](https://stacks.math.columbia.edu/tag/03EY)
* [The Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u w

namespace Stacks.SheafOfModules.FlatTwoOutOfThree

/-! ### Sheaves of modules -/

section Sheaf

-- The sections universe `w` is independent of the two site universes, so Mathlib's
-- size-restricted instances do not supply the sheaf-condition composition through which
-- `Stacks.SheafOfModules.Tensor.ringSheaf` and `IsFlat` are stated.
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})

/-- Four lemma for a bifunctor `T`: if `T(-, A)` and `T(-, B)` send `S` to short exact sequences
and `T(S.X₁, -)`, `T(S.X₃, -)` preserve the monomorphism `ι`, so does `T(S.X₂, -)`. -/
private theorem mono_map_obj_X₂_of_shortExact {D E : Type*} [Category D] [HasZeroMorphisms D]
    [Category E] [Abelian E]
    (T : D ⥤ D ⥤ E) (S : ShortComplex D) {A B : D} (ι : A ⟶ B) [Mono ι]
    [(T.flip.obj A).PreservesZeroMorphisms] [(T.flip.obj B).PreservesZeroMorphisms]
    [PreservesFiniteLimits (T.obj S.X₁)] [PreservesFiniteLimits (T.obj S.X₃)]
    (hA : (S.map (T.flip.obj A)).ShortExact) (hB : (S.map (T.flip.obj B)).ShortExact) :
    Mono ((T.obj S.X₂).map ι) :=
  ShortComplex.mono_of_mono_of_mono_of_mono
    { τ₁ := (T.obj S.X₁).map ι
      τ₂ := (T.obj S.X₂).map ι
      τ₃ := (T.obj S.X₃).map ι
      comm₁₂ := (T.map S.f).naturality ι
      comm₂₃ := (T.map S.g).naturality ι }
    hA.exact hB.mono_f inferInstance inferInstance

/-- If `T(f, A)` is a monomorphism and `T(Y, -)` preserves the monomorphism `ι`, then
`T(X, -)` preserves `ι` too, by the naturality square of `T(f, -)`. -/
private theorem mono_map_obj_of_mono_app {D E : Type*} [Category D] [Category E] [Abelian E]
    (T : D ⥤ D ⥤ E) {X Y A B : D} (f : X ⟶ Y) (ι : A ⟶ B) [Mono ι]
    [PreservesFiniteLimits (T.obj Y)] (hf : Mono ((T.map f).app A)) :
    Mono ((T.obj X).map ι) :=
  Stacks.SheafOfModules.FlatTensorShortExact.mono_of_fac _ ((T.map f).app B)
    ((T.map f).app A ≫ (T.obj Y).map ι) ((T.map f).naturality ι)
    (Stacks.SheafOfModules.FlatTensorShortExact.mono_comp' _ _ hf inferInstance)

/-- Tensoring on the left with a flat sheaf of modules preserves finite limits. -/
private lemma preservesFiniteLimits_sheafTensorObj
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) M) :
    PreservesFiniteLimits ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M) :=
  ((exactFunctor_iff _).1 (Stacks.SheafOfModules.exact_sheafTensorObj_of_isFlat R hM)).1

/-- Flatness of a sheaf of modules `M` from the one thing right exactness of `M ⊗ ·` leaves
open: that it preserves monomorphisms. -/
lemma isFlat_of_mono_sheafTensor_map
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    (hmono : ∀ {A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
      (ι : A ⟶ B), Mono ι →
        Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M).map ι)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) M := by
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M
  -- Right exactness of `M ⊗ ·` is Tag 05NB.
  let : PreservesFiniteColimits T := by
    have := Stacks.SheafOfModules.preservesColimits_sheafTensorObj R M
    exact PreservesColimitsOfSize.preservesFiniteColimits _
  let : T.PreservesZeroMorphisms := inferInstance
  let : T.PreservesMonomorphisms := { preserves := fun f ↦ hmono f inferInstance }
  let : PreservesColimitsOfShape WalkingParallelPair T :=
    PreservesFiniteColimits.preservesFiniteColimits WalkingParallelPair
  let : ∀ {A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)} (f : A ⟶ B),
      PreservesColimit (parallelPair f 0) T :=
    fun f ↦ PreservesColimitsOfShape.preservesColimit (F := T) (K := parallelPair f 0)
  let : T.PreservesHomology := Functor.preservesHomology_of_preservesMonos_and_cokernels T
  let : ∀ {A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)} (f : A ⟶ B),
      PreservesLimit (parallelPair f 0) T :=
    fun f ↦ Functor.PreservesHomology.preservesKernels (F := T) f
  have hobj : exactFunctor _ _ T :=
    (exactFunctor_iff T).2 ⟨T.preservesFiniteLimits_of_preservesKernels, inferInstance⟩
  exact Stacks.SheafOfModules.isFlat_of_exactFunctor_sheafTensorFlip R M
    ((exactFunctor _ _).prop_of_iso
      ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding R).app M) hobj)

/-- **Tag 03EY, part (1) for sheaves.** In a short exact sequence of sheaves of modules whose
outer terms are flat, the middle term is flat. -/
@[stacks 03EY "sheaves, part (1)"]
theorem isFlat_middle_of_shortExact
    (S : ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)))
    (hS : S.ShortExact)
    (h₁ : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) S.X₁)
    (h₃ : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) S.X₃) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) S.X₂ := by
  refine isFlat_of_mono_sheafTensor_map R S.X₂ ?_
  intro A B ι _
  have := preservesFiniteLimits_sheafTensorObj R S.X₁ h₁
  have := preservesFiniteLimits_sheafTensorObj R S.X₃ h₃
  exact mono_map_obj_X₂_of_shortExact
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) S ι
    (Stacks.SheafOfModules.FlatCover.shortExact_map_sheafTensorFlipObj R S hS h₃ A)
    (Stacks.SheafOfModules.FlatCover.shortExact_map_sheafTensorFlipObj R S hS h₃ B)

/-- **Tag 03EY, part (2) for sheaves.** In a short exact sequence of sheaves of modules whose
middle and right terms are flat, the left term is flat. -/
@[stacks 03EY "sheaves, part (2)", sga "4 XVII 4.1.1" "(i)"]
theorem isFlat_left_of_shortExact
    (S : ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)))
    (hS : S.ShortExact)
    (h₂ : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) S.X₂)
    (h₃ : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) S.X₃) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) S.X₁ := by
  refine isFlat_of_mono_sheafTensor_map R S.X₁ ?_
  intro A B ι _
  have := preservesFiniteLimits_sheafTensorObj R S.X₂ h₂
  exact mono_map_obj_of_mono_app
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) S.f ι
    (Stacks.SheafOfModules.FlatCover.shortExact_map_sheafTensorFlipObj R S hS h₃ A).mono_f

end Sheaf

/-! ### Presheaves of modules

The presheaf case is deduced from the sheaf case for the trivial topology `⊥`, where
sheafification is an equivalence, so the one genuinely new ingredient is Tag 03EX for
presheaves. -/

namespace Presheaf

open MonoidalCategory AlgebraicGeometry.SheafOfModules

section Bot

variable {C : Type u} [SmallCategory.{u} C]

/-- For the trivial topology every morphism inverted by sheafification is locally bijective,
because sheafification is the identity. -/
lemma bot_wEqualsLocallyBijective :
    (⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  let (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) : IsIso (toSheafify (⊥ : GrothendieckTopology C) P) :=
    isIso_toSheafify _ (Presheaf.isSheaf_bot P)
  apply GrothendieckTopology.WEqualsLocallyBijective.mk'

/-- For the trivial topology, presheaves of modules *are* sheaves of modules: every presheaf
satisfies the sheaf condition, and the forgetful functor is an inverse on the nose. -/
def botEquiv (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{u}) :
    _root_.PresheafOfModules.{u} R.obj ≌ _root_.SheafOfModules.{u} R where
  functor :=
    { obj := fun M => ⟨M, Presheaf.isSheaf_bot M.presheaf⟩
      map := fun f => ⟨f⟩ }
  inverse := _root_.SheafOfModules.forget R
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end Bot

section

variable {C : Type u} [SmallCategory.{u} C] {O : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- The objectwise tensor functor `· ⊗ G` of presheaves of modules is additive: it is
isomorphic to the monoidal structure's version, which is. -/
instance additive_tensorRight (G : _root_.PresheafOfModules.{u} (ringPresheaf O)) :
    (PresheafOfModules.tensorRight.{u, u, u, u, u} G).Additive :=
  Functor.additive_of_iso (Stacks.SheafOfModules.FlatCoproduct.tensorRightIso.{u, u, u} O G).symm

/-- **Stacks 03EX for presheaves of modules.** If the final term of a short exact sequence of
presheaves of modules is flat, tensoring the sequence with any presheaf of modules gives a short
exact sequence.

This is the sheaf case for the trivial topology, transported along `botEquiv` and the
identification of sheafification with that equivalence. It carries no tag: the clause it proves
belongs to Tag 03EX. -/
theorem shortExact_map_tensorRight
    {S : ShortComplex (_root_.PresheafOfModules.{u} (ringPresheaf O))}
    (hS : S.ShortExact)
    (h₃ : PresheafOfModules.IsFlat S.X₃)
    (G : _root_.PresheafOfModules.{u} (ringPresheaf O)) :
    (S.map (PresheafOfModules.tensorRight G)).ShortExact := by
  have hbot := bot_wEqualsLocallyBijective.{u} (C := C)
  let O' : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u} := ⟨O, Presheaf.isSheaf_bot O⟩
  let R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{u} :=
    Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O'
  let S' : ShortComplex (_root_.PresheafOfModules.{u} R.obj) := S
  let G' : _root_.PresheafOfModules.{u} R.obj := G
  have hS' : S'.ShortExact := hS
  let e := botEquiv R
  let SF : _root_.PresheafOfModules.{u} R.obj ⥤ _root_.SheafOfModules.{u} R :=
    _root_.PresheafOfModules.sheafification.{u} (R := R) (𝟙 R.obj)
  let TF : _root_.PresheafOfModules.{u} R.obj ⥤ _root_.PresheafOfModules.{u} R.obj :=
    PresheafOfModules.tensorRight (O := O'.obj) S'.X₃
  let TG : _root_.PresheafOfModules.{u} R.obj ⥤ _root_.PresheafOfModules.{u} R.obj :=
    PresheafOfModules.tensorRight (O := O'.obj) G'
  have hTGadd : TG.Additive := additive_tensorRight.{u} G
  have hTGzero : TG.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive TG
  have hTFlim : PreservesFiniteLimits TF := h₃.1
  have hTFcolim : PreservesFiniteColimits TF := h₃.2
  have hSFadd : SF.Additive :=
    _root_.PresheafOfModules.sheafification_additive R (𝟙 R.obj)
  let adj : SF ⊣ e.inverse := _root_.PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  have hEIadd : e.inverse.Additive := adj.right_adjoint_additive
  have hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O')
      ((S'.map e.functor).X₃) :=
    ⟨comp_preservesFiniteLimits e.inverse (TF ⋙ SF),
      comp_preservesFiniteColimits e.inverse (TF ⋙ SF)⟩
  have hh :=
    Stacks.SheafOfModules.FlatTensorShortExact.shortExact_map_sheafTensor_flip O'
      (S := S'.map e.functor) (hS'.map_of_exact e.functor) hflat (e.functor.obj G')
  let iso : SF ⋙ e.inverse ≅ 𝟭 _ :=
    Functor.isoWhiskerRight (adj.leftAdjointUniq e.toAdjunction) e.inverse ≪≫ e.unitIso.symm
  exact ShortComplex.shortExact_of_iso ((S'.map TG).mapNatIso iso) (hh.map_of_exact e.inverse)

/-- The braiding, read as an isomorphism `M ⊗ · ≅ · ⊗ M` of endofunctors of presheaves of
modules. -/
def flipIso (M : _root_.PresheafOfModules.{u} (ringPresheaf O)) :
    (curriedTensor (_root_.PresheafOfModules.{u} (ringPresheaf O))).obj M ≅
      (curriedTensor (_root_.PresheafOfModules.{u} (ringPresheaf O))).flip.obj M :=
  BraidedCategory.tensorLeftIsoTensorRight M

/-- Flatness of a presheaf of modules, restated for the monoidal structure's tensor product. -/
lemma isFlat_iff_exactFunctor_curriedTensor (M : _root_.PresheafOfModules.{u} (ringPresheaf O)) :
    PresheafOfModules.IsFlat M ↔
      exactFunctor (_root_.PresheafOfModules.{u} (ringPresheaf O)) _
        ((curriedTensor (_root_.PresheafOfModules.{u} (ringPresheaf O))).flip.obj M) :=
  ⟨fun h ↦ (exactFunctor _ _).prop_of_iso
      (Stacks.SheafOfModules.FlatCoproduct.tensorRightIso.{u, u, u} O M) h,
    fun h ↦ (exactFunctor _ _).prop_of_iso
      (Stacks.SheafOfModules.FlatCoproduct.tensorRightIso.{u, u, u} O M).symm h⟩

/-- For a flat presheaf of modules `M`, the functor `M ⊗ ·` preserves finite limits. -/
lemma preservesFiniteLimits_curriedTensor_obj_of_isFlat
    (M : _root_.PresheafOfModules.{u} (ringPresheaf O)) (hM : PresheafOfModules.IsFlat M) :
    PreservesFiniteLimits
      ((curriedTensor (_root_.PresheafOfModules.{u} (ringPresheaf O))).obj M) :=
  ((exactFunctor _ _).prop_of_iso (flipIso M).symm
    ((isFlat_iff_exactFunctor_curriedTensor M).1 hM)).1

/-- **Stacks 03EX for presheaves of modules, in the `curriedTensor` spelling.** -/
theorem shortExact_map_curriedTensor_flip
    {S : ShortComplex (_root_.PresheafOfModules.{u} (ringPresheaf O))}
    (hS : S.ShortExact) (h₃ : PresheafOfModules.IsFlat S.X₃)
    (G : _root_.PresheafOfModules.{u} (ringPresheaf O)) :
    (S.map ((curriedTensor
      (_root_.PresheafOfModules.{u} (ringPresheaf O))).flip.obj G)).ShortExact :=
  ShortComplex.shortExact_of_iso
    (S.mapNatIso (Stacks.SheafOfModules.FlatCoproduct.tensorRightIso.{u, u, u} O G))
    (shortExact_map_tensorRight hS h₃ G)

/-- Flatness of a presheaf of modules `M` from the one thing right exactness of `M ⊗ ·` leaves
open: that it preserves monomorphisms. -/
lemma isFlat_of_mono_curriedTensor_map (M : _root_.PresheafOfModules.{u} (ringPresheaf O))
    (hmono : ∀ {A B : _root_.PresheafOfModules.{u} (ringPresheaf O)} (ι : A ⟶ B), Mono ι →
      Mono (((curriedTensor (_root_.PresheafOfModules.{u} (ringPresheaf O))).obj M).map ι)) :
    PresheafOfModules.IsFlat M := by
  have hobj : exactFunctor _ _
      ((curriedTensor (_root_.PresheafOfModules.{u} (ringPresheaf O))).obj M) := by
    refine (exactFunctor_iff _).2 ⟨?_, inferInstance⟩
    refine (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).2 fun T hT ↦ ?_
    refine ⟨?_, hmono T.f hT.mono_f⟩
    exact ((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
      ((curriedTensor (_root_.PresheafOfModules.{u} (ringPresheaf O))).obj M)).1
        inferInstance T hT).1
  exact (isFlat_iff_exactFunctor_curriedTensor M).2
    ((exactFunctor _ _).prop_of_iso (flipIso M) hobj)

/-- **Tag 03EY, part (1) for presheaves.** In a short exact sequence of presheaves of modules
whose outer terms are flat, the middle term is flat. -/
@[stacks 03EY "presheaves, part (1)"]
theorem isFlat_middle_of_shortExact
    (S : ShortComplex (_root_.PresheafOfModules.{u} (ringPresheaf O)))
    (hS : S.ShortExact)
    (h₁ : PresheafOfModules.IsFlat S.X₁)
    (h₃ : PresheafOfModules.IsFlat S.X₃) :
    PresheafOfModules.IsFlat S.X₂ := by
  refine isFlat_of_mono_curriedTensor_map S.X₂ ?_
  intro A B ι _
  have := preservesFiniteLimits_curriedTensor_obj_of_isFlat S.X₁ h₁
  have := preservesFiniteLimits_curriedTensor_obj_of_isFlat S.X₃ h₃
  exact mono_map_obj_X₂_of_shortExact
    (curriedTensor (_root_.PresheafOfModules.{u} (ringPresheaf O))) S ι
    (shortExact_map_curriedTensor_flip hS h₃ A) (shortExact_map_curriedTensor_flip hS h₃ B)

/-- **Tag 03EY, part (2) for presheaves.** In a short exact sequence of presheaves of modules
whose middle and right terms are flat, the left term is flat. -/
@[stacks 03EY "presheaves, part (2)", sga "4 XVII 4.1.1" "(i), presheaves"]
theorem isFlat_left_of_shortExact
    (S : ShortComplex (_root_.PresheafOfModules.{u} (ringPresheaf O)))
    (hS : S.ShortExact)
    (h₂ : PresheafOfModules.IsFlat S.X₂)
    (h₃ : PresheafOfModules.IsFlat S.X₃) :
    PresheafOfModules.IsFlat S.X₁ := by
  refine isFlat_of_mono_curriedTensor_map S.X₁ ?_
  intro A B ι _
  have := preservesFiniteLimits_curriedTensor_obj_of_isFlat S.X₂ h₂
  exact mono_map_obj_of_mono_app
    (curriedTensor (_root_.PresheafOfModules.{u} (ringPresheaf O))) S.f ι
    (shortExact_map_curriedTensor_flip hS h₃ A).mono_f

end

end Presheaf

end Stacks.SheafOfModules.FlatTwoOutOfThree

end

end
