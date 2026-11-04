module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantWeakSerre
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UliftFunctorSheafification
public import StacksFrontier.CategoryTheory.Sites.SheafOfSetsUniverseDescent

/-!
# Descending the coefficient universe of a finite type locally constant sheaf of modules

`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf` (Tag 093U) is stated for sheaves of
`Λ`-modules whose sections live in `ModuleCat.{max u v w} Λ` on a site `C : Type u` with
`Category.{v} C`, the module universes at which sheafification is automatic. This file shows that
on finite type locally constant sheaves all of those universes carry the same objects: such a
sheaf with sections in `ModuleCat.{max u v s} Λ` is the pointwise universe lift of one with
sections in `ModuleCat.{max u v} Λ`, which is again finite type locally constant.

This is the module-coefficient form of
`Stacks.ConstantSheaf.exists_isFiniteLocallyConstant_uliftFunctor_iso`, and the argument is the
same: finite type local constancy bounds the size of the sections, because a sheaf is separated
for each of its covering sieves, so its sections over an object inject into the product of its
sections over the members of a trivializing covering family, indexed by a type in
`Type (max u v)`, and over a member the sheaf is the constant sheaf on a *finitely generated*
`Λ`-module, which is `max u v`-small as soon as `Λ` is.

## Main results

* `Stacks.ConstantSheaf.small_constantSheaf_moduleSections`: the sections of the constant sheaf on
  a finitely generated `Λ`-module are `max u v`-small, whatever the universe they are presented
  in.
* `Stacks.ConstantSheaf.small_sections_of_isFiniteTypeLocallyConstantModuleSheaf`: the sections of
  a finite type locally constant sheaf of `Λ`-modules over any object of the site are
  `max u v`-small.
* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_of_uliftFunctor_iso`: finite type
  local constancy descends along the pointwise universe lift of a sheaf of modules.
* `Stacks.ConstantSheaf.exists_isFiniteTypeLocallyConstantModuleSheaf_uliftFunctor_iso`: **the
  descent itself** — a finite type locally constant sheaf of `Λ`-modules with sections in
  `ModuleCat.{max u v s} Λ` is isomorphic to the pointwise universe lift of a finite type locally
  constant sheaf of `Λ`-modules with sections in `ModuleCat.{max u v} Λ`.

## Implementation notes

What made the module case wait for the set case is that `ModuleCat.uliftFunctor` carried no
`CategoryTheory.GrothendieckTopology.HasSheafCompose` instance, so `sheafCompose J
(ModuleCat.uliftFunctor Λ)` did not typecheck and the two steps of the argument that go through it
— `CategoryTheory.constantCommuteCompose`, for the smallness of the sections of a constant sheaf,
and `CategoryTheory.fullyFaithfulSheafCompose`, for the descent of the trivializations — had no
module analogue. That is supplied by
`ModuleCat.hasSheafCompose_uliftFunctor` and `ModuleCat.preservesSheafification_uliftFunctor`.

The small model of the sections is not a shrinking construction on presheaves, as it is for
sheaves of sets: the values of `F` are `max u v`-small objects of `ModuleCat.{max u v s} Λ`,
hence lie in the essential image of the fully faithful `ModuleCat.uliftFunctor.{s, max u v} Λ`
(the witness being `CategoryTheory.Shrink` of the carrier with the module structure transported
along `Shrink.linearEquiv`), and `CategoryTheory.Functor.essImage.liftFunctor` factors a functor
through a fully faithful functor whose essential image contains its values. There is therefore no
module analogue of `CategoryTheory.FunctorToTypes.shrink` here, and none is needed.

The hypothesis `Small.{max u v} Λ` is not an artefact: finite *type* over `Λ` bounds the size of
a module only relative to the size of `Λ`, where in the set case finiteness bounded it absolutely.

The universe lift is spelled `ModuleCat.uliftFunctor.{s, max u v} Λ`, parametrized by the level
the universe is raised *by*: the instances of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UliftFunctorSheafification` are stated for a free
module universe dominating `max u v`, which this spelling meets with `UnivLE.{max u v, max u v}`.

## References

* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe s v u r

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (Λ : Type r) [Ring Λ]
  [Small.{max u v} Λ]

/-- **The sections of the constant sheaf on a finitely generated module are small.** A finitely
generated module over a `max u v`-small ring is `max u v`-small, hence the universe lift of a
module in `ModuleCat.{max u v} Λ`, and the universe lift commutes with the constant sheaf, so the
sections are a universe lift. -/
theorem small_constantSheaf_moduleSections (E : ModuleCat.{max u v s} Λ)
    (hE : ModuleCat.isFG Λ E) (Y : C) :
    Small.{max u v} (((constantSheaf J (ModuleCat.{max u v s} Λ)).obj E).obj.obj (op Y)) := by
  have : Module.Finite Λ E := hE
  have : Small.{max u v} (E : Type _) := Module.Finite.small Λ E
  let E₀ : ModuleCat.{max u v} Λ := ModuleCat.of Λ (Shrink.{max u v} E)
  have e : (ModuleCat.uliftFunctor.{s, max u v} Λ).obj E₀ ≅ E :=
    (ULift.moduleEquiv.trans (Shrink.linearEquiv Λ E)).toModuleIso
  let k : ((constantSheaf J (ModuleCat.{max u v s} Λ)).obj E).obj.obj (op Y) ≅
      (ModuleCat.uliftFunctor.{s, max u v} Λ).obj
        (((constantSheaf J (ModuleCat.{max u v} Λ)).obj E₀).obj.obj (op Y)) :=
    ((sheafSections J (ModuleCat.{max u v s} Λ)).obj (op Y)).mapIso
      (((constantSheaf J (ModuleCat.{max u v s} Λ)).mapIso e).symm ≪≫
        ((constantCommuteCompose J (ModuleCat.uliftFunctor.{s, max u v} Λ)).app E₀).symm)
  exact small_map
    (((forget (ModuleCat.{max u v s} Λ)).mapIso k).toEquiv.trans Equiv.ulift)

/-- **The sections of a finite type locally constant sheaf of modules are small.** They inject
into the product, over a trivializing covering family of the object, of the sections over its
members, and those are the sections of a constant sheaf on a finitely generated module. -/
theorem small_sections_of_isFiniteTypeLocallyConstantModuleSheaf
    (F : Sheaf J (ModuleCat.{max u v s} Λ))
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{v, u, s} J Λ F) (U : C) :
    Small.{max u v} (F.obj.obj (op U)) := by
  obtain ⟨I, X, f, hf, h⟩ := hF U
  let G : Sheaf J (Type max u v s) :=
    ⟨F.obj ⋙ forget (ModuleCat.{max u v s} Λ),
      Presheaf.isSheaf_comp_of_isSheaf J F.obj _ F.property⟩
  have hi : ∀ i, Small.{max u v} (G.obj.obj (op (X i))) := by
    intro i
    obtain ⟨E, hE, ⟨e⟩⟩ := h i
    exact small_map
      (hβ := small_constantSheaf_moduleSections.{s} (J.over (X i)) Λ E hE (Over.mk (𝟙 (X i))))
      ((forget (ModuleCat.{max u v s} Λ)).mapIso
        (((sheafSections (J.over (X i)) (ModuleCat.{max u v s} Λ)).obj
          (op (Over.mk (𝟙 (X i))))).mapIso e).symm).toEquiv
  exact small_of_injective (Sheaves.UniverseLift.injective_restrict_ofArrows J G X f hf)

/-- **Finite type local constancy descends along the pointwise universe lift of a sheaf of
modules.** -/
theorem isFiniteTypeLocallyConstantModuleSheaf_of_uliftFunctor_iso
    {F₀ : Sheaf J (ModuleCat.{max u v} Λ)} {F : Sheaf J (ModuleCat.{max u v s} Λ)}
    (e : (sheafCompose J (ModuleCat.uliftFunctor.{s, max u v} Λ)).obj F₀ ≅ F)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{v, u, s} J Λ F) :
    IsFiniteTypeLocallyConstantModuleSheaf.{v, u, v} J Λ F₀ := by
  intro U
  obtain ⟨I, X, f, hf, h⟩ := hF U
  refine ⟨I, X, f, hf, fun i ↦ ?_⟩
  obtain ⟨E, hE, ⟨eE⟩⟩ := h i
  let _ : HasSheafify (J.over (X i)) (ModuleCat.{max u v} Λ) :=
    hasSheafify_moduleCat_of_univLE.{max u v, v, r, max u v} (J.over (X i)) Λ
  let _ : HasSheafify (J.over (X i)) (ModuleCat.{max u v s} Λ) :=
    hasSheafify_moduleCat_of_univLE.{max u v, v, r, max u v s} (J.over (X i)) Λ
  have : Module.Finite Λ E := hE
  have : Small.{max u v} (E : Type _) := Module.Finite.small Λ E
  have e₀ : (ModuleCat.uliftFunctor.{s, max u v} Λ).obj
      (ModuleCat.of Λ (Shrink.{max u v} E)) ≅ E :=
    (ULift.moduleEquiv.trans (Shrink.linearEquiv Λ E)).toModuleIso
  refine ⟨ModuleCat.of Λ (Shrink.{max u v} E),
    Module.Finite.equiv (Shrink.linearEquiv Λ (E : Type _)).symm, ⟨?_⟩⟩
  have e' : (sheafCompose (J.over (X i)) (ModuleCat.uliftFunctor.{s, max u v} Λ)).obj
        ((constantSheaf (J.over (X i)) (ModuleCat.{max u v} Λ)).obj
          (ModuleCat.of Λ (Shrink.{max u v} E))) ≅
      (sheafCompose (J.over (X i)) (ModuleCat.uliftFunctor.{s, max u v} Λ)).obj
        ((J.overPullback (ModuleCat.{max u v} Λ) (X i)).obj F₀) :=
    (constantCommuteCompose (J.over (X i)) (ModuleCat.uliftFunctor.{s, max u v} Λ)).app _ ≪≫
      (constantSheaf (J.over (X i)) (ModuleCat.{max u v s} Λ)).mapIso e₀ ≪≫ eE ≪≫
      (J.overPullback (ModuleCat.{max u v s} Λ) (X i)).mapIso e.symm
  exact (fullyFaithfulSheafCompose (J.over (X i))
    (ModuleCat.fullyFaithfulUliftFunctor.{r, max u v, s} Λ)).preimageIso e'

/-- **A finite type locally constant sheaf of modules is the pointwise universe lift of a finite
type locally constant sheaf of modules with sections in the smallest universe.** -/
theorem exists_isFiniteTypeLocallyConstantModuleSheaf_uliftFunctor_iso
    (F : Sheaf J (ModuleCat.{max u v s} Λ))
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{v, u, s} J Λ F) :
    ∃ F₀ : Sheaf J (ModuleCat.{max u v} Λ),
      IsFiniteTypeLocallyConstantModuleSheaf.{v, u, v} J Λ F₀ ∧
        Nonempty ((sheafCompose J (ModuleCat.uliftFunctor.{s, max u v} Λ)).obj F₀ ≅ F) := by
  have hsm : ∀ Y : Cᵒᵖ, Small.{max u v} (F.obj.obj Y) := fun Y ↦
    small_sections_of_isFiniteTypeLocallyConstantModuleSheaf.{s} J Λ F hF Y.unop
  have hess : ∀ Y : Cᵒᵖ,
      (ModuleCat.uliftFunctor.{s, max u v} Λ).essImage (F.obj.obj Y) := fun Y ↦
    ⟨ModuleCat.of Λ (Shrink.{max u v} (F.obj.obj Y)),
      ⟨(ULift.moduleEquiv.trans (Shrink.linearEquiv Λ (F.obj.obj Y : Type _))).toModuleIso⟩⟩
  have ei : Functor.essImage.liftFunctor F.obj (ModuleCat.uliftFunctor.{s, max u v} Λ) hess ⋙
      ModuleCat.uliftFunctor.{s, max u v} Λ ≅ F.obj :=
    Functor.essImage.liftFunctorCompIso F.obj (ModuleCat.uliftFunctor.{s, max u v} Λ) hess
  let F₀ : Sheaf J (ModuleCat.{max u v} Λ) :=
    ⟨Functor.essImage.liftFunctor F.obj (ModuleCat.uliftFunctor.{s, max u v} Λ) hess,
      Presheaf.isSheaf_of_isSheaf_comp J _ (ModuleCat.uliftFunctor.{s, max u v} Λ)
        ((Presheaf.isSheaf_of_iso_iff ei).2 F.property)⟩
  have e : (sheafCompose J (ModuleCat.uliftFunctor.{s, max u v} Λ)).obj F₀ ≅ F :=
    (fullyFaithfulSheafToPresheaf J (ModuleCat.{max u v s} Λ)).preimageIso ei
  exact ⟨F₀, isFiniteTypeLocallyConstantModuleSheaf_of_uliftFunctor_iso.{s} J Λ e hF, ⟨e⟩⟩

end Stacks.ConstantSheaf

end
