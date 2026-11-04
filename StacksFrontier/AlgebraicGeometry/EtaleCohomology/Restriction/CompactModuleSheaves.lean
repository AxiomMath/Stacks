module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactRepresentables
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Compactness of module-valued sheaves: the coefficient change away from sets

Part (4) of Stacks 0738 says that on a site, taking sections over an object `U` whose coverings
are refined by finite coverings with quasi-compact fibre products commutes with filtered colimits
of sheaves **of sets**
(`CategoryTheory.Sheaf.preservesFilteredColimitsOfSize_sheafSections`). Stacks 09Z4 needs the
same statement for sheaves of modules, and that is not a formal consequence: a colimit of sheaves
is the sheafification of the colimit of the underlying presheaves, so passing between coefficient
categories has to be compatible with sheafification before anything can be transported.

This file carries out that coefficient change, for an arbitrary site and an arbitrary ring, and
then draws the conclusion Stacks 09Z4 is after: the module-valued analogue of the sheafified
representable — the extension by zero of the constant free rank-one module sheaf, realized as the
free module sheaf on the sheafified representable — is a finitely presentable object, and so is a
coequalizer of two maps between finite direct sums of such sheaves. That last shape is exactly the
one Stacks 095N produces from a constructible sheaf of modules on a quasi-compact quasi-separated
scheme, so this is the category-theoretic half of the module case of Stacks 09Z4.

Nothing here mentions schemes: every statement holds over an arbitrary site, and the geometry
enters only through the hypothesis
`CategoryTheory.GrothendieckTopology.HasFiniteQuasiCompactCoverings`, as it does for sheaves of
sets in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactRepresentables`.

## Main results

* `CategoryTheory.Sheaf.preservesColimitsOfShape_sheafCompose` — post-composition with a
  sheafification-preserving functor commutes with colimits of sheaves.
* `CategoryTheory.Sheaf.hasWeakSheafify_moduleCat` and
  `CategoryTheory.Sheaf.preservesSheafification_forget_moduleCat` — module-valued presheaves on a
  site admit weak sheafification, and the forgetful functor to sets preserves it, at the
  coefficient universe of the site.
* `CategoryTheory.Sheaf.preservesFilteredColimitsOfSize_sheafSections_moduleCat` — **part (4) of
  Stacks 0738 for sheaves of modules**: sections over an object with a cofinal system of finite
  coverings with quasi-compact fibre products commute with filtered colimits.
* `CategoryTheory.Sheaf.isFinitelyPresentable_composeAndSheafify_free_sheafifiedYoneda` — the free
  module sheaf on such a sheafified representable is finitely presentable.
* `CategoryTheory.Sheaf.isFinitelyPresentable_coequalizer_sigma_composeAndSheafify_free` — so is a
  coequalizer of two maps between finite direct sums of them.
* `CategoryTheory.GrothendieckTopology.hasFiniteQuasiCompactCoverings_bot` and
  `CategoryTheory.Sheaf.exists_isFinitelyPresentable_moduleCat_bot` — the hypothesis of all of the
  above is satisfiable, and the whole chain is dischargeable, on the trivial topology.

## Implementation notes

The coefficient universe is `max u v` for a site `C : Type u` with `Category.{v} C`. It is forced,
not chosen: the sheaves-of-sets statement being transported is about `Type max u v`, which is the
target of `forget (ModuleCat.{max u v} R)`, so no other module universe lets the two sections
functors be compared. The ring universe `r` stays free for everything up to and including the
sections statement; it is tied to `max u v` only from
`CategoryTheory.Sheaf.isFinitelyPresentable_composeAndSheafify_free_sheafifiedYoneda` on, because
the free-module functor `ModuleCat.free` has the ring and the module in one universe — and that
tie is real rather than bureaucratic, since for `r` larger than the module universe the free module
on a one-point set is not an object of `ModuleCat.{max u v} R` at all, so the forgetful functor has
no left adjoint there.

Three instances are assembled by hand rather than found: `ModuleCat`'s standard filtered-colimit
instance ties the module universe to the ring universe, so preservation of filtered colimits by
`forget (ModuleCat.{max u v} R)` is routed through abelian groups. With that in place Mathlib's own
`CategoryTheory.GrothendieckTopology.PreservesSheafification` instance for a forgetful functor
applies, and the sheafification of module-valued presheaves follows. They are `theorem`s rather
than `instance`s because their coefficient universe is written with a `max`, which does not unify
at a concrete site; a consumer introduces them with `let`, as
`AlgebraicGeometry.SmallEtale.hasSheafify_moduleCat` is introduced.

`CategoryTheory.Sheaf.preservesColimitsOfShape_sheafCompose` subsumes
`Stacks.Cohomology.Sections.preservesColimitsOfShape_sheafCompose`, which is the same statement
with the site and the index category restricted to one universe, and the proof inlined in
`Stacks.Cohomology.CompactSections.preservesColimitsOfShape_sheafCompose_forget`, which is its
special case for `forget AddCommGrpCat` on the site of opens of a space. It also weakens
`HasSheafify` to `HasWeakSheafify`, which is all the argument uses. The reduction of a diagram of
sheaves to a diagram of presheaves followed by sheafification is needed because `sheafToPresheaf`
does **not** preserve filtered colimits; the counit of the sheafification adjunction being an
isomorphism is what replaces that.

The finite direct sums are taken with respect to a `HasColimitsOfShape` instance supplied by the
caller rather than one synthesised here, for the reason given in `CompactRepresentables`: a
consumer stating a presentation has already fixed one, and the two must agree for the statements to
match up.

`Fact Cardinal.aleph0.IsRegular` is a local instance, as in Mathlib's file on finitely presentable
objects.

## References

* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₂ u₂ v₁ u₁ vI uI r v u

namespace CategoryTheory

attribute [local instance] Cardinal.fact_isRegular_aleph0

variable {C : Type u} [Category.{v} C]

namespace GrothendieckTopology

/-- **The hypothesis of part (4) of Stacks 0738 is satisfiable.** On the trivial topology the only
covering sieve of `U` is the maximal one, which is refined by the one-member family `{𝟙 U}`; its
only fibre product is `U` itself, and every object of the trivial site is quasi-compact
(`CategoryTheory.GrothendieckTopology.isQuasiCompactObject_bot`).

(No object of a *nontrivial* site is exhibited here. The predicate is not refuted at the opposite
degenerate topology either: on the discrete topology every sieve covers, and the empty family
refines the empty sieve.) -/
public theorem hasFiniteQuasiCompactCoverings_bot (U : C) :
    (⊥ : GrothendieckTopology C).HasFiniteQuasiCompactCoverings U := by
  intro S hS
  refine ⟨{ I₀ := PUnit, X := fun _ => U, f := fun _ => 𝟙 U }, inferInstance, ?_, ?_, ?_⟩
  · rw [bot_covering, ← Sieve.id_mem_iff_eq_top]
    exact Sieve.ofArrows_mk _ _ PUnit.unit
  · rw [bot_covering.1 hS]
    exact le_top
  · exact fun _ _ => ⟨U, 𝟙 U, 𝟙 U, IsPullback.of_horiz_isIso ⟨by simp⟩,
      isQuasiCompactObject_bot U⟩

end GrothendieckTopology

namespace Sheaf

variable (J : GrothendieckTopology C)

/-- **Post-composition with a sheafification-preserving functor commutes with colimits.** If
`F : A ⥤ B` preserves sheafification and `I`-colimits then `sheafCompose J F` preserves
`I`-colimits of sheaves.

The argument cannot go through `sheafToPresheaf`, which does not preserve filtered colimits.
Instead the diagram of sheaves is rewritten as a diagram of presheaves followed by sheafification,
using that the counit of the sheafification adjunction is an isomorphism; then only the left
adjoint `presheafToSheaf` and the composite `presheafToSheaf ⋙ sheafCompose J F` — which
`CategoryTheory.sheafComposeNatIso` identifies with a whiskering by `F`, colimit-preserving
pointwise — have to preserve colimits. -/
public theorem preservesColimitsOfShape_sheafCompose
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {I : Type uI} [Category.{vI} I]
    [HasWeakSheafify J A] [HasWeakSheafify J B]
    [HasColimitsOfShape I A] [HasColimitsOfShape I B]
    (F : A ⥤ B) [J.HasSheafCompose F] [J.PreservesSheafification F]
    [PreservesColimitsOfShape I F] :
    PreservesColimitsOfShape I (sheafCompose J F) := by
  have : PreservesColimitsOfShape I (presheafToSheaf J A ⋙ sheafCompose J F) :=
    preservesColimitsOfShape_of_natIso
      (sheafComposeNatIso J F (sheafificationAdjunction J A) (sheafificationAdjunction J B))
  constructor
  intro D
  let : PreservesColimit (D ⋙ sheafToPresheaf J A ⋙ presheafToSheaf J A)
      (sheafCompose J F) :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves (presheafToSheaf J A) (colimit.isColimit (D ⋙ sheafToPresheaf J A)))
      (isColimitOfPreserves (presheafToSheaf J A ⋙ sheafCompose J F)
        (colimit.isColimit (D ⋙ sheafToPresheaf J A)))
  exact preservesColimit_of_iso_diagram (sheafCompose J F)
    (Functor.isoWhiskerLeft D (asIso (sheafificationAdjunction J A).counit))

/-- The forgetful functor from modules to sets preserves filtered colimits, routed through abelian
groups. -/
private theorem preservesFilteredColimits_forget_moduleCat (R : Type r) [Ring R] :
    PreservesFilteredColimits (forget (ModuleCat.{u₁} R)) := by
  let : PreservesColimitsOfSize.{u₁, u₁}
      (forget₂ (ModuleCat.{u₁} R) AddCommGrpCat.{u₁}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u₁, r, u₁, u₁} R
  let : PreservesFilteredColimits (forget (ModuleCat.{u₁} R)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{u₁} R) AddCommGrpCat.{u₁}) (forget AddCommGrpCat.{u₁})
  infer_instance

/-- **Weak sheafification of module-valued presheaves on a site.** The standard filtered-colimit
instance for `ModuleCat` ties the module universe to the ring universe, so the instance the plus
construction needs is assembled through abelian groups instead. -/
@[sga "7 VI 3.1(a)" "partial"]
public theorem hasWeakSheafify_moduleCat (R : Type r) [Ring R] :
    HasWeakSheafify J (ModuleCat.{max u v} R) := by
  have := preservesFilteredColimits_forget_moduleCat.{max u v, r} R
  infer_instance

/-- **The forgetful functor from modules to sets preserves sheafification.** This is Mathlib's own
instance for the forgetful functor of a concrete category; what has to be supplied is that
`forget (ModuleCat.{max u v} R)` preserves filtered colimits indexed by the site, which again goes
through abelian groups. -/
public theorem preservesSheafification_forget_moduleCat (R : Type r) [Ring R] :
    J.PreservesSheafification (forget (ModuleCat.{max u v} R)) := by
  have := preservesFilteredColimits_forget_moduleCat.{max u v, r} R
  infer_instance

/-- **Forgetting the module structure of a sheaf of modules commutes with filtered colimits.** The
two previous statements and `CategoryTheory.Sheaf.preservesColimitsOfShape_sheafCompose`. -/
public theorem preservesFilteredColimitsOfSize_sheafCompose_forget_moduleCat
    (R : Type r) [Ring R] :
    PreservesFilteredColimitsOfSize.{max u v, max u v}
      (sheafCompose J (forget (ModuleCat.{max u v} R))) := by
  have := preservesFilteredColimits_forget_moduleCat.{max u v, r} R
  exact ⟨fun I _ _ => preservesColimitsOfShape_sheafCompose J (forget (ModuleCat.{max u v} R))⟩

/-- **Part (4) of Stacks 0738 for sheaves of modules.** Sections over an object all of whose
coverings are refined by finite coverings with quasi-compact fibre products commute with filtered
colimits of sheaves of modules over any ring.

The underlying map of sets is the comparison map for sheaves of sets, which is bijective by part
(4) of Stacks 0738; forgetting the module structure commutes with the colimit by the previous
statement, and the forgetful functor reflects isomorphisms. -/
public theorem preservesFilteredColimitsOfSize_sheafSections_moduleCat
    (R : Type r) [Ring R] {U : C} (H : J.HasFiniteQuasiCompactCoverings U) :
    PreservesFilteredColimitsOfSize.{max u v, max u v}
      ((sheafSections J (ModuleCat.{max u v} R)).obj (op U)) := by
  let := hasWeakSheafify_moduleCat.{r, v, u} J R
  have := preservesFilteredColimits_forget_moduleCat.{max u v, r} R
  refine ⟨fun I _ _ => ?_⟩
  let : PreservesColimitsOfShape I (sheafCompose J (forget (ModuleCat.{max u v} R))) :=
    (preservesFilteredColimitsOfSize_sheafCompose_forget_moduleCat.{r, v, u} J
      R).preserves_filtered_colimits I
  let : PreservesColimitsOfShape I ((sheafSections J (Type max u v)).obj (op U)) :=
    (preservesFilteredColimitsOfSize_sheafSections J H).preserves_filtered_colimits I
  let : PreservesColimitsOfShape I
      (sheafCompose J (forget (ModuleCat.{max u v} R)) ⋙
        (sheafSections J (Type max u v)).obj (op U)) := inferInstance
  let : PreservesColimitsOfShape I
      ((sheafSections J (ModuleCat.{max u v} R)).obj (op U) ⋙
        forget (ModuleCat.{max u v} R)) :=
    preservesColimitsOfShape_of_natIso
      (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl) :
        sheafCompose J (forget (ModuleCat.{max u v} R)) ⋙
          (sheafSections J (Type max u v)).obj (op U) ≅
        (sheafSections J (ModuleCat.{max u v} R)).obj (op U) ⋙
          forget (ModuleCat.{max u v} R))
  let : ReflectsColimitsOfShape I (forget (ModuleCat.{max u v} R)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves
    ((sheafSections J (ModuleCat.{max u v} R)).obj (op U)) (forget (ModuleCat.{max u v} R))

/-- **The free module sheaf on a sheafified representable is finitely presentable**, for every
object `U` of the site all of whose coverings are refined by finite coverings with quasi-compact
fibre products.

This is the module-valued form in which part (4) of Stacks 0738 enters the module case of Stacks
09Z4. The free module sheaf on `h_U^#` is the extension by zero from `U` of the constant free
rank-one module sheaf; morphisms out of it are, by the free-forgetful adjunction and Yoneda's lemma
for sheaves of sets, the sections over `U`, and those commute with filtered colimits. Formally it
is `CategoryTheory.Sheaf.composeAndSheafify`, the left adjoint of
`sheafCompose J (forget (ModuleCat R))`, applied to a finitely presentable object, and that
adjoint's right adjoint preserves filtered colimits. -/
public theorem isFinitelyPresentable_composeAndSheafify_free_sheafifiedYoneda
    (R : Type max u v) [Ring R] {U : C} (H : J.HasFiniteQuasiCompactCoverings U) :
    IsFinitelyPresentable.{max u v}
      ((composeAndSheafify J (ModuleCat.free R)).obj ((sheafifiedYoneda J).obj U)) := by
  let := hasWeakSheafify_moduleCat.{max u v, v, u} J R
  let := isFinitelyPresentable_sheafifiedYoneda J H
  let : (sheafCompose J (forget (ModuleCat.{max u v} R))).IsFinitelyAccessible.{max u v} :=
    Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize.2
      (preservesFilteredColimitsOfSize_sheafCompose_forget_moduleCat.{max u v, v, u} J R)
  exact (Sheaf.adjunction J (ModuleCat.adj R)).isCardinalPresentable_leftAdjoint_obj _ _

section Presentation

variable (R : Type max u v) [Ring R] [HasWeakSheafify J (ModuleCat.{max u v} R)]

/-- A finite direct sum of free module sheaves on sheafified representables, at objects whose
coverings are refined by finite coverings with quasi-compact fibre products, is finitely
presentable. -/
public theorem isFinitelyPresentable_sigma_composeAndSheafify_free_sheafifiedYoneda
    {k : ℕ} (W : Fin k → C) (hW : ∀ i, J.HasFiniteQuasiCompactCoverings (W i))
    [HasColimitsOfShape (Discrete (Fin k)) (Sheaf J (ModuleCat.{max u v} R))] :
    IsFinitelyPresentable.{max u v}
      (∐ fun i ↦ (composeAndSheafify J (ModuleCat.free R)).obj
        ((sheafifiedYoneda J).obj (W i))) := by
  have : ∀ j : Discrete (Fin k),
      IsFinitelyPresentable.{max u v}
        ((Discrete.functor fun i ↦ (composeAndSheafify J (ModuleCat.free R)).obj
          ((sheafifiedYoneda J).obj (W i))).obj j) := by
    rintro ⟨i⟩
    exact isFinitelyPresentable_composeAndSheafify_free_sheafifiedYoneda J R (hW i)
  exact isFinitelyPresentable_of_isColimit_of_finCategory _ (colimit.isColimit _)

/-- **A finite shriek presentation makes a sheaf of modules finitely presentable.** A coequalizer
of two maps between finite direct sums of free module sheaves on sheafified representables, at
objects whose coverings are refined by finite coverings with quasi-compact fibre products, is
finitely presentable.

This is the shape in which Stacks 095N presents a constructible sheaf of modules over a Noetherian
ring on a quasi-compact quasi-separated scheme, and hence the step of the module case of
**Stacks 09Z4** that does not depend on the geometry of the small étale site. -/
public theorem isFinitelyPresentable_coequalizer_sigma_composeAndSheafify_free
    {n m : ℕ} (U : Fin n → C) (V : Fin m → C)
    (hU : ∀ i, J.HasFiniteQuasiCompactCoverings (U i))
    (hV : ∀ j, J.HasFiniteQuasiCompactCoverings (V j))
    [HasColimitsOfShape (Discrete (Fin n)) (Sheaf J (ModuleCat.{max u v} R))]
    [HasColimitsOfShape (Discrete (Fin m)) (Sheaf J (ModuleCat.{max u v} R))]
    (f g : (∐ fun j ↦ (composeAndSheafify J (ModuleCat.free R)).obj
          ((sheafifiedYoneda J).obj (V j))) ⟶
        ∐ fun i ↦ (composeAndSheafify J (ModuleCat.free R)).obj
          ((sheafifiedYoneda J).obj (U i)))
    [HasColimit (parallelPair f g)] :
    IsFinitelyPresentable.{max u v} (coequalizer f g) := by
  have : ∀ j : WalkingParallelPair,
      IsFinitelyPresentable.{max u v} ((parallelPair f g).obj j) := by
    rintro (_ | _)
    · exact isFinitelyPresentable_sigma_composeAndSheafify_free_sheafifiedYoneda J R V hV
    · exact isFinitelyPresentable_sigma_composeAndSheafify_free_sheafifiedYoneda J R U hU
  exact isFinitelyPresentable_of_isColimit_of_finCategory _ (colimit.isColimit _)

end Presentation

/-- **The chain above is dischargeable.** On the trivial topology the hypothesis on `U` holds for
every object, weak sheafification of module-valued presheaves is available, and the free module
sheaf on the sheafified representable at `U` is a finitely presentable sheaf of modules. So no
statement
above is conditional on an unexhibited hypothesis. -/
public theorem exists_isFinitelyPresentable_moduleCat_bot (R : Type max u v) [Ring R] (U : C) :
    ∃ F : Sheaf (⊥ : GrothendieckTopology C) (ModuleCat.{max u v} R),
      IsFinitelyPresentable.{max u v} F := by
  let := hasWeakSheafify_moduleCat.{max u v, v, u} (⊥ : GrothendieckTopology C) R
  exact ⟨_, isFinitelyPresentable_composeAndSheafify_free_sheafifiedYoneda ⊥ R
    (GrothendieckTopology.hasFiniteQuasiCompactCoverings_bot U)⟩

end Sheaf

end CategoryTheory

end
