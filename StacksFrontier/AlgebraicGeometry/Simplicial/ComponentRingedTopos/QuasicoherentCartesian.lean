module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModulePairFunctor
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransition
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSheafify

/-!
# Quasi-coherent modules on the total site of a simplicial site

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of rings on its total
site. Stacks 0D7M says that a sheaf of `O`-modules `F` is quasi-coherent in the sense of
Modules on Sites, Definition 03DL, if and only if `F` is cartesian and every component module
`F_n` is a quasi-coherent `O_n`-module.

This file assembles the right-hand side of that equivalence from the pieces the development
already has — the cartesian condition of Stacks 07TF (2) and quasi-coherence on a site of
Stacks 03DL (6) — and proves the colimit mechanism that both directions of the source's proof
run on: a natural transformation between two functors that preserve the relevant colimits and
agree on the structure sheaf agrees on every module that admits a global presentation.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.IsCartesianWithQuasicoherentComponents`: the
  right-hand side of Stacks 0D7M — `F` is cartesian and every `F_n` is quasi-coherent.

## Main results

* `Stacks.CategoryTheory.isIso_app_of_isColimit`: a natural transformation that is invertible
  on the objects of a diagram is invertible at a colimit of that diagram, provided both
  functors preserve it.
* `Stacks.SheafOfModules.isIso_app_free`: such a transformation is invertible on free sheaves
  of modules as soon as it is invertible on the structure sheaf.
* `Stacks.SheafOfModules.isIso_app_of_presentation`: it is then invertible on every sheaf of
  modules admitting a `SheafOfModules.Presentation`.

## Implementation notes

**What is proved about Stacks 0D7M and what is not.** Neither implication of the source's
equivalence is proved here. Both of its directions turn a *local* presentation of a module on
a slice of one site into a presentation on a slice of the other — the source writes
"restricting the presentation above to the sites `C_n/U_i` and `C_m/V_i`" for the forward
direction and "pulling back to `C_{total}/U_i`" for the converse — and the development has no
localization of the total site at an object: nothing relates the slice `C_{total}/U` of the
total site to the slice `C_n/U` of the component site, and `S.totalTopology.over` does not
occur anywhere. The localized pullback that the quasi-coherent clause of Stacks 03DO is proved
from, `Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos`, is available only
for a morphism of ringed *sites* presented by a left exact continuous functor, and the
component morphism `g_n` of Stacks 09WG is not of that form: its inverse image is restriction
along the *cocontinuous* component inclusion `C_n ⥤ C_{total}`.

**What the colimit mechanism supplies.** Granted such a localization, the remaining step in
each direction is the one proved here in its global form: the transition
`f_φ^*F_m ⟶ F_n` of Stacks 09WF is a natural transformation between two functors that are
pullbacks of sheaves of modules, hence preserve colimits (Stacks 03DC (2)), so it is invertible
on every module built from the structure sheaf by coproducts and cokernels — which is what a
global presentation exhibits. The three lemmas are stated for an arbitrary pair of functors so
that the same mechanism serves the converse direction, where the functors run the other way.

**On `Stacks.CategoryTheory.isIso_app_of_isColimit`.** The same statement is proved, in the
same generality, at `Stacks.EilenbergWatts.isIso_app_of_isColimit`
(`StacksFrontier/AlgebraicGeometry/EilenbergWatts/Devissage.lean`) and
`Stacks.AlgebraicGeometry.PushforwardColimits.isIso_app_of_isColimit`
(`StacksFrontier/AlgebraicGeometry/PushforwardColimits/Unit.lean`) and
`CategoryTheory.NatTrans.isIso_app_of_isColimit_mapCocone`
(`StacksFrontier/AlgebraicGeometry/Duality/ProjectionFormulaCokernel.lean`), and in a restricted
form at `StacksDraft.CompactDevissage.isIso_app_of_isColimit`. Each of those sits behind
imports unrelated to sites — monoidal closed module categories, schemes, triangulated
categories — so none can be reused here without dragging them into the simplicial-sites tree.
It is restated rather than imported, and the five copies belong in one place.

**The cartesian condition used.** There are two declarations named
`CategoryTheory.SimplicialSiteSituation.IsCartesianModule` in the development, in modules that
do not import each other; this file uses the one of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/CartesianModule.lean`, whose
component restriction is the pullback of sheaves of modules along the component morphism of
ringed topoi of Stacks 0D72, because that is the restriction whose target carries the
component structure sheaf `O_n` that Stacks 0D7M asks quasi-coherence over.

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.CategoryTheory

universe v₁ u₁ v₂ u₂ v₃ u₃

/-- **A natural transformation invertible along a diagram is invertible at its colimit.** If
`α : G ⟶ H` is invertible at every object in the image of a diagram `D`, and both `G` and `H`
carry a colimit cocone of `D` to a colimit cocone, then `α` is invertible at the colimit.

The two images of the cocone are colimits of isomorphic diagrams, so their points are
canonically isomorphic, and that isomorphism is `α` at the colimit because both are determined
by the same compatibility with the cocone maps. -/
theorem isIso_app_of_isColimit {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {G H : A ⥤ B} (α : G ⟶ H) {K : Type u₃} [Category.{v₃} K] {D : K ⥤ A} {c : Cocone D}
    (hG : IsColimit (G.mapCocone c)) (hH : IsColimit (H.mapCocone c))
    (h : ∀ k : K, IsIso (α.app (D.obj k))) :
    IsIso (α.app c.pt) := by
  let β : D ⋙ G ≅ D ⋙ H :=
    NatIso.ofComponents (fun k ↦ asIso (α.app (D.obj k))) (fun f ↦ α.naturality (D.map f))
  have key : α.app c.pt = (IsColimit.coconePointsIsoOfNatIso hG hH β).hom := by
    refine hG.hom_ext fun k ↦ ?_
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    exact α.naturality (c.ι.app k)
  rw [key]
  infer_instance

end Stacks.CategoryTheory

namespace Stacks.SheafOfModules

universe u v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {B : Type u₂} [Category.{v₂} B] {G H : _root_.SheafOfModules.{u} R ⥤ B}

/-- **A natural transformation agreeing on the structure sheaf agrees on free modules.** A free
sheaf of modules is a coproduct of copies of the structure sheaf, so a transformation `α` that
is invertible at `SheafOfModules.unit R` is invertible at `SheafOfModules.free I` as soon as
both functors preserve coproducts indexed by `I`. -/
theorem isIso_app_free (α : G ⟶ H) (I : Type u)
    [PreservesColimitsOfShape (Discrete I) G] [PreservesColimitsOfShape (Discrete I) H]
    (hunit : IsIso (α.app (_root_.SheafOfModules.unit R))) :
    IsIso (α.app (_root_.SheafOfModules.free (R := R) I)) :=
  Stacks.CategoryTheory.isIso_app_of_isColimit α
    (isColimitOfPreserves G (_root_.SheafOfModules.isColimitFreeCofan (R := R) I))
    (isColimitOfPreserves H (_root_.SheafOfModules.isColimitFreeCofan (R := R) I))
    (fun _ ↦ hunit)

/-- **A natural transformation agreeing on free modules agrees on a presented module.** A
`SheafOfModules.Presentation` exhibits its module as a cokernel of a map between two free
sheaves of modules, so a transformation invertible at those two free modules is invertible at
the module itself as soon as both functors preserve finite colimits. -/
theorem isIso_app_of_presentation (α : G ⟶ H)
    [PreservesFiniteColimits G] [PreservesFiniteColimits H]
    {M : _root_.SheafOfModules.{u} R} (P : M.Presentation)
    (hgen : IsIso (α.app (_root_.SheafOfModules.free (R := R) P.generators.I)))
    (hrel : IsIso (α.app (_root_.SheafOfModules.free (R := R) P.relations.I))) :
    IsIso (α.app M) := by
  refine Stacks.CategoryTheory.isIso_app_of_isColimit α
    (isColimitOfPreserves G P.isColimit) (isColimitOfPreserves H P.isColimit) ?_
  rintro (_ | _) <;> assumption

/-- **A natural transformation agreeing on the structure sheaf agrees on a presented module.**
The two previous lemmas combined: this is the mechanism both directions of Stacks 0D7M run on,
once a presentation is in hand. -/
theorem isIso_app_of_presentation_of_unit (α : G ⟶ H)
    [PreservesFiniteColimits G] [PreservesFiniteColimits H]
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) G]
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) H]
    (hunit : IsIso (α.app (_root_.SheafOfModules.unit R)))
    {M : _root_.SheafOfModules.{u} R} (P : M.Presentation) :
    IsIso (α.app M) :=
  isIso_app_of_presentation α P (isIso_app_free α _ hunit) (isIso_app_free α _ hunit)

end Stacks.SheafOfModules

namespace CategoryTheory.SimplicialSiteSituation

universe u

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

section Modules

/-- Abelian sheaves on the total site are sheafifiable at the site universe, the total category
being small there. -/
local instance hasWeakSheafifyTotalQuasicoherentCartesian :
    HasWeakSheafify S.totalTopology AddCommGrpCat.{u} :=
  (GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} S.totalTopology).1

/-- On the total site at the site universe, the maps inverted by sheafification of abelian
sheaves are exactly the locally bijective ones. -/
local instance wEqualsLocallyBijectiveTotalQuasicoherentCartesian :
    S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  letI : HasSheafify ((equivSmallModel.{u} (S.totalCategory : Type u)).inverse.inducedTopology
      S.totalTopology) AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u, u + 1, u}
    S.totalTopology

attribute [local instance] hasWeakSheafifyComponent

/-- **The right-hand side of Stacks 0D7M.** A sheaf of `O`-modules on the total site of a
simplicial-site situation is cartesian in the sense of Stacks 07TF (2) and each of its
component modules `F_n` is a quasi-coherent `O_n`-module in the sense of Stacks 03DL (6).

The source asserts that this condition is equivalent to quasi-coherence of `F` itself on the
total site; that equivalence is not proved in this development. -/
@[stacks 0D7M "the right-hand side of the equivalence only: `F` is cartesian in the sense of \
07TF (2) and every component module `F_n` is a quasi-coherent `O_n`-module in the sense of \
03DL (6). Neither direction of the equivalence with quasi-coherence of `F` on the total site \
is proved: both need a localization of the total site at an object, which the development \
does not have"]
noncomputable abbrev IsCartesianWithQuasicoherentComponents
    (F : SheafOfModules.{u} (S.totalRingSheaf O)) : Prop :=
  S.IsCartesianModule O F ∧
    ∀ n : SimplexCategory, (S.componentModule O F n).IsQuasicoherentOnSite

end Modules

end CategoryTheory.SimplicialSiteSituation
