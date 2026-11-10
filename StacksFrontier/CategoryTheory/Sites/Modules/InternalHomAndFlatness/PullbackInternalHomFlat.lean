module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomMapLeftConjugate
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.ExtensionByZeroTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomPullback
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.FlatPullbackExact
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.Basic
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The first variable of the internal Hom sheaf, and the pullback of internal Hom along a flat
morphism

Let `(C, O)` be a ringed site and let `F`, `F'`, `G` be sheaves of `O`-modules. Stacks 03EO
makes tensoring on the right by `F` left adjoint to the internal Hom sheaf `Hom_O(F, -)` of
Stacks 03EM. A morphism `c : F' ⟶ F` therefore gives two comparisons at once: the natural
transformation `- ⊗_O F' ⟶ - ⊗_O F` between the two left adjoints, and its *mate*, a natural
transformation `Hom_O(F, -) ⟶ Hom_O(F', -)` between the two right adjoints. This file builds the
second one, `Stacks.SheafOfModules.InternalHom.internalHomPre`, as that mate, and records the
calculus it comes with.

Taking the comparison in the first variable to be the mate — rather than defining it by hand as
precomposition with `c` on sections — is what makes it interact with the evaluation morphism of
Stacks 03EM by construction: `CategoryTheory.conjugateEquiv_counit` is exactly the identity
`(internalHomPre c ⊗ 𝟙 F') ≫ ev_{F'} = (𝟙 ⊗ c) ≫ ev_F`, which is the one step every argument
about the first variable of internal Hom needs and which no other declaration of this
development supplies at this spelling. With it, the morphism `A ⊗_O F ⟶ G` attached by
`Stacks.SheafOfModules.InternalHom.tensorEvaluation` to a morphism `A ⟶ Hom_O(F, G)` can be
computed after composing with `internalHomPre c`, and
`Stacks.SheafOfModules.InternalHom.tensorEvaluation_injective` then turns any identity between
two morphisms into `Hom_O(F', G)` into an identity between morphisms out of a tensor product.

The file then reads the canonical map of Stacks 0GMX off a morphism of ringed *topoi* rather
than a morphism of ringed sites, and records the two naturality statements that let that map be
moved past a second pullback.

Finally it turns to Stacks 0GN2: the canonical map
`f^* Hom_{O_D}(F, G) ⟶ Hom_{O_C}(f^*F, f^*G)` is an isomorphism for a flat morphism of ringed
sites and a finitely presented `F`. The argument is the formal one of the source. Internal Hom
into a fixed `G`, contravariant in its source, is a functor `Mod(O) ⥤ Mod(O)ᵒᵖ`; the canonical
map is a natural transformation between the two composites of that functor with the pullback; a
finite presentation of `F` is a finite colimit; both composites carry finite colimits to
colimits — the pullback preserves colimits because it is a left adjoint, and it preserves finite
*limits* exactly when `f` is flat, which is what makes the second composite continuous as well —
and so a natural transformation that is invertible at the structure sheaf is invertible at `F`.

The base of that induction, `F = O_D`, is proved here with no hypotheses, as are the
functoriality of the canonical map in its first variable and the continuity of internal Hom in
its first variable — Stacks 03EN, which is available for this functor because the mate
`internalHomPre` is identified with precomposition. The step, for a general `F`, assumes
flatness of `f` and a *global* finite presentation of `F`. The local finite presentation that
the source assumes is reduced to that case by
`isIso_pullbackInternalHomMap_of_isFinitePresentationOnSite`, which states the source's own
hypotheses and carries the 0GN2 tag.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.internalHomPre`: the comparison
  `Hom_O(F, -) ⟶ Hom_O(F', -)` attached to `c : F' ⟶ F`, defined as the mate of `- ⊗_O c`.
* `Stacks.SheafOfModules.InternalHom.toposPullback`,
  `Stacks.SheafOfModules.InternalHom.toposPullbackEvaluation` and
  `Stacks.SheafOfModules.InternalHom.toposPullbackInternalHomMap`: the pullback of sheaves of
  modules, the pulled-back evaluation morphism and the canonical map of Stacks 0GMX, for a
  morphism of ringed topoi between the topoi of two ringed sites.
* `Stacks.SheafOfModules.InternalHom.internalHomSecondFunctorUnitIso`: the clause of
  Stacks 03EM that internal Hom out of the structure sheaf is the identity functor.
* `Stacks.SheafOfModules.InternalHom.internalHomFirstMate` and
  `Stacks.SheafOfModules.InternalHom.internalHomFirstMateLeft`: internal Hom into a fixed sheaf
  of modules, contravariant in its source, as a functor into the opposite category, assembled
  from each of the two mates of a morphism in the first variable.
* `Stacks.SheafOfModules.InternalHom.pullbackInternalHomNatTrans`: the canonical maps of
  Stacks 0GMX assembled into a natural transformation of their first variable.

## Main results

* `Stacks.SheafOfModules.InternalHom.internalHomPre_id` and
  `Stacks.SheafOfModules.InternalHom.internalHomPre_comp`: the comparison is functorial in `c`,
  contravariantly.
* `Stacks.SheafOfModules.InternalHom.isIso_internalHomPre`: it is invertible when `c` is.
* `Stacks.SheafOfModules.InternalHom.homEquiv_comp_sheafInternalHomMapLeft_right` and
  `Stacks.SheafOfModules.InternalHom.internalHomPre_eq_internalHomMapLeftNatTrans`: **the mate
  in the first variable is precomposition.** The comparison of the correspondence of
  Stacks 03EO is contravariantly natural in the internal-Hom source, and that identity pins the
  mate down as `sheafInternalHomMapLeft`.
* `Stacks.SheafOfModules.InternalHom.internalHomFirstMate_preservesColimitsOfShape` and
  `Stacks.SheafOfModules.InternalHom.internalHomFirstMate_preservesFiniteColimits`:
  **Stacks 03EN in the first variable**, at the spelling the proof of Stacks 0GN2 needs.
* `Stacks.SheafOfModules.InternalHom.tensor_internalHomPre_internalHomEvaluation`: the
  comparison is compatible with the evaluation morphism of the internal Hom sheaf. This is the
  mate identity, and it is the only input the rest of the calculus needs.
* `Stacks.SheafOfModules.InternalHom.tensorEvaluation_comp` and
  `Stacks.SheafOfModules.InternalHom.tensorEvaluation_comp_internalHomPre`: the two ways of
  precomposing a morphism into an internal Hom sheaf, read through the correspondence of
  Stacks 03EO.
* `Stacks.SheafOfModules.InternalHom.tensorEvaluation_comp_internalHomSecondFunctor_map`: the
  companion of the previous statement for the second variable.
* `Stacks.SheafOfModules.InternalHom.toposPullbackEvaluation_ringedToposHom` and
  `Stacks.SheafOfModules.InternalHom.toposPullbackInternalHomMap_ringedToposHom`: at the morphism
  of ringed topoi of a morphism of ringed sites the two readings of Stacks 0GMX agree, on the
  nose.
* `Stacks.SheafOfModules.InternalHom.tensorEvaluation_toposPullbackInternalHomMap`: the
  compatibility of the canonical map with evaluation, which by
  `Stacks.SheafOfModules.InternalHom.tensorEvaluation_injective` pins the canonical map down.
* `Stacks.SheafOfModules.InternalHom.pullbackTensorIso_inv_app_naturality_left`: the comparison
  of Stacks 03EL is natural in its first variable, read with the curried tensor product.
* `Stacks.SheafOfModules.InternalHom.toposPullback_tensorEvaluation`: the pullback of a
  tensor--evaluation composite. This is the step that moves the canonical map of Stacks 0GMX
  past a second pullback.
* `Stacks.SheafOfModules.InternalHom.pullbackTensorIso_inv_app_naturality_right`: the companion
  of the previous naturality statement for the second variable.
* `Stacks.SheafOfModules.InternalHom.toposPullbackInternalHomMap_naturality` and
  `Stacks.SheafOfModules.InternalHom.pullbackInternalHomNatural`: the canonical map of
  Stacks 0GMX is functorial in its first variable.
* `Stacks.SheafOfModules.InternalHom.isIso_toposPullbackInternalHomMap_of_isEquivalence` and
  `Stacks.SheafOfModules.InternalHom.isIso_toposPullbackInternalHomMap_unit`: the canonical map
  of Stacks 0GMX is an isomorphism when internal Hom out of its first argument is an
  equivalence on both sites, and in particular when that argument is the structure sheaf.
* `Stacks.SheafOfModules.InternalHom.preservesFiniteColimits_internalHomFirstMate`:
  **Stacks 03EN in the first variable**, for the mate — internal Hom into a fixed sheaf of
  modules carries finite colimits in its source to finite limits. This is proved here with no
  hypothesis, by exhibiting `internalHomFirstMate` as a left adjoint.
* `Stacks.SheafOfModules.InternalHom.preservesFiniteLimits_ringedSitePullback_of_isFlat`:
  **Stacks 04JC for a morphism of ringed sites** — the pullback of sheaves of modules along a
  flat morphism of ringed sites is left exact.
* `Stacks.SheafOfModules.InternalHom.isIso_toposPullbackInternalHomMap_structureSheaf` and
  `Stacks.SheafOfModules.InternalHom.isIso_pullbackInternalHomMap_structureSheaf`:
  **Stacks 0GN2 for `F` the structure sheaf**, with no hypotheses.
* `Stacks.SheafOfModules.InternalHom.isIso_pullbackInternalHomMap`: **Stacks 0GN2** for a
  general `F`, for a flat `f` and a global finite presentation of `F`.

## Implementation notes

The two sites, their morphisms and the sections of their structure sheaves lie in one universe,
for the reason recorded in the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomPullback`.

The comparison *is* identified with the precomposition map
`Stacks.SheafOfModules.InternalHom.sheafInternalHomMapLeft` of
`StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFirstVariable`,
which is the map the left exactness of Stacks 0GMY is stated about, by
`internalHomPre_eq_internalHomMapLeftNatTrans`. The mate is never computed on sections — that
would need the correspondence of Stacks 03EO on pure local tensors, a formula this development
does not have. Instead the conjugate is pinned down by its compatibility with the two
hom-equivalences, `CategoryTheory.conjugateEquiv_eq_of_homEquiv`, and that compatibility is
checked on the *right-handed* correspondence `sheafTensorRightHomAdjunction`, whose
hom-equivalence is the presheaf currying of Stacks 03EO after the unit of module sheafification
on the nose. No braiding is involved, because the precomposition that has to be moved is
`A ⊗_O c`, with `c` in the second tensor factor, which is the variable the presheaf statement
`Stacks.PresheafOfModules.InternalHom.curryGlobal_comp_internalHomMapLeft` is about. (The
left-handed identification `conjugateEquiv_tensoringLeft_map` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomMapLeftConjugate` needs the braiding
for exactly that reason, and it is the braiding that is the obstruction when the
identification is approached from that side.) Nothing else below depends on the identification:
the mate identity replaces it wherever the first variable has to be moved.

The identification is what makes the continuity of internal Hom in its first variable — Tag
03EN, proved in that file as
`Stacks.SheafOfModules.InternalHom.siteInternalHomFirstFunctor_preservesColimitsOfShape` —
available for `internalHomFirstMate`, which is the spelling the proof of Stacks 0GN2 below
needs.

Every statement here about the canonical map of Stacks 0GMX is reached through
`Stacks.SheafOfModules.InternalHom.tensorEvaluation_injective`: an identity between two
morphisms into an internal Hom sheaf is proved by tensoring with the source module and
evaluating. That route never forms a tensor product of more than two factors, so it needs the
comparison of Stacks 03EL only through its naturality in one variable at a time and not through
any associativity coherence — which matters, because the associativity coherence of that
comparison is exactly what the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsMonoidal` record as unavailable, the
transport of trilinear pairings along the inverse image not existing yet. What a composite of
two pullbacks additionally needs is the compatibility of the comparison of Stacks 03EL with
*composition* of morphisms of ringed topoi — the identification of the comparison of
`AlgebraicGeometry.RingedToposHom.comp` with the two comparisons of its factors, conjugated by
`AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso`. That statement is binary too. Its
first two steps, the ones over the target site, are
`Stacks.SheafOfModules.pullbackTensorStep1_comp` and
`Stacks.SheafOfModules.pullbackTensorStep2_comp` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposComp`; beyond them the two
chains are not comparable step by step, since the remaining four steps of the composite's chain
are over `χ⁻¹O_E` on the source site whereas the composite route's are over `ψ⁻¹O_E` on the
middle site and `φ⁻¹O_D` on the source site. What closes that gap in shape is the regrouping of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposCompBilinear`: those four steps
compose to the single base change of bilinear pairings
`Stacks.SheafOfModules.pullbackTensorBilinEquiv`, two links of the composite route then cancel
in pairs, and `Stacks.SheafOfModules.pullbackTensorHomEquiv_comp_iff` makes the composition law
equivalent to one equation — the compatibility of that base change with composition. That
equation is `Stacks.SheafOfModules.pullbackTensorBilinEquiv_comp`, and the composition law it
gives is `Stacks.SheafOfModules.pullbackTensorHomEquiv_comp`. Otherwise
`Stacks.SheafOfModules.pullbackTensorIso` comes with naturality in its two sheaf variables and
with nothing about the morphism variable.

**The scope of what is proved about Stacks 0GN2 here.** For `F` the structure sheaf the
isomorphism is proved outright, with no hypothesis at all, by
`isIso_pullbackInternalHomMap_structureSheaf`: the two inputs the source names at that point are
the identification `f^*O_D = O_C`, which is
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`, and the identity
`Hom_O(O, -) = id` of Stacks 03EM, which is `internalHomSecondFunctorUnitIso`. Flatness plays no
part: the source needs it only to carry a presentation of a general `F` across the pullback.
The first-variable functoriality of the canonical map of Stacks 0GMX, which the source's proof
also cites, is `toposPullbackInternalHomMap_naturality` for a morphism of ringed topoi and
`pullbackInternalHomNatural` for a morphism of ringed sites, likewise unconditional.

For a general `F` the two further inputs the source's proof cites are proved here as well:
Tag 03EN in the first variable is `preservesFiniteColimits_internalHomFirstMate`, and the
exactness of the flat pullback is `preservesFiniteLimits_ringedSitePullback_of_isFlat`, which is
Tag 04JC at the morphism of ringed topoi of `f`. So the only hypotheses
`isIso_pullbackInternalHomMap` carries are flatness of `f` and a presentation of `F`.

**Flatness is read at the morphism of ringed topoi of `f`.** The hypothesis is
`AlgebraicGeometry.SheafOfModules.IsFlatMapULift f.ringedToposHom.fSharpInverseImage`: `O_C` is
flat as an `f⁻¹O_D`-module, with `f⁻¹` the inverse image of the morphism of ringed topoi and
with the rings of sections lifted into a universe containing the site, as Tag 04JB's definition
of a flat morphism requires and as
`Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap`
consumes it. `AlgebraicGeometry.RingedSite.Hom.IsFlat` states the same condition with `f⁻¹`
spelled as `Stacks.SheafOfModules.sheafPullback` along the continuous functor `u` of the
underlying sites instead. The two are not bridged here: the identification needs the comparison
of `Stacks.Sheaves.ToposPullback.inverseImageCommRingFunctor f.toposHom` with
`f.u.sheafPullback CommRingCat`, the commutation of the universe lift of
`AlgebraicGeometry.SheafOfModules.sheafULift` with that inverse image, and transport of
`AlgebraicGeometry.SheafOfModules.IsFlatMap` along the resulting isomorphism of the source
sheaf of rings, none of which this development has.

**The presentation of `F` is a GLOBAL finite presentation**, not the local finite
presentation `SheafOfModules.IsFinitePresentationOnSite` of Tag 03DL that
Stacks 0GN2 assumes: the hypotheses exhibit `F` as a cokernel of a morphism between finite
coproducts of copies of the structure sheaf over the whole site. That is strictly stronger than
the source's hypothesis, so the theorem below is the global special case; the reduction of the
local case to it is carried out in
`PullbackInternalHomFinitePresentation.isIso_pullbackInternalHomMap_of_isFinitePresentationOnSite`,
which is the declaration that carries the 0GN2 tag. Invertibility of a morphism of sheaves of
modules *is* local — `CategoryTheory.Sheaf.isIso_of_coversTop` and
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop` are in place, and the covering
by objects over which `F` has a global presentation comes from Tag 03DL. The two comparisons
that reduction needs are in place as well: the base change `f_V^*(F|_V) ≅ (f^*F)|_{u(V)}` of
Tag 04J0 on sheaves of modules is
`AlgebraicGeometry.RingedSite.Hom.localizedPullbackModulesSquare`, and the localization of
internal Hom of Tag 0E8H is
`Stacks.SheafOfModules.ExtensionByZero.internalHomRestrictionNatIso`.

What is not in place is the step that joins them: recognizing the restriction of the canonical
map of Stacks 0GMX to a localized ringed site as the canonical map of the localized morphism.
Every identity about that map proved here goes through
`tensorEvaluation_injective`, hence through the comparison of Stacks 03EL; and around the
localization square the two sides are the pullbacks along two *composites* of morphisms of
ringed topoi, so the recognition needs the compatibility of Stacks 03EL with composition
discussed above. Of that compatibility three levels are now proved, all in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposCompBilinear`: the law for the
chain of bijections, `Stacks.SheafOfModules.pullbackTensorHomEquiv_comp`; the law for the
comparison morphism, `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp`; and the law for the
*inverse* comparison, `Stacks.SheafOfModules.pullbackTensorIso_inv_app_comp`, which is the
direction the canonical map of Stacks 0GMX is built from, `toposPullbackEvaluation` being
`(pullbackTensorIso _).inv.app _` followed by the pullback of the evaluation morphism. Each of
those statements takes the composite as data — a third morphism of ringed topoi with a
comparison `τ` of the geometric direct images carrying the composite structure map to its own,
the four-field morphism of ringed topoi having no composition — and for a genuine composite that
data is `AlgebraicGeometry.RingedToposHom.toModulesHomPushforwardIso` together with
`AlgebraicGeometry.RingedToposHom.fSharpSetComp_toModulesHomPushforwardIso` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompProvider`.

What the recognition needs beyond all of that is the law one level up again: the canonical map
of Stacks 0GMX is reached from the comparison of Stacks 03EL only through
`tensorEvaluation_injective`, so carrying the law to the canonical map of a composite is a
further step, which this development does not take. Until it is taken a local presentation gives
no information about the global canonical map.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)

namespace Stacks.SheafOfModules.InternalHom

universe u

private theorem map_comp_of_commutative_square
    {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D)
    {A B E : C} {X Y : D} {s : X ⟶ Y} {t : Y ⟶ L.obj B}
    {r : X ⟶ L.obj A} {f : A ⟶ B}
    (h : s ≫ t = r ≫ L.map f) (g : B ⟶ E) :
    s ≫ t ≫ L.map g = r ≫ L.map (f ≫ g) := by
  rw [← Category.assoc, h, Category.assoc, ← L.map_comp]

section FirstVariable

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u})

/-- The comparison `Hom_O(F, -) ⟶ Hom_O(F', -)` of internal Hom sheaves attached to a morphism
`c : F' ⟶ F` of sheaves of `O`-modules: the mate of the comparison `- ⊗_O F' ⟶ - ⊗_O F` of the
two left adjoints of the correspondence of Stacks 03EO.

Read on sections this is precomposition with `c`, but it is built as the mate so that its
compatibility with the evaluation morphism of Stacks 03EM,
`tensor_internalHomPre_internalHomEvaluation`, is the defining property of a mate rather than a
computation on local sections. -/
@[ega "0 4.1.5" "partial"]
def internalHomPre
    {F F' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (c : F' ⟶ F) :
    internalHomSecondFunctor J O F ⟶ internalHomSecondFunctor J O F' :=
  conjugateEquiv (sheafTensorRightHomAdjunction O F) (sheafTensorRightHomAdjunction O F')
    ((sheafTensor.{u, u, u, u, u} O).flip.map c)

/-- The comparison in the first variable is the identity at the identity. -/
theorem internalHomPre_id
    (F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    internalHomPre O (𝟙 F) = 𝟙 (internalHomSecondFunctor J O F) :=
  (congrArg (conjugateEquiv (sheafTensorRightHomAdjunction O F)
      (sheafTensorRightHomAdjunction O F)) ((sheafTensor.{u, u, u, u, u} O).flip.map_id F)).trans
    (conjugateEquiv_id _)

/-- The comparison in the first variable is contravariantly functorial. -/
theorem internalHomPre_comp
    {F F' F'' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (c : F'' ⟶ F') (d : F' ⟶ F) :
    internalHomPre O d ≫ internalHomPre O c = internalHomPre O (c ≫ d) :=
  (conjugateEquiv_comp (sheafTensorRightHomAdjunction O F)
    (sheafTensorRightHomAdjunction O F') (sheafTensorRightHomAdjunction O F'')
    ((sheafTensor.{u, u, u, u, u} O).flip.map d) ((sheafTensor.{u, u, u, u, u} O).flip.map c)).trans
      (congrArg (conjugateEquiv (sheafTensorRightHomAdjunction O F)
        (sheafTensorRightHomAdjunction O F''))
        ((sheafTensor.{u, u, u, u, u} O).flip.map_comp c d).symm)

/-- The comparison in the first variable along an isomorphism is an isomorphism. -/
instance isIso_internalHomPre
    {F F' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (c : F' ⟶ F) [IsIso c] : IsIso (internalHomPre O c) :=
  ⟨internalHomPre O (inv c), by
      rw [internalHomPre_comp, IsIso.inv_hom_id, internalHomPre_id], by
      rw [internalHomPre_comp, IsIso.hom_inv_id, internalHomPre_id]⟩

section Precomposition

open MonoidalCategory

attribute [local instance] Stacks.SheafOfModules.Tensor.ringSheafPresheafMonoidalCategory

/-- **The hom-equivalence of the correspondence of Stacks 03EO is contravariantly natural in
the internal-Hom source.** Transposing `f : A ⊗_O F ⟶ H` across the correspondence for `F` and
then precomposing by `c : F' ⟶ F` on the internal Hom sheaf is transposing `(A ⊗_O c) ≫ f`
across the correspondence for `F'`.

Both transposes are the presheaf currying of Stacks 03EO after the unit of module
sheafification — the right-handed correspondence `sheafTensorRightHomAdjunction` is built from
the presheaf clause directly, so no braiding and no re-seating intervene and the two readings
hold by `rfl`. What remains is the presheaf statement
`Stacks.PresheafOfModules.InternalHom.curryGlobal_comp_internalHomMapLeft` together with the
naturality of the sheafification hom-equivalence in its source. -/
theorem homEquiv_comp_sheafInternalHomMapLeft_right
    {F F' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)} (c : F' ⟶ F)
    (A H : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))
    (f : ((sheafTensor.{u, u, u, u, u} O).flip.obj F).obj A ⟶ H) :
    (sheafTensorRightHomAdjunction O F).homEquiv A H f ≫ sheafInternalHomMapLeft J O c =
      (sheafTensorRightHomAdjunction O F').homEquiv A H
        (((sheafTensor.{u, u, u, u, u} O).flip.map c).app A ≫ f) := by
  have hnat : (sheafifyForgetAdjunction O).homEquiv _ H
        (((sheafTensor.{u, u, u, u, u} O).flip.map c).app A ≫ f) =
      (A.val ◁ c.val) ≫ (sheafifyForgetAdjunction O).homEquiv _ H f :=
    Adjunction.homEquiv_naturality_left (sheafifyForgetAdjunction O) (A.val ◁ c.val) f
  refine SheafOfModules.hom_ext ?_
  have e1 : ((sheafTensorRightHomAdjunction O F).homEquiv A H f ≫
        sheafInternalHomMapLeft J O c).val =
      Stacks.PresheafOfModules.InternalHom.curryGlobal O.obj A.val F.val H.val
          ((sheafifyForgetAdjunction O).homEquiv _ H f) ≫
        Stacks.PresheafOfModules.InternalHom.internalHomMapLeft O.obj c.val := rfl
  have e2 : ((sheafTensorRightHomAdjunction O F').homEquiv A H
        (((sheafTensor.{u, u, u, u, u} O).flip.map c).app A ≫ f)).val =
      Stacks.PresheafOfModules.InternalHom.curryGlobal O.obj A.val F'.val H.val
        ((sheafifyForgetAdjunction O).homEquiv _ H
          (((sheafTensor.{u, u, u, u, u} O).flip.map c).app A ≫ f)) := rfl
  rw [e1, e2]
  refine Eq.trans
    (Stacks.PresheafOfModules.InternalHom.curryGlobal_comp_internalHomMapLeft
      O.obj A.val H.val c.val _) ?_
  refine congrArg
    (Stacks.PresheafOfModules.InternalHom.curryGlobal O.obj A.val F'.val H.val) ?_
  exact hnat.symm

/-- **The mate in the first variable is precomposition.** The comparison `internalHomPre`,
defined as the mate of `- ⊗_O c`, is the precomposition map `sheafInternalHomMapLeft` of
`StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFirstVariable`.

A conjugate transformation is pinned down by its compatibility with the two hom-equivalences,
`CategoryTheory.conjugateEquiv_eq_of_homEquiv`, and that compatibility is
`homEquiv_comp_sheafInternalHomMapLeft_right`. The mate is therefore identified without ever
computing it on sections. -/
theorem internalHomPre_eq_internalHomMapLeftNatTrans
    {F F' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)} (c : F' ⟶ F) :
    internalHomPre O c = internalHomMapLeftNatTrans O c :=
  conjugateEquiv_eq_of_homEquiv _ _ _ _
    (fun A H f => homEquiv_comp_sheafInternalHomMapLeft_right O c A H f)

/-- The same identification at a fixed target: the component of the mate at `H` is
precomposition by `c` on the internal Hom sheaves with target `H`. -/
theorem internalHomPre_app_eq_sheafInternalHomMapLeft
    {F F' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)} (c : F' ⟶ F)
    (H : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    (internalHomPre O c).app H = sheafInternalHomMapLeft J O c :=
  congrArg (fun γ => NatTrans.app γ H) (internalHomPre_eq_internalHomMapLeftNatTrans O c)

end Precomposition

/-- **The comparison in the first variable is compatible with evaluation.** Tensoring
`internalHomPre O c` with `F'` and then evaluating `Hom_O(F', H)` is the same as tensoring `c`
into the second factor and then evaluating `Hom_O(F, H)`.

This is the identity that characterizes the mate of `- ⊗_O c`, and it is the statement that
makes the first variable of the internal Hom sheaf usable: it is what lets the source module be
moved along `c` underneath an evaluation. -/
theorem tensor_internalHomPre_internalHomEvaluation
    {F F' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)} (c : F' ⟶ F)
    (H : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    ((sheafTensor.{u, u, u, u, u} O).map ((internalHomPre O c).app H)).app F' ≫
        internalHomEvaluation O F' H =
      ((sheafTensor.{u, u, u, u, u} O).obj ((internalHomSecondFunctor J O F).obj H)).map c ≫
        internalHomEvaluation O F H :=
  conjugateEquiv_counit (sheafTensorRightHomAdjunction O F)
    (sheafTensorRightHomAdjunction O F') _ H

/-- Tensoring and evaluating is contravariantly functorial in the morphism into the internal
Hom sheaf: precomposing with `ψ` tensors `ψ` into the first factor. -/
theorem tensorEvaluation_comp
    {A A' F H : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (ψ : A ⟶ A') (χ : A' ⟶ (internalHomSecondFunctor J O F).obj H) :
    tensorEvaluation O F H (ψ ≫ χ) =
      ((sheafTensor.{u, u, u, u, u} O).map ψ).app F ≫ tensorEvaluation O F H χ :=
  (congrArg (fun morphism => NatTrans.app morphism F ≫ internalHomEvaluation O F H)
    ((sheafTensor.{u, u, u, u, u} O).map_comp ψ χ)).trans (Category.assoc _ _ _)

/-- Tensoring and evaluating after the comparison in the first variable tensors `c` into the
second factor. Together with `tensorEvaluation_injective` this is how an identity between two
morphisms into `Hom_O(F', H)` is reduced to an identity between morphisms out of a tensor
product. -/
theorem tensorEvaluation_comp_internalHomPre
    {A F F' H : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (c : F' ⟶ F) (ψ : A ⟶ (internalHomSecondFunctor J O F).obj H) :
    tensorEvaluation O F' H (ψ ≫ (internalHomPre O c).app H) =
      ((sheafTensor.{u, u, u, u, u} O).obj A).map c ≫ tensorEvaluation O F H ψ :=
  (tensorEvaluation_comp O ψ ((internalHomPre O c).app H)).trans
    ((congrArg (fun morphism => ((sheafTensor.{u, u, u, u, u} O).map ψ).app F' ≫ morphism)
      (tensor_internalHomPre_internalHomEvaluation O c H)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun morphism => morphism ≫ internalHomEvaluation O F H)
            (((sheafTensor.{u, u, u, u, u} O).map ψ).naturality c).symm).trans
              (Category.assoc _ _ _))))

/-- Tensoring and evaluating is covariantly functorial in the target of the internal Hom sheaf:
postcomposing a morphism into `Hom_O(F, H)` with the functorial action of `Hom_O(F, -)` on
`h : H ⟶ H'` postcomposes `h`.

This is naturality of the counit of the correspondence of Stacks 03EO, and it is the companion
of `tensorEvaluation_comp_internalHomPre` for the second variable. -/
theorem tensorEvaluation_comp_internalHomSecondFunctor_map
    {A F H H' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (h : H ⟶ H') (ψ : A ⟶ (internalHomSecondFunctor J O F).obj H) :
    tensorEvaluation O F H' (ψ ≫ (internalHomSecondFunctor J O F).map h) =
      tensorEvaluation O F H ψ ≫ h :=
  (tensorEvaluation_comp O ψ ((internalHomSecondFunctor J O F).map h)).trans
    ((congrArg (fun morphism => ((sheafTensor.{u, u, u, u, u} O).map ψ).app F ≫ morphism)
      ((sheafTensorRightHomAdjunction.{u, u} O F).counit_naturality h)).trans
        (Category.assoc _ _ _).symm)

end FirstVariable

section ToposPullback

/-! ## The canonical map of Stacks 0GMX for a morphism of ringed topoi

The canonical map of Stacks 0GMX is built from data of two kinds: the internal Hom sheaf and the
tensor--internal-Hom correspondence, which need the two ringed *sites*, and the pullback of
sheaves of modules together with the comparison of Stacks 03EL, which need only the morphism of
ringed *topoi* that a morphism of ringed sites determines. Taking that morphism of ringed topoi
as the argument therefore costs nothing and gains the composition and 2-isomorphism calculus of
`AlgebraicGeometry.RingedToposHom`, which a morphism of ringed sites does not have: a
localization morphism `j_U : (Sh(C/U), O_U) ⟶ (Sh(C), O)` is a morphism of ringed topoi and is
*not* induced by any morphism of sites in that direction, so every square built from a
localization lives at this level and nowhere else. -/

variable {X Y : RingedSite.{u, u, u}}

/-- The pullback of sheaves of modules along a morphism of ringed topoi between the topoi of two
ringed sites. This is `Stacks.SheafOfModules.InternalHom.ringedSitePullback` with the morphism of
ringed topoi supplied directly rather than read off a morphism of ringed sites. -/
abbrev toposPullback (φ : RingedToposHom (RingedSite.ringedTopos X) (RingedSite.ringedTopos Y)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules (X := RingedSite.ringedTopos X)
    (Y := RingedSite.ringedTopos Y) φ.toModulesHom

variable (φ : RingedToposHom (RingedSite.ringedTopos X) (RingedSite.ringedTopos Y))
  (F G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))

/-- The pullback of the evaluation morphism of `Hom_{O_Y}(F, G)` along a morphism of ringed
topoi, read as a morphism out of the tensor product of the pullbacks through the comparison of
Stacks 03EL. -/
def toposPullbackEvaluation :
    ((sheafTensor.{u, u, u, u, u} X.O).obj
          ((toposPullback φ).obj ((internalHomSecondFunctor Y.J Y.O F).obj G))).obj
        ((toposPullback φ).obj F) ⟶
      (toposPullback φ).obj G :=
  (pullbackTensorIso φ.toModulesHom).inv.app
      ((internalHomSecondFunctor Y.J Y.O F).obj G, F) ≫
    (toposPullback φ).map (internalHomEvaluation Y.O F G)

/-- **Stacks 0GMX for a morphism of ringed topoi.** The canonical map
`φ^* Hom_{O_Y}(F, G) ⟶ Hom_{O_X}(φ^*F, φ^*G)`: the transpose, under the correspondence of
Stacks 03EO, of the pullback of the evaluation morphism. -/
def toposPullbackInternalHomMap :
    (toposPullback φ).obj ((internalHomSecondFunctor Y.J Y.O F).obj G) ⟶
      (internalHomSecondFunctor X.J X.O ((toposPullback φ).obj F)).obj
        ((toposPullback φ).obj G) :=
  sheafTensorHomEquiv X.O
    ((toposPullback φ).obj ((internalHomSecondFunctor Y.J Y.O F).obj G))
    ((toposPullback φ).obj F) ((toposPullback φ).obj G) (toposPullbackEvaluation φ F G)

/-- At the morphism of ringed topoi of a morphism of ringed sites, the pulled-back evaluation
morphism of this section is the one of
`StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomPullback`. -/
theorem toposPullbackEvaluation_ringedToposHom (f : RingedSite.Hom X Y) :
    toposPullbackEvaluation f.ringedToposHom F G = pullbackEvaluation f F G := rfl

/-- At the morphism of ringed topoi of a morphism of ringed sites, the canonical map of this
section is the canonical map of Stacks 0GMX. -/
theorem toposPullbackInternalHomMap_ringedToposHom (f : RingedSite.Hom X Y) :
    toposPullbackInternalHomMap f.ringedToposHom F G = pullbackInternalHomMap f F G := rfl

/-- **Stacks 0GMX for a morphism of ringed topoi**: the canonical map is compatible with
evaluation. -/
theorem tensorEvaluation_toposPullbackInternalHomMap :
    tensorEvaluation X.O ((toposPullback φ).obj F) ((toposPullback φ).obj G)
        (toposPullbackInternalHomMap φ F G) =
      toposPullbackEvaluation φ F G :=
  (tensorEvaluation_eq X.O ((toposPullback φ).obj F) ((toposPullback φ).obj G)
      (toposPullbackInternalHomMap φ F G)).trans
    ((sheafTensorHomEquiv X.O
        ((toposPullback φ).obj ((internalHomSecondFunctor Y.J Y.O F).obj G))
        ((toposPullback φ).obj F)
        ((toposPullback φ).obj G)).symm_apply_apply (toposPullbackEvaluation φ F G))

/-- The comparison of Stacks 03EL is natural in its first variable, read with the curried tensor
product that the correspondence of Stacks 03EO is stated with rather than with the bifunctor on
the product category that Stacks 03EL is stated with. -/
theorem pullbackTensorIso_inv_app_naturality_left
    {A A' B : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)}
    (a : A ⟶ A') :
    ((sheafTensor.{u, u, u, u, u} X.O).map ((toposPullback φ).map a)).app
        ((toposPullback φ).obj B) ≫
        (pullbackTensorIso φ.toModulesHom).inv.app (A', B) =
      (pullbackTensorIso φ.toModulesHom).inv.app (A, B) ≫
        (toposPullback φ).map (((sheafTensor.{u, u, u, u, u} Y.O).map a).app B) := by
  simpa [-Tensor.sheafTensor_obj_map] using
    (pullbackTensorIso φ.toModulesHom).inv.naturality (Prod.mkHom a (𝟙 B))

/-- **The pullback of a tensor--evaluation composite.** Let `a : A ⟶ Hom_{O_Y}(F, G)` be a
morphism of sheaves of `O_Y`-modules. Tensoring its pullback with `φ^*F` and then evaluating
`Hom_{O_Y}(F, G)` after pullback is the comparison of Stacks 03EL followed by the pullback of the
morphism `A ⊗_{O_Y} F ⟶ G` that the correspondence of Stacks 03EO attaches to `a`.

This is the one computation the first variable of the internal Hom sheaf has to supply in order
for the canonical map of Stacks 0GMX to be moved past a second pullback, and it uses nothing
about the tensor product beyond the naturality of the comparison of Stacks 03EL in one variable
at a time: the tensor products appearing are all of exactly two factors, so no associativity
coherence of the comparison is involved. -/
theorem toposPullback_tensorEvaluation
    {A F' G' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)}
    (a : A ⟶ (internalHomSecondFunctor Y.J Y.O F').obj G') :
    ((sheafTensor.{u, u, u, u, u} X.O).map ((toposPullback φ).map a)).app
        ((toposPullback φ).obj F') ≫
        toposPullbackEvaluation φ F' G' =
      (pullbackTensorIso φ.toModulesHom).inv.app (A, F') ≫
        (toposPullback φ).map (tensorEvaluation Y.O F' G' a) := by
  simp only [toposPullbackEvaluation, tensorEvaluation]
  exact map_comp_of_commutative_square (toposPullback φ)
    (pullbackTensorIso_inv_app_naturality_left φ a) (internalHomEvaluation Y.O F' G')

end ToposPullback

section Flat

/-! ## Stacks 0GN2: the canonical map is an isomorphism for a flat morphism and a finitely
presented source

The argument of the source is formal once the two sides of the canonical map are read as
functors of the first variable. Internal Hom into a fixed sheaf of modules is a functor
`Mod(O) ⥤ Mod(O)ᵒᵖ` — `Stacks.SheafOfModules.InternalHom.internalHomFirstMate`, built from the
comparison `internalHomPre` of this file — and the canonical map of Stacks 0GMX is a natural
transformation between the two composites

`F ↦ Hom_{O_C}(f^*F, f^*G)` and `F ↦ f^* Hom_{O_D}(F, G)`

of that functor with the pullback, by `pullbackInternalHomNatural`. A sheaf of
modules of finite presentation is, locally, a cokernel of a morphism between finite coproducts
of copies of the structure sheaf; both composites carry such a finite colimit to a colimit —
the pullback preserves colimits because it is a left adjoint, and it preserves finite *limits*
exactly when `f` is flat, which is what makes the second composite continuous as well — so a
natural transformation that is invertible at the structure sheaf is invertible at `F`. -/

open CategoryTheory.Limits

section FirstVariableFunctor

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u})
  (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))

/-- Internal Hom into a fixed sheaf of modules `G`, contravariant in its source, assembled from
the comparison `Stacks.SheafOfModules.InternalHom.internalHomPre` in the first variable.

It is directed into the *opposite* category rather than out of it, so that the assertion of
Stacks 03EN in the first variable — colimits of sheaves of modules go to limits of internal Hom
sheaves — reads as preservation of colimits, and so that the canonical map of Stacks 0GMX is a
natural transformation between two functors on `Mod(O_D)` rather than a comparison between a
covariant and a contravariant one. -/
@[sga "4 IV 12.2" "partial"]
def internalHomFirstMate :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) ⥤
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))ᵒᵖ where
  obj F := Opposite.op ((internalHomSecondFunctor J O F).obj G)
  map c := ((internalHomPre O c).app G).op
  map_id F := congrArg Quiver.Hom.op
    (congrArg (fun γ ↦ NatTrans.app γ G) (internalHomPre_id O F))
  map_comp c d := by
    rw [← op_comp]
    exact congrArg Quiver.Hom.op
      (congrArg (fun γ ↦ NatTrans.app γ G) (internalHomPre_comp O c d)).symm

/-- `internalHomFirstMate` is the functor `siteInternalHomFirstFunctor` of
`StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFirstVariable`:
the two have the same values, and their functorial actions agree by
`internalHomPre_app_eq_sheafInternalHomMapLeft`. -/
def internalHomFirstMateIso :
    internalHomFirstMate O G ≅ siteInternalHomFirstFunctor J O G :=
  NatIso.ofComponents (fun F => Iso.refl ((internalHomFirstMate O G).obj F))
    (fun {_ _} c =>
      (Category.comp_id _).trans
        ((congrArg Quiver.Hom.op (internalHomPre_app_eq_sheafInternalHomMapLeft O c G)).trans
          (Category.id_comp _).symm))

/-- **Stacks 03EN in the first variable, at the mate spelling.** Internal Hom into a fixed
sheaf of modules carries colimits of its source to limits.

This is `siteInternalHomFirstFunctor_preservesColimitsOfShape` transported along
`internalHomFirstMateIso`; there the functor is its own left adjoint, through the symmetry
`Hom_O(A, Hom_O(B, G)) ≃ Hom_O(B, Hom_O(A, G))` of the internal Hom sheaf in its two
arguments. -/
@[sga "4 IV 12.2" "partial, special case"]
instance internalHomFirstMate_preservesColimitsOfShape (I : Type*) [Category I] :
    PreservesColimitsOfShape I (internalHomFirstMate O G) :=
  preservesColimitsOfShape_of_natIso (internalHomFirstMateIso O G).symm

/-- Internal Hom into a fixed sheaf of modules, as a functor into the opposite category,
preserves finite colimits. -/
instance internalHomFirstMate_preservesFiniteColimits :
    PreservesFiniteColimits (internalHomFirstMate O G) :=
  ⟨fun _ _ _ => inferInstance⟩

/-- Tensoring the identity of the internal Hom sheaf and evaluating is the evaluation
morphism. -/
theorem tensorEvaluation_id
    (F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    tensorEvaluation O F G (𝟙 ((internalHomSecondFunctor J O F).obj G)) =
      internalHomEvaluation O F G :=
  (congrArg (fun morphism => NatTrans.app morphism F ≫ internalHomEvaluation O F G)
    ((sheafTensor.{u, u, u, u, u} O).map_id ((internalHomSecondFunctor J O F).obj G))).trans
      (Category.id_comp _)

end FirstVariableFunctor

section FirstMateContinuity

/-! ### Stacks 03EN in the first variable, for the mate

Internal Hom into a fixed `G` is adjoint to its own left opposite, so it carries colimits in its
first variable to limits. The pairing `Hom(A ⊗_O B, G)` is symmetric in `A` and `B`, and the two
readings of that symmetry are the two tensor--internal-Hom correspondences of Stacks 03EO that
this development proves separately: `sheafTensorRightHomAdjunction` for `- ⊗_O A` and
`Stacks.SheafOfModules.ExtensionByZero.sheafTensorHomAdjunction` for `B ⊗_O -`. They share a
right adjoint and their left adjoints agree on objects, so composing one hom-equivalence with
the inverse of the other transposes a morphism `B ⟶ Hom_O(A, G)` into a morphism
`A ⟶ Hom_O(B, G)` with no braiding.

The two naturality squares of that transposition are the two mate identities of
`CategoryTheory.homEquiv_comp_conjugateEquiv`, one for each of the two correspondences, and
they land on the two different mates of a morphism in the first variable: the right-handed one
is `internalHomPre` by definition, the left-handed one is
`Stacks.SheafOfModules.ExtensionByZero.internalHomSecondFunctorMapLeft` by
`Stacks.SheafOfModules.ExtensionByZero.conjugateEquiv_sheafTensor_map`. So the adjunction
obtained is between the functor built from `internalHomPre` and the left opposite of the functor
built from `internalHomSecondFunctorMapLeft`; identifying the two mates — which is the braiding
compatibility the implementation notes record as unavailable — is not needed, because an
adjunction between them already makes the left one continuous. -/

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u}) (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))

/-- Tensoring on the left by a sheaf of modules is left adjoint to internal Hom out of it: the
tensor--internal-Hom correspondence of Stacks 03EO in the handedness opposite to the one
`sheafTensorRightHomAdjunction` is stated in, abbreviated for use below. -/
@[sga "4 IV 12.8" "partial, special case"]
private abbrev tensorLeftHomAdjunction
    (B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (sheafTensor O).obj B ⊣ internalHomSecondFunctor J O B :=
  _root_.Stacks.SheafOfModules.ExtensionByZero.sheafTensorHomAdjunction J O B

/-- The comparison in the first variable, read as the mate of the comparison
`F ⊗_O - ⟶ F' ⊗_O -` of the *left*-handed tensor--internal-Hom correspondence of Stacks 03EO,
is the identity at the identity. -/
private theorem mapLeft_id (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    _root_.Stacks.SheafOfModules.ExtensionByZero.internalHomSecondFunctorMapLeft J O (𝟙 F) =
      𝟙 (internalHomSecondFunctor J O F) := by
  rw [← _root_.Stacks.SheafOfModules.ExtensionByZero.conjugateEquiv_sheafTensor_map J O (𝟙 F),
    CategoryTheory.Functor.map_id]
  exact conjugateEquiv_id _

/-- The left-handed comparison in the first variable is contravariantly functorial. -/
private theorem mapLeft_comp
    {F F' F'' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (c : F ⟶ F') (d : F' ⟶ F'') :
    _root_.Stacks.SheafOfModules.ExtensionByZero.internalHomSecondFunctorMapLeft J O d ≫
        _root_.Stacks.SheafOfModules.ExtensionByZero.internalHomSecondFunctorMapLeft J O c =
      _root_.Stacks.SheafOfModules.ExtensionByZero.internalHomSecondFunctorMapLeft J O
        (c ≫ d) := by
  rw [← _root_.Stacks.SheafOfModules.ExtensionByZero.conjugateEquiv_sheafTensor_map J O d,
    ← _root_.Stacks.SheafOfModules.ExtensionByZero.conjugateEquiv_sheafTensor_map J O c,
    ← _root_.Stacks.SheafOfModules.ExtensionByZero.conjugateEquiv_sheafTensor_map J O (c ≫ d),
    conjugateEquiv_comp, ← CategoryTheory.Functor.map_comp]

/-- Internal Hom into a fixed sheaf of modules `G`, contravariant in its source, assembled from
the *left*-handed comparison
`Stacks.SheafOfModules.ExtensionByZero.internalHomSecondFunctorMapLeft` in the first variable.

This is `Stacks.SheafOfModules.InternalHom.internalHomFirstMate` with the other of the two
mates of a morphism in the first variable. It is directed into the opposite category for the
same reason, and it serves as the right adjoint of `internalHomFirstMate` below. -/
@[sga "4 IV 12.2" "partial"]
def internalHomFirstMateLeft :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))ᵒᵖ where
  obj F := Opposite.op ((internalHomSecondFunctor J O F).obj G)
  map c := ((_root_.Stacks.SheafOfModules.ExtensionByZero.internalHomSecondFunctorMapLeft
    J O c).app G).op
  map_id F := by
    exact congrArg Quiver.Hom.op
      (congrArg (fun γ ↦ NatTrans.app γ G) (mapLeft_id O F))
  map_comp c d := by
    rw [← op_comp]
    exact congrArg Quiver.Hom.op
      (congrArg (fun γ ↦ NatTrans.app γ G) (mapLeft_comp O c d)).symm

/-- **The symmetry of the internal Hom pairing.** A morphism `B ⟶ Hom_O(A, G)` is the same
thing as a morphism `A ⟶ Hom_O(B, G)`: both are the transpose of a morphism
`A ⊗_O B ⟶ G`, through the two handednesses of the correspondence of Stacks 03EO. -/
private def mateTranspose (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (B ⟶ (internalHomSecondFunctor J O A).obj G) ≃
      (A ⟶ (internalHomSecondFunctor J O B).obj G) :=
  ((sheafTensorRightHomAdjunction O A).homEquiv B G).symm.trans
    ((tensorLeftHomAdjunction O B).homEquiv A G)

/-- The transposition is natural in the source of the morphism it is applied to: precomposing
with `f : A' ⟶ A` before transposing is transposing and then applying the comparison
`internalHomPre` in the first variable.

This is the mate identity of the right-handed correspondence of Stacks 03EO, and
`internalHomPre` appears because it *is* the mate for that handedness, by definition. -/
private theorem mateTranspose_symm_naturality
    {A A' B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (f : A' ⟶ A)
    (g : A ⟶ (internalHomSecondFunctor J O B).obj G) :
    (mateTranspose O G A' B).symm (f ≫ g) =
      (mateTranspose O G A B).symm g ≫ (internalHomPre O f).app G := by
  have h1 : (mateTranspose O G A' B).symm (f ≫ g) =
      ((sheafTensorRightHomAdjunction O A').homEquiv B G)
        (((tensorLeftHomAdjunction O B).homEquiv A' G).symm (f ≫ g)) := rfl
  have h2 : (mateTranspose O G A B).symm g =
      ((sheafTensorRightHomAdjunction O A).homEquiv B G)
        (((tensorLeftHomAdjunction O B).homEquiv A G).symm g) := rfl
  rw [h1, h2, (tensorLeftHomAdjunction O B).homEquiv_naturality_left_symm]
  exact (CategoryTheory.homEquiv_comp_conjugateEquiv
    (sheafTensorRightHomAdjunction.{u, u} O A) (sheafTensorRightHomAdjunction.{u, u} O A')
    ((sheafTensor O).flip.map f) B G _).symm

/-- The transposition is natural in the target of the morphism it is applied to: precomposing
with `b : B' ⟶ B` before transposing is transposing and then applying the left-handed
comparison in the first variable.

This is the mate identity of the left-handed correspondence of Stacks 03EO, whose mate is
`Stacks.SheafOfModules.ExtensionByZero.internalHomSecondFunctorMapLeft` by
`Stacks.SheafOfModules.ExtensionByZero.conjugateEquiv_sheafTensor_map`. -/
private theorem mateTranspose_naturality
    {A B B' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (b : B' ⟶ B)
    (ψ : B ⟶ (internalHomSecondFunctor J O A).obj G) :
    mateTranspose O G A B' (b ≫ ψ) =
      mateTranspose O G A B ψ ≫
        (_root_.Stacks.SheafOfModules.ExtensionByZero.internalHomSecondFunctorMapLeft
          J O b).app G := by
  dsimp only [mateTranspose, Equiv.trans_apply]
  refine (congrArg ((tensorLeftHomAdjunction O B').homEquiv A G)
    ((sheafTensorRightHomAdjunction.{u, u} O A).homEquiv_naturality_left_symm b ψ)).trans ?_
  have h := (CategoryTheory.homEquiv_comp_conjugateEquiv
    (tensorLeftHomAdjunction O B) (tensorLeftHomAdjunction O B')
    ((sheafTensor O).map b) A G
    (((sheafTensorRightHomAdjunction.{u, u} O A).homEquiv B G).symm ψ)).symm
  refine h.trans ?_
  exact congrArg (fun α : internalHomSecondFunctor J O B ⟶
      internalHomSecondFunctor J O B' ↦
    ((tensorLeftHomAdjunction O B).homEquiv A G)
      (((sheafTensorRightHomAdjunction.{u, u} O A).homEquiv B G).symm ψ) ≫ α.app G)
    (_root_.Stacks.SheafOfModules.ExtensionByZero.conjugateEquiv_sheafTensor_map J O b)

/-- The symmetry of the internal Hom pairing, read as the hom-equivalence of the adjunction
`internalHomFirstMateAdjunction`. -/
private def firstMateHomEquiv (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (Y : (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))ᵒᵖ) :
    ((internalHomFirstMate O G).obj A ⟶ Y) ≃
      (A ⟶ (internalHomFirstMateLeft O G).leftOp.obj Y) where
  toFun φ := mateTranspose O G A Y.unop φ.unop
  invFun χ := ((mateTranspose O G A Y.unop).symm χ).op
  left_inv φ :=
    Quiver.Hom.unop_inj ((mateTranspose O G A Y.unop).symm_apply_apply φ.unop)
  right_inv χ := (mateTranspose O G A Y.unop).apply_symm_apply χ

/-- **The symmetry of the internal Hom pairing, as an adjunction.** Internal Hom into `G`,
contravariant in its source and read into the opposite category, is left adjoint to the left
opposite of the same construction built from the other mate.

The unit and counit are not computed: the hom-equivalence is the transposition
`mateTranspose`, and its two naturality squares are the mate identities of the two
correspondences of Stacks 03EO. -/
private def internalHomFirstMateAdjunction :
    internalHomFirstMate O G ⊣ (internalHomFirstMateLeft O G).leftOp :=
  Adjunction.mkOfHomEquiv
    { homEquiv := firstMateHomEquiv O G
      homEquiv_naturality_left_symm := by
        intro A' A Y f g
        exact Quiver.Hom.unop_inj (mateTranspose_symm_naturality O G f g)
      homEquiv_naturality_right := by
        intro A Y Y' f g
        exact mateTranspose_naturality O G g.unop f.unop }

/-- **Stacks 03EN in the first variable, for the mate.** Internal Hom into a fixed sheaf of
modules, contravariant in its source, carries finite colimits of sheaves of modules to finite
limits of internal Hom sheaves.

This is the continuity that the proof of Stacks 0GN2 uses to pass from the structure sheaf to a
finitely presented source, and it holds with no hypothesis: `internalHomFirstMate` is a left
adjoint, by `internalHomFirstMateAdjunction`. -/
@[stacks 03EN "sheaf case, first variable, for the mate of the tensor comparison",
  ega "0 6.7.6" "Left exactness of Hom(-", sga "4 IV 12.2" "partial, special case"]
theorem preservesFiniteColimits_internalHomFirstMate :
    Limits.PreservesFiniteColimits (internalHomFirstMate O G) := by
  have hsize : Limits.PreservesColimitsOfSize.{0, 0} (internalHomFirstMate O G) :=
    (internalHomFirstMateAdjunction O G).leftAdjoint_preservesColimits
  infer_instance

end FirstMateContinuity

section UnitSource

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u})

attribute [local instance] _root_.SheafOfModules.monoidalCategory
  _root_.SheafOfModules.monoidalClosed

/-- **Internal Hom out of the structure sheaf is the identity functor**, the clause of
Stacks 03EM that says a local map `O|_U ⟶ G|_U` is its value at the unit section.

The internal Hom sheaf out of `F` is the internal hom of the monoidal closed structure on
sheaves of `O`-modules, by the bridge
`Stacks.SheafOfModules.InternalHom.ihomIsoInternalHomSecondFunctor`; at the monoidal unit that
internal hom is the identity functor, and the monoidal unit is the structure sheaf by
`SheafOfModules.unitIso`. -/
@[ega "0 4.1.5" "Hom_A(A, special case"]
def internalHomSecondFunctorUnitIso :
    internalHomSecondFunctor J O (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) ≅
      𝟭 _ :=
  (ihomIsoInternalHomSecondFunctor O _).symm ≪≫
    MonoidalClosed.internalHom.mapIso (_root_.SheafOfModules.unitIso O).op ≪≫
      MonoidalClosed.unitNatIso.symm

end UnitSource

section Reassociation

variable {C : Type*} [Category* C]

/-- From `m ≫ i₁ = i₂ ≫ w` and `w ≫ p = q` conclude `m ≫ i₁ ≫ p = i₂ ≫ q`.

Over a plain category on purpose. The identity it is used for carries one sheaf of rings,
`Stacks.SheafOfModules.Tensor.ringSheaf O`, on both sides -- the several spellings this
paragraph used to distinguish have been merged onto that one declaration -- but the
`CategoryStruct.comp` instances recorded in its two sides are still reached by different paths;
a reassociation performed in place there is not accepted by the transparency at which `rw`
type-checks its motive. -/
private theorem comp_comp_of_comp_eq {W Z T V S : C}
    (m : W ⟶ Z) (i₁ : Z ⟶ T) (p : T ⟶ V) (i₂ : W ⟶ S) (w : S ⟶ T) (q : S ⟶ V)
    (h : m ≫ i₁ = i₂ ≫ w) (h2 : w ≫ p = q) : m ≫ i₁ ≫ p = i₂ ≫ q := by
  rw [← Category.assoc, h, Category.assoc, h2]

end Reassociation

section AbstractColimits

variable {C D : Type*} [Category* C] [Category* D] {L L' : C ⥤ D}
  [PreservesFiniteColimits L] [PreservesFiniteColimits L']

/-- A natural transformation between functors preserving finite colimits which is invertible at
`A` is invertible at a finite coproduct of copies of `A`. -/
private theorem isIso_app_of_finiteCofan (α : L ⟶ L') {A P : C} [IsIso (α.app A)]
    {I : Type*} [Finite I] (ι : I → (A ⟶ P)) (hP : IsColimit (Cofan.mk P ι)) :
    IsIso (α.app P) := by
  have : ∀ i, IsIso ((Functor.whiskerLeft (Discrete.functor (fun _ : I => A)) α).app i) := by
    intro _
    change IsIso (α.app A)
    infer_instance
  have : IsIso (Functor.whiskerLeft (Discrete.functor (fun _ : I => A)) α) :=
    NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit _ α _ hP

/-- A natural transformation between functors preserving finite colimits which is invertible at
the two terms of a presentation is invertible at the presented object. -/
private theorem isIso_app_of_cokernel [HasZeroMorphisms C] (α : L ⟶ L') {Q P M : C}
    (a : Q ⟶ P) (b : P ⟶ M) (hab : a ≫ b = 0)
    (hM : IsColimit (CokernelCofork.ofπ b hab)) [IsIso (α.app Q)] [IsIso (α.app P)] :
    IsIso (α.app M) := by
  have : ∀ j, IsIso ((Functor.whiskerLeft (parallelPair a 0) α).app j) := by
    intro j
    cases j <;> dsimp <;> infer_instance
  have : IsIso (Functor.whiskerLeft (parallelPair a 0) α) := NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit _ α _ hM

/-- A composite of two isomorphisms is an isomorphism, with the two factors supplied as terms
rather than found by instance search. -/
private theorem isIso_comp {A B D' : C} (p : A ⟶ B) (q : B ⟶ D')
    (hp : IsIso p) (hq : IsIso q) : IsIso (p ≫ q) := by
  have := hp
  have := hq
  infer_instance

/-- **A natural transformation between functors preserving finite colimits which is invertible
at `A` is invertible at every object presented by finite coproducts of copies of `A`.** -/
@[ega "0 6.7.6" "partial"]
private theorem isIso_app_of_finitePresentation [HasZeroMorphisms C] (α : L ⟶ L')
    {A P Q M : C} [IsIso (α.app A)] {I K : Type*} [Finite I] [Finite K]
    (ι : I → (A ⟶ P)) (κ : K → (A ⟶ Q))
    (hP : IsColimit (Cofan.mk P ι)) (hQ : IsColimit (Cofan.mk Q κ))
    (a : Q ⟶ P) (b : P ⟶ M) (hab : a ≫ b = 0)
    (hM : IsColimit (CokernelCofork.ofπ b hab)) : IsIso (α.app M) := by
  have := isIso_app_of_finiteCofan α ι hP
  have := isIso_app_of_finiteCofan α κ hQ
  exact isIso_app_of_cokernel α a b hab hM

end AbstractColimits

section ToposFlat

variable {X Y : RingedSite.{u, u, u}}
  (φ : RingedToposHom (RingedSite.ringedTopos X) (RingedSite.ringedTopos Y))
  (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))

/-- The comparison of Stacks 03EL is natural in its second variable, read with the curried
tensor product that the correspondence of Stacks 03EO is stated with. This is the companion of
`pullbackTensorIso_inv_app_naturality_left`. -/
theorem pullbackTensorIso_inv_app_naturality_right
    {A B B' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)}
    (b : B ⟶ B') :
    ((sheafTensor.{u, u, u, u, u} X.O).obj ((toposPullback φ).obj A)).map
        ((toposPullback φ).map b) ≫
        (pullbackTensorIso φ.toModulesHom).inv.app (A, B') =
      (pullbackTensorIso φ.toModulesHom).inv.app (A, B) ≫
        (toposPullback φ).map (((sheafTensor.{u, u, u, u, u} Y.O).obj A).map b) := by
  simpa using (pullbackTensorIso φ.toModulesHom).inv.naturality (Prod.mkHom (𝟙 A) b)

/-- **The canonical map of Stacks 0GMX is functorial in its first variable.** For a morphism
`c : F' ⟶ F` of sheaves of `O_Y`-modules the square built from the canonical maps at `F` and at
`F'` and from the comparison `internalHomPre` in the first variable on the two sites commutes.

This is the "functoriality of Remark 18.27.3" that the proof of Stacks 0GN2 cites. By
`tensorEvaluation_injective` it is an identity between two morphisms out of a tensor product,
and there it is the naturality of the comparison of Stacks 03EL in its second variable: both
sides become the pulled-back evaluation of `Hom_{O_Y}(F, G)` precomposed with `c`. -/
@[stacks 0GMX "functoriality of the canonical map in the first variable"]
theorem toposPullbackInternalHomMap_naturality
    {F F' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)}
    (c : F' ⟶ F) :
    toposPullbackInternalHomMap φ F G ≫
        (internalHomPre X.O ((toposPullback φ).map c)).app ((toposPullback φ).obj G) =
      (toposPullback φ).map ((internalHomPre Y.O c).app G) ≫
        toposPullbackInternalHomMap φ F' G := by
  have hkey : tensorEvaluation Y.O F' G ((internalHomPre Y.O c).app G) =
      ((sheafTensor.{u, u, u, u, u} Y.O).obj ((internalHomSecondFunctor Y.J Y.O F).obj G)).map c ≫
        internalHomEvaluation Y.O F G := by
    simpa only [Category.id_comp, tensorEvaluation_id] using
      tensorEvaluation_comp_internalHomPre Y.O c (𝟙 ((internalHomSecondFunctor Y.J Y.O F).obj G))
  have hmap := congrArg (fun z ↦ (toposPullback φ).map z) hkey.symm
  have hcomp := (toposPullback φ).map_comp
    (((sheafTensor.{u, u, u, u, u} Y.O).obj ((internalHomSecondFunctor Y.J Y.O F).obj G)).map c)
    (internalHomEvaluation Y.O F G)
  apply tensorEvaluation_injective X.O ((toposPullback φ).obj F') ((toposPullback φ).obj G)
  rw [tensorEvaluation_comp_internalHomPre, tensorEvaluation_toposPullbackInternalHomMap,
    tensorEvaluation_comp, tensorEvaluation_toposPullbackInternalHomMap,
    toposPullback_tensorEvaluation]
  exact comp_comp_of_comp_eq _ _ _ _ _ _
    (pullbackTensorIso_inv_app_naturality_right φ c) (hcomp.symm.trans hmap)

/-- **The canonical map of Stacks 0GMX is an isomorphism when internal Hom out of its first
argument is an equivalence on both sites.**

The evaluation morphism of `Hom_{O_D}(A, G)` is the counit of the correspondence of
Stacks 03EO, so it is invertible as soon as `Hom_{O_D}(A, -)` is fully faithful; the pullback of
an invertible morphism is invertible and the comparison of Stacks 03EL is an isomorphism, so the
pullback of the evaluation morphism is invertible too. The canonical map is its transpose, which
is the unit of the correspondence on the site `C` followed by `Hom_{O_C}(f^*A, -)` applied to
it, and both of those are invertible when `Hom_{O_C}(f^*A, -)` is an equivalence.

At `A = O_D` the two hypotheses are the identity `Hom_O(O, -) = id` of Stacks 03EM together
with the identification `f^*O_D = O_C`; that is
`isIso_toposPullbackInternalHomMap_unit`. -/
theorem isIso_toposPullbackInternalHomMap_of_isEquivalence
    (A : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
    (hA : (internalHomSecondFunctor Y.J Y.O A).IsEquivalence)
    (hA' : (internalHomSecondFunctor X.J X.O ((toposPullback φ).obj A)).IsEquivalence) :
    IsIso (toposPullbackInternalHomMap φ A G) := by
  have counitIsIso : IsIso (sheafTensorRightHomAdjunction Y.O A).counit :=
    @Adjunction.instIsIsoFunctorCounitOfIsEquivalence_1 _ _ _ _ _ _
      (sheafTensorRightHomAdjunction Y.O A) hA
  have hcounit : IsIso (internalHomEvaluation Y.O A G) :=
    ((@asIso _ _ _ _ (sheafTensorRightHomAdjunction Y.O A).counit counitIsIso).app G).isIso_hom
  have h1 : IsIso ((pullbackTensorIso φ.toModulesHom).inv.app
      ((internalHomSecondFunctor Y.J Y.O A).obj G, A)) :=
    ((pullbackTensorIso φ.toModulesHom).app
      ((internalHomSecondFunctor Y.J Y.O A).obj G, A)).isIso_inv
  have h3 : IsIso ((toposPullback φ).map (internalHomEvaluation Y.O A G)) :=
    ((toposPullback φ).mapIso (@asIso _ _ _ _ (internalHomEvaluation Y.O A G) hcounit)).isIso_hom
  have h2 : IsIso (toposPullbackEvaluation φ A G) := isIso_comp _ _ h1 h3
  have unitIsIso : IsIso (sheafTensorRightHomAdjunction X.O ((toposPullback φ).obj A)).unit :=
    @Adjunction.instIsIsoFunctorUnitOfIsEquivalence _ _ _ _ _ _
      (sheafTensorRightHomAdjunction X.O ((toposPullback φ).obj A)) hA'
  have hu : IsIso ((sheafTensorRightHomAdjunction X.O
      ((toposPullback φ).obj A)).unit.app
      ((toposPullback φ).obj ((internalHomSecondFunctor Y.J Y.O A).obj G))) := by
    infer_instance
  have hm : IsIso ((internalHomSecondFunctor X.J X.O ((toposPullback φ).obj A)).map
      (toposPullbackEvaluation φ A G)) :=
    ((internalHomSecondFunctor X.J X.O ((toposPullback φ).obj A)).mapIso
      (@asIso _ _ _ _ (toposPullbackEvaluation φ A G) h2)).isIso_hom
  have key := (sheafTensorRightHomAdjunction X.O ((toposPullback φ).obj A)).homEquiv_unit
    ((toposPullback φ).obj ((internalHomSecondFunctor Y.J Y.O A).obj G))
    ((toposPullback φ).obj G) (toposPullbackEvaluation φ A G)
  exact (congrArg (fun morphism => IsIso morphism) key).mpr (isIso_comp _ _ hu hm)

/-- **Stacks 0GN2 at the structure sheaf.** The canonical map of Stacks 0GMX is an isomorphism
when its first argument is the structure sheaf.

The hypotheses are the two inputs the source names at this point: the identification
`f^*O_D = O_C` of the pullback of the structure sheaf, and the identity `Hom_O(O, -) = id` of
Stacks 03EM on each of the two sites. -/
theorem isIso_toposPullbackInternalHomMap_unit
    (eO : (toposPullback φ).obj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
    (hY : internalHomSecondFunctor Y.J Y.O
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) ≅ 𝟭 _)
    (hX : internalHomSecondFunctor X.J X.O
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) ≅ 𝟭 _) :
    IsIso (toposPullbackInternalHomMap φ
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) G) :=
  isIso_toposPullbackInternalHomMap_of_isEquivalence φ G _
    (Functor.isEquivalence_of_iso hY.symm)
    (Functor.isEquivalence_of_iso (hX.symm ≪≫ asIso (internalHomPre X.O eO.hom)))

/-- **Stacks 0GN2 at the structure sheaf, for a morphism of ringed topoi.** The canonical map
`φ^* Hom_{O_Y}(O_Y, G) ⟶ Hom_{O_X}(φ^*O_Y, φ^*G)` of Stacks 0GMX is an isomorphism.

No flatness and no finiteness hypothesis is needed: the two inputs are the identification
`φ^*O_Y = O_X` of Stacks 03D6 and the identity `Hom_O(O, -) = id` of Stacks 03EM on each of the
two sites, both of which this development proves. -/
theorem isIso_toposPullbackInternalHomMap_structureSheaf :
    IsIso (toposPullbackInternalHomMap φ
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) G) :=
  isIso_toposPullbackInternalHomMap_unit φ G
    (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso φ.toModulesHom).symm
    (internalHomSecondFunctorUnitIso Y.O) (internalHomSecondFunctorUnitIso X.O)

end ToposFlat

section RingedSiteFlat

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))

/-- **The canonical maps of Stacks 0GMX are functorial in the first variable.** For a morphism
`c : F' ⟶ F` of sheaves of `O_D`-modules the square built from the canonical maps at `F` and at
`F'` and from the comparison `internalHomPre` on the two sites commutes.

This is the "functoriality of Remark 18.27.3" that the proof of Stacks 0GN2 cites. It is
`toposPullbackInternalHomMap_naturality` at the morphism of ringed topoi of `f`, the two
readings of the canonical map agreeing by `toposPullbackInternalHomMap_ringedToposHom`. -/
@[stacks 0GMX "first-variable functoriality, for a morphism of ringed sites",
  ega "0 4.4.6" "Functoriality of γ♯"]
theorem pullbackInternalHomNatural
    {F F' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)}
    (c : F' ⟶ F) :
    pullbackInternalHomMap f F G ≫
        (internalHomPre X.O ((ringedSitePullback f).map c)).app
          ((ringedSitePullback f).obj G) =
      (ringedSitePullback f).map ((internalHomPre Y.O c).app G) ≫
        pullbackInternalHomMap f F' G :=
  toposPullbackInternalHomMap_naturality f.ringedToposHom G c

/-- **The canonical map of Stacks 0GMX as a natural transformation of the first variable.** The
naturality squares are `pullbackInternalHomNatural`. -/
def pullbackInternalHomNatTrans :
    ringedSitePullback f ⋙ internalHomFirstMate X.O ((ringedSitePullback f).obj G) ⟶
      internalHomFirstMate Y.O G ⋙ (ringedSitePullback f).op where
  app F := (pullbackInternalHomMap f F G).op
  naturality _ _ c := Quiver.Hom.unop_inj (pullbackInternalHomNatural f G c)

/-- **Stacks 04JC for a morphism of ringed sites.** If `f` is flat — that is, if `O_C` is flat
as an `f⁻¹O_D`-module — then the pullback `f^* : Mod(O_D) ⥤ Mod(O_C)` of sheaves of modules
preserves finite limits.

This is `Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap` at the morphism
of ringed topoi of `f`. That result is stated for the pullback built over the four-field
morphism of ringed topoi of the modules development, whereas `ringedSitePullback` is built over
the two-field morphism of Stacks 01D3; the two are left adjoints of one and the same direct
image, by `AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModulesViaComparison` and
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules`, so they are identified by
uniqueness of left adjoints and left exactness transfers along that isomorphism. -/
@[stacks 04JC "left exactness of the flat pullback, for a morphism of ringed sites"]
theorem preservesFiniteLimits_ringedSitePullback_of_isFlat
    (hf : AlgebraicGeometry.SheafOfModules.IsFlatMapULift
      f.ringedToposHom.fSharpInverseImage) :
    Limits.PreservesFiniteLimits (ringedSitePullback f) := by
  have hex := Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap
    f.ringedToposHom hf
  rw [exactFunctor_iff] at hex
  have := hex.1
  exact preservesFiniteLimits_of_natIso
    (Adjunction.leftAdjointUniq
      (AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModulesViaComparison
        f.ringedToposHom)
      (AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules f.ringedToposHom))

/-- **Stacks 0GN2, for a globally finitely presented `F`.** Let
`f : (C, O_C) ⟶ (D, O_D)` be a flat morphism of ringed sites and let `F`, `G` be sheaves of
`O_D`-modules with `F` presented, over the whole site `D`, as the cokernel of a morphism between
finite coproducts of copies of `O_D`. Then the canonical map

`f^* Hom_{O_D}(F, G) ⟶ Hom_{O_C}(f^*F, f^*G)`

of Stacks 0GMX is an isomorphism.

Flatness is the hypothesis `hf`, that `O_C` is flat as an `f⁻¹O_D`-module, which is the
definition of a flat morphism of Tag 04JB. It enters through the left exactness of `f^*`
(Tag 04JC, `preservesFiniteLimits_ringedSitePullback_of_isFlat`), because that is what makes
`F ↦ f^* Hom_{O_D}(F, G)` carry the finite colimit presenting `F` to a limit of internal Hom
sheaves; the other composite needs only that `f^*` is a left adjoint. The continuity of internal
Hom in its first variable is Tag 03EN, `preservesFiniteColimits_internalHomFirstMate`, and the
remaining two inputs the source's proof names are `pullbackInternalHomNatural`, the
first-variable functoriality of the canonical map of Stacks 0GMX, and
`isIso_toposPullbackInternalHomMap_structureSheaf`, its invertibility at the structure sheaf.

The presentation of `F` is a global one, not the local finite presentation of Tag 03DL that the
source assumes: `ι`, `κ`, `hP`, `hQ`, `a`, `b`, `hab` and `hF` exhibit `F` as a cokernel of a
morphism between finite coproducts of copies of the structure sheaf over the whole site `D`.
That is strictly stronger than finite presentation, so the statement here is the global special
case of Stacks 0GN2; the local case is reduced to it by
`PullbackInternalHomFinitePresentation.isIso_pullbackInternalHomMap_of_isFinitePresentationOnSite`,
which states the source's own hypotheses. -/
@[stacks 0GN2 "the isomorphism, for a global rather than local (Tag 03DL) finite presentation
of F", ega "0 6.7.6" "special case"]
theorem isIso_pullbackInternalHomMap
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hf : AlgebraicGeometry.SheafOfModules.IsFlatMapULift
      f.ringedToposHom.fSharpInverseImage)
    {n m : ℕ} {P Q : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (ι : Fin n → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶ P))
    (κ : Fin m → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶ Q))
    (hP : Limits.IsColimit (Limits.Cofan.mk P ι))
    (hQ : Limits.IsColimit (Limits.Cofan.mk Q κ))
    (a : Q ⟶ P) (b : P ⟶ F) (hab : a ≫ b = 0)
    (hF : Limits.IsColimit (Limits.CokernelCofork.ofπ b hab)) :
    IsIso (pullbackInternalHomMap f F G) := by
  have := preservesFiniteLimits_ringedSitePullback_of_isFlat f hf
  have := preservesFiniteColimits_internalHomFirstMate X.O ((ringedSitePullback f).obj G)
  have := preservesFiniteColimits_internalHomFirstMate Y.O G
  have hsize : Limits.PreservesColimitsOfSize.{0, 0} (ringedSitePullback f) :=
    (RingedToposHom.pullbackAdjPushforwardModules
      f.ringedToposHom).leftAdjoint_preservesColimits
  have hcol : Limits.PreservesFiniteColimits (ringedSitePullback f) := inferInstance
  have hop : Limits.PreservesFiniteColimits (ringedSitePullback f).op :=
    Limits.preservesFiniteColimits_op _
  have hL : Limits.PreservesFiniteColimits
      (ringedSitePullback f ⋙ internalHomFirstMate X.O ((ringedSitePullback f).obj G)) :=
    Limits.comp_preservesFiniteColimits _ _
  have hL' : Limits.PreservesFiniteColimits
      (internalHomFirstMate Y.O G ⋙ (ringedSitePullback f).op) :=
    Limits.comp_preservesFiniteColimits _ _
  have hunit : IsIso (pullbackInternalHomMap f
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) G) :=
    isIso_toposPullbackInternalHomMap_structureSheaf f.ringedToposHom G
  have happ : IsIso ((pullbackInternalHomNatTrans f G).app
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))) := by
    have := hunit
    change IsIso (pullbackInternalHomMap f
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) G).op
    infer_instance
  have hpres := isIso_app_of_finitePresentation (pullbackInternalHomNatTrans f G)
    ι κ hP hQ a b hab hF
  have hopF : IsIso (pullbackInternalHomMap f F G).op := hpres
  exact isIso_of_op _

/-- **Stacks 0GN2 for `F` the structure sheaf.** Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of
ringed sites and `G` a sheaf of `O_D`-modules. The canonical map

`f^* Hom_{O_D}(O_D, G) ⟶ Hom_{O_C}(f^*O_D, f^*G)`

of Stacks 0GMX is an isomorphism.

The structure sheaf is finitely presented, and at it both sides of the canonical map are
identified with `f^*G`: the inputs are the identification `f^*O_D = O_C` of Stacks 03D6 and the
identity `Hom_O(O, -) = id` of Stacks 03EM. Flatness of `f` is not used — the source needs it
only to carry a presentation of a general `F` across the pullback. -/
@[stacks 0GN2 "the isomorphism for F the structure sheaf", ega "0 6.7.6" "partial, special case"]
theorem isIso_pullbackInternalHomMap_structureSheaf :
    IsIso (pullbackInternalHomMap f
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) G) :=
  isIso_toposPullbackInternalHomMap_structureSheaf f.ringedToposHom G

end RingedSiteFlat

end Flat

end Stacks.SheafOfModules.InternalHom

end
