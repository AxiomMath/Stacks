module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeDual
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.MorphismGluing

/-!
# Restricting a local algebraization of a map out of a completion to a smaller open

Let `X` be a locally Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals on `X`, `G` a
coherent `𝒪_X`-module and `(F_n)` a coherent `ℐ`-adic system, and let `α : G^∧ ⟶ (F_n)` be the
datum of Stacks 0889 part (2). Over an affine open `U` the datum admits a local algebraization
`b : G|_U ⟶ F` with `β : F^∧ ≅ (F_n)|_U`, by
`Stacks.Algebraization.exists_local_algebraization_dual`. This file carries such a local
algebraization along a further open immersion `g : V ⟶ U`, so that it becomes a local
algebraization of the datum restricted along a morphism `h : V ⟶ X` factoring as `g ≫ f`. For
`V` an affine open contained in two members `U` and `U'` of a covering, the two algebraizations
then become local algebraizations of one datum on `V`, and
`Stacks.Algebraization.unique_local_algebraization_dual` relates them by a unique isomorphism.
These overlap comparisons satisfy the cocycle identity, are compatible with shrinking the
overlap, and are read on the sections over an open of `X` of the direct images of the local
algebraizations.

## Main definitions

* `Stacks.Algebraization.completionCongrIso`: the completion of a coherent module read along an
  equality of ideal sheaves.
* `Stacks.Algebraization.restrictCoherentModulesCompIso`: restricting a coherent module along a
  composite of two open immersions agrees with restricting it in two steps.
* `Stacks.Algebraization.restrictCoherentModulesCongrIso` and
  `Stacks.Algebraization.restrictedSystemCongrIso`: a coherent module and a coherent adic system
  restricted along two equal open immersions.
* `Stacks.Algebraization.compRestrictedAlgebraizationMap` and
  `Stacks.Algebraization.compRestrictedAlgebraizationIso`: the morphism and the isomorphism of a
  local algebraization transported along a further open immersion.
* `Stacks.Algebraization.restrictedAlgebraizationMapOfLE` and
  `Stacks.Algebraization.restrictedAlgebraizationIsoOfLE`: the same for the inclusion of an open
  `W ≤ U` into `U`.
* `Stacks.Algebraization.coherentModulesPushforward`: the direct image of a coherent module on an
  open subscheme, as a sheaf of modules on `X`.
* `Stacks.Algebraization.localAppOpenEquiv`: the action on the sections over an open of `X` of an
  isomorphism of the restrictions to a larger open, as a linear equivalence.
* `Stacks.Algebraization.overlapRestrictIso`: the comparison of two direct images over an open
  contained in both of their subschemes.
* `Stacks.Algebraization.restrictCoherentModulesTransportIso`: the comparison of the two ways of
  restricting a coherent module from `U` to `V ≤ W ≤ U`.

## Main results

* `Stacks.Algebraization.completionProjection_comp_completionCongrIso`: the transport along an
  equality of ideal sheaves carries the canonical projections to the canonical projections.
* `Stacks.Algebraization.restrictedCompletionCompIso_hom_eq`: the comparison of the two restricted
  completions is the completion of the comparison of the two restricted modules.
* `Stacks.Algebraization.restrictedSystemMapDual_eq_compRestrictedAlgebraization`: the datum
  restricted along `g ≫ f` factors through the transported algebraization.
* `Stacks.Algebraization.exists_restricted_local_algebraization_dual`: a local algebraization
  restricts to a local algebraization: for `h` factoring as `g ≫ f`, the transported morphism
  lands in `G|_V ⟶ F|_V` and its kernel and cokernel are annihilated by a power of `ℐ|_V`.
* `Stacks.Algebraization.restrictedSystemMapDual_eq_congr`: an algebraization of the datum
  restricted along `h` is one of the datum restricted along any morphism equal to `h`.
* `Stacks.Algebraization.restrictedSystemMapDual_eq_restrictedAlgebraizationOfLE`,
  `Stacks.Algebraization.isPowerAnnihilated_kernel_restrictedAlgebraizationMapOfLE` and
  `Stacks.Algebraization.isPowerAnnihilated_cokernel_restrictedAlgebraizationMapOfLE`: the
  canonical local algebraization over a smaller open is one, with both annihilations.
* `Stacks.Algebraization.restrictFunctorComp_assoc_app`: the associativity coherence of
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`.
* `Stacks.Algebraization.compRestrictedAlgebraizationMap_comp`: transporting `b` along `g` and
  then along `q` agrees with transporting it along `q ≫ g`.
* `Stacks.Algebraization.exists_overlapComparison_of_localAlgebraizations`: given a local
  algebraization over every affine open of `X`, every affine open `W` contained in two of them
  carries an isomorphism of the two restrictions, compatible with the two morphisms out of `G|_W`
  and with the two identifications of `(F_n)|_W`, and these satisfy the cocycle identity on a
  triple overlap.
* `Stacks.Algebraization.isQuasicoherent_restrict_coherentModulesPushforward` and
  `Stacks.Algebraization.isFiniteType_restrict_coherentModulesPushforward`: the direct image of a
  coherent module is quasi-coherent and of finite type on its own open subscheme.
* `Stacks.Algebraization.exists_sectionComparison_of_sheafComparison`: a family of comparisons of
  coherent modules with its cocycle identity gives a family of linear equivalences of sections
  over opens of `X` with its cocycle identity.
* `Stacks.Algebraization.restrictCoherentPushforwardCompIso_hom_app` and
  `Stacks.Algebraization.coherentModulesPushforwardRestrictIso_hom_app`: the identification of
  the sections of a direct image over a smaller open, and its inverse, act on the sections over
  an open as a single restriction map of the presheaf of the module.
* `Stacks.Algebraization.localApp_overlapRestrictIso` and
  `Stacks.Algebraization.localAppOpen_overlapRestrictIso`: an overlap comparison of two direct
  images acts on the sections over an open of `X` as the comparison of the two restricted
  coherent modules, between two restriction maps.
* `Stacks.Algebraization.restrictedAlgebraizationIsoDual_naturality`,
  `Stacks.Algebraization.compRestrictedAlgebraizationIso_naturality` and
  `Stacks.Algebraization.restrictedAlgebraizationIsoOfLE_naturality`: the transported comparison
  isomorphism of a local algebraization is natural in the pair `(F, β)`.
* `Stacks.Algebraization.restrictedAlgebraizationIsoOfLE_trans` and
  `Stacks.Algebraization.restrictedAlgebraizationMapOfLE_trans`: the local algebraization over
  `U` carried down to `V ≤ W ≤ U` in two steps is the one carried down in a single step, on the
  comparison isomorphism and on the morphism respectively.
* `Stacks.Algebraization.overlapComparison_eq_transport`: an overlap comparison over an affine
  open contained in a larger open is the transport of the comparison over that larger open.
* `Stacks.Algebraization.localAppOpen_overlapRestrictIso_restrict`: the overlap comparisons on
  sections are compatible with shrinking the overlap.
* `Stacks.Algebraization.restrictedAlgebraizationIsoOfLE_hom_app`: the level-`n` component of
  the transported comparison isomorphism, unfolded.

## Implementation notes

The ideal sheaf of the composite and the composite of the two ideal sheaves are equal, by
`AlgebraicGeometry.Scheme.IdealSheafData.comap_comp`, but the completion functor depends on its
ideal sheaf through the type of its values, so the equality cannot be used by `rw`: abstracting
the ideal sheaf out of the type of a datum already typed at one of the two leaves a motive that
is not type correct. Everything is therefore routed through
`Stacks.Algebraization.completionCongrIso`, whose two lemmas are proved by `cases` on an equality
of two *variable* ideal sheaves and instantiated afterwards. The same device handles the
factorization `g ≫ f = h`: `Stacks.Algebraization.exists_restricted_local_algebraization_dual`
takes `h` as a variable with that equation as a hypothesis, which `subst` eliminates.

Four kinds of rewrite fail in this file because the term being rewritten occurs in the *type* of
something else in the goal:

* `AlgebraicGeometry.Scheme.homOfLE_ι` and `AlgebraicGeometry.Scheme.homOfLE_homOfLE` under
  `· ''ᵁ ·`, whose motive carries the open-immersion instance of the morphism; handled by
  `Stacks.Algebraization.homOfLE_image_eq_ι_preimage_image` and
  `Stacks.Algebraization.image_comp_eq_of_eq`, which take the equation as a hypothesis on a
  *variable* morphism;
* `AlgebraicGeometry.Scheme.IdealSheafData.comap_comp` inside the type of a datum, handled by
  `Stacks.Algebraization.completionCongrIso`;
* `CategoryTheory.Category.assoc` on morphisms of `AlgebraicGeometry.Scheme.Modules`, which
  matches the scheme-level composite inside the morphism's type; handled by reassociation lemmas
  stated in an abstract category (among them `comp_assoc_eq_of_eq₂` and
  `comp_assoc_eq_comp_of_eq₂` of `AlgebraizeDual`) and applied by `exact`, which checks up to
  definitional equality;
* `AlgebraicGeometry.Scheme.Modules.Hom.comp_app` and
  `Stacks.Algebraization.restrictFunctor_map_app`, which in some goals do not match even though
  they are `rfl`: `AlgebraicGeometry.Scheme.Modules` is a `def` for
  `SheafOfModules X.ringCatSheaf`, and the two spellings carry defeq but not syntactically equal
  category instances; handled by a `rfl` lemma stated at exactly the shape of the goal, or by
  closing the residual goal with `rfl`.

`Stacks.Algebraization.restrictedAlgebraizationIsoOfLE` is a threefold composite of
isomorphisms, so the equation naming its level-`n` component as the composite of the three
components is `rfl`; stated that way it exceeds the kernel's reduction budget, the type of a
component naming the terms of a completion, which are cokernels.
`Stacks.Algebraization.restrictedAlgebraizationIsoOfLE_eq` states the unfolding at the level of
isomorphisms, and `Stacks.Algebraization.isoTrans₃_hom_app` takes the component afterwards in an
abstract functor category. `Stacks.Algebraization.coherentIsoConjugate_hom_app` is the same
device at the level of coherent modules.

The cocycle identity is obtained from the uniqueness clause
`Stacks.Algebraization.unique_local_algebraization_dual`, which is why
`Stacks.Algebraization.restrictedAlgebraizationMapOfLE` and
`Stacks.Algebraization.restrictedAlgebraizationIsoOfLE` are definitions and not existential
statements: the comparison on an overlap is pinned down by the same transported algebraization on
each of the three faces of a triple overlap.

## References

* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-! ### Reassociation in a category -/

section AssocHelpers

variable {C : Type*} [Category C]

/-- Cancelling an inverse-then-forward pair in the middle of a composite. -/
private theorem comp_cancel_mid {A B D E Z T : C} (a : A ⟶ B) (b : B ⟶ D) (ci : D ⟶ E)
    (ch : E ⟶ D) (b' : D ⟶ Z) (d : Z ⟶ T) (h : ci ≫ ch = 𝟙 D) :
    (a ≫ b ≫ ci) ≫ ch ≫ b' ≫ d = a ≫ (b ≫ b') ≫ d := by
  simp only [Category.assoc]
  rw [← Category.assoc ci ch, h, Category.id_comp]

/-- Regrouping a composite of four morphisms against two given composites. -/
private theorem comp_regroup_eq {A B D E Z S T : C} {c : A ⟶ B} {p : B ⟶ D} {x : D ⟶ E}
    {y : E ⟶ Z} {s : A ⟶ S} {u : S ⟶ E} {t : S ⟶ T} {v : T ⟶ Z}
    (h₁ : c ≫ p ≫ x = s ≫ u) (h₂ : u ≫ y = t ≫ v) : c ≫ p ≫ x ≫ y = (s ≫ t) ≫ v := by
  rw [reassoc_of% h₁, h₂, Category.assoc]

/-- Composition in a full subcategory is composition of the underlying morphisms. -/
private theorem fullSubcategory_comp_hom {P : ObjectProperty C} {A B D : P.FullSubcategory}
    (x : A ⟶ B) (y : B ⟶ D) : (x ≫ y).hom = x.hom ≫ y.hom := rfl

end AssocHelpers

/-! ### Transport along an equality of ideal sheaves -/

/-- **The completion of a coherent module read along an equality of ideal sheaves.** -/
public def completionCongrIso {V : Scheme.{u}} [IsLocallyNoetherian V]
    {K K' : V.IdealSheafData} (hK : K = K')
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules V.ringCatSheaf) :
    ((completionFunctor V K).obj M).obj ≅ ((completionFunctor V K').obj M).obj := by
  cases hK
  exact Iso.refl _

/-- **The transport along an equality of ideal sheaves carries projections to projections.** -/
public theorem completionProjection_comp_completionCongrIso {V : Scheme.{u}}
    [IsLocallyNoetherian V] {K K' : V.IdealSheafData} (hK : K = K')
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules V.ringCatSheaf) (n : ℕ) :
    completionProjection V K M n ≫ (completionCongrIso hK M).hom.app (op n) =
      completionProjection V K' M n := by
  cases hK
  exact Category.comp_id _

/-- **The transport along an equality of ideal sheaves is natural in the module.** -/
public theorem completionCongrIso_naturality {V : Scheme.{u}} [IsLocallyNoetherian V]
    {K K' : V.IdealSheafData} (hK : K = K')
    {M N : AlgebraicGeometry.SheafOfModules.CoherentModules V.ringCatSheaf} (b : M ⟶ N) :
    ((completionFunctor V K).map b).hom ≫ (completionCongrIso hK N).hom =
      (completionCongrIso hK M).hom ≫ ((completionFunctor V K').map b).hom := by
  cases hK
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-! ### Restricting a coherent module along a composite -/

/-- **Restricting a coherent module along a composite of two open immersions agrees with
restricting it in two steps.** This is
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` read in the full subcategory of coherent
modules. -/
public def restrictCoherentModulesCompIso {X Y V : Scheme.{u}} (g : V ⟶ Y) (f : Y ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    restrictCoherentModules (g ≫ f) G ≅
      restrictCoherentModules g (restrictCoherentModules f G) :=
  ObjectProperty.isoMk _ ((Scheme.Modules.restrictFunctorComp g f).app G.obj)

/-- The underlying morphism of `Stacks.Algebraization.restrictCoherentModulesCompIso`. -/
public theorem restrictCoherentModulesCompIso_hom_hom {X Y V : Scheme.{u}} (g : V ⟶ Y)
    (f : Y ⟶ X) [IsOpenImmersion g] [IsOpenImmersion f] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y]
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    (restrictCoherentModulesCompIso g f G).hom.hom =
      (Scheme.Modules.restrictFunctorComp g f).hom.app G.obj :=
  rfl

/-! ### Naturality in the module of the comparison of the two restricted completions -/

/-- **The comparison of the two restricted completions is the completion of the comparison of the
two restricted modules.** This is the naturality in the module of
`Stacks.Algebraization.restrictedCompletionCompIso`. -/
public theorem restrictedCompletionCompIso_hom_eq {X Y V : Scheme.{u}} (g : V ⟶ Y) (f : Y ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian V] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    (restrictedCompletionCompIso g f I G).hom =
      ((completionFunctor V (I.comap (g ≫ f))).map
            (restrictCoherentModulesCompIso g f G).hom).hom ≫
        (completionCongrIso (Scheme.IdealSheafData.comap_comp I g f)
          (restrictCoherentModules g (restrictCoherentModules f G))).hom := by
  refine completionSystemHom_ext V (I.comap (g ≫ f)) (restrictCoherentModules (g ≫ f) G) _ _
    fun n => ?_
  refine (completionProjection_comp_restrictedCompletionCompIso g f I G n).trans ?_
  exact (comp_assoc_eq_comp_of_eq₂
    (completionFunctor_map_quotient V (I.comap (g ≫ f))
      (restrictCoherentModulesCompIso g f G).hom n)
    (completionProjection_comp_completionCongrIso (Scheme.IdealSheafData.comap_comp I g f)
      (restrictCoherentModules g (restrictCoherentModules f G)) n)).symm

/-! ### Transporting a local algebraization along a further open immersion -/

/-- The morphism of a local algebraization transported along a further open immersion: the
restriction of `b` along `g`, read on the restriction of `G` along the composite. -/
public def compRestrictedAlgebraizationMap {X Y V : Scheme.{u}} (g : V ⟶ Y) (f : Y ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    {F : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf}
    (b : restrictCoherentModules f G ⟶ F) :
    restrictCoherentModules (g ≫ f) G ⟶ restrictCoherentModules g F :=
  (restrictCoherentModulesCompIso g f G).hom ≫ restrictCoherentModulesMap g b

/-- The isomorphism of a local algebraization transported along a further open immersion. -/
public def compRestrictedAlgebraizationIso {X Y V : Scheme.{u}} (g : V ⟶ Y) (f : Y ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian V] (I : X.IdealSheafData)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (β : ((completionFunctor Y (I.comap f)).obj F).obj ≅
      ((Stacks.Coherent.restrictFunctor I f).obj Fsys).obj) :
    ((completionFunctor V (I.comap (g ≫ f))).obj (restrictCoherentModules g F)).obj ≅
      ((Stacks.Coherent.restrictFunctor I (g ≫ f)).obj Fsys).obj :=
  completionCongrIso (Scheme.IdealSheafData.comap_comp I g f) (restrictCoherentModules g F) ≪≫
    restrictedAlgebraizationIsoDual g (I.comap f)
        ((Stacks.Coherent.restrictFunctor I f).obj Fsys) F β ≪≫
      (restrictedSystemCompIso g f I Fsys).symm

/-- **The transported algebraization is an algebraization of the restricted datum.** If
`α : G^∧ ⟶ (F_n)` factors over `Y` as the completion of `b : G|_Y ⟶ F` followed by `β`, then the
datum restricted along `g ≫ f` factors as the completion of
`Stacks.Algebraization.compRestrictedAlgebraizationMap` followed by
`Stacks.Algebraization.compRestrictedAlgebraizationIso`. -/
public theorem restrictedSystemMapDual_eq_compRestrictedAlgebraization {X Y V : Scheme.{u}}
    (g : V ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion g] [IsOpenImmersion f] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian V] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (b : restrictCoherentModules f G ⟶ F)
    (β : ((completionFunctor Y (I.comap f)).obj F).obj ≅
      ((Stacks.Coherent.restrictFunctor I f).obj Fsys).obj)
    (hβ : restrictedSystemMapDual f I G Fsys α =
      ((completionFunctor Y (I.comap f)).map b).hom ≫ β.hom) :
    restrictedSystemMapDual (g ≫ f) I G Fsys α =
      ((completionFunctor V (I.comap (g ≫ f))).map
          (compRestrictedAlgebraizationMap g f b)).hom ≫
        (compRestrictedAlgebraizationIso g f I Fsys F β).hom := by
  have htrans := restrictedSystemMapDual_comp g f I G Fsys α
  rw [restrictedSystemMapDual_eq_of_algebraization g (I.comap f)
    (restrictCoherentModules f G) ((Stacks.Coherent.restrictFunctor I f).obj Fsys)
    (restrictedSystemMapDual f I G Fsys α) F b β hβ, ← Iso.eq_comp_inv] at htrans
  have hmapcomp : ((completionFunctor V (I.comap (g ≫ f))).map
        (compRestrictedAlgebraizationMap g f b)).hom =
      ((completionFunctor V (I.comap (g ≫ f))).map
          (restrictCoherentModulesCompIso g f G).hom).hom ≫
        ((completionFunctor V (I.comap (g ≫ f))).map
          (restrictCoherentModulesMap g b)).hom := by
    rw [compRestrictedAlgebraizationMap, Functor.map_comp]
    rfl
  rw [compRestrictedAlgebraizationIso, Iso.trans_hom, Iso.trans_hom, hmapcomp,
    Category.assoc, ← Category.assoc
      (((completionFunctor V (I.comap (g ≫ f))).map (restrictCoherentModulesMap g b)).hom),
    completionCongrIso_naturality (Scheme.IdealSheafData.comap_comp I g f)
      (restrictCoherentModulesMap g b),
    Category.assoc, ← Category.assoc
      (((completionFunctor V (I.comap (g ≫ f))).map
        (restrictCoherentModulesCompIso g f G).hom).hom),
    ← restrictedCompletionCompIso_hom_eq g f I G, htrans]
  simp only [Category.assoc]
  rfl

/-- The kernel of a morphism composed with an isomorphism on the source is annihilated by a power
of an ideal sheaf as soon as the kernel of the morphism is. -/
private theorem isPowerAnnihilated_kernel_iso_comp {Y : Scheme.{u}} (K : Y.IdealSheafData)
    {A B D : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf} (e : A ≅ B)
    (m : B ⟶ D) (h : IsPowerAnnihilated K (kernel (C := Y.Modules) m.hom)) :
    IsPowerAnnihilated K (kernel (C := Y.Modules) (e.hom ≫ m).hom) := by
  have : IsIso e.hom.hom := (ObjectProperty.isIso_hom_iff _).2 inferInstance
  obtain ⟨t, ht⟩ := h
  exact ⟨t, idealPowerMultiple_eq_bot_of_iso K (kernelIsIsoComp e.hom.hom m.hom) t ht⟩

/-- The cokernel of a morphism composed with an isomorphism on the source is annihilated by a
power of an ideal sheaf as soon as the cokernel of the morphism is. -/
private theorem isPowerAnnihilated_cokernel_iso_comp {Y : Scheme.{u}} (K : Y.IdealSheafData)
    {A B D : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf} (e : A ≅ B)
    (m : B ⟶ D) (h : IsPowerAnnihilated K (cokernel (C := Y.Modules) m.hom)) :
    IsPowerAnnihilated K (cokernel (C := Y.Modules) (e.hom ≫ m).hom) := by
  have : IsIso e.hom.hom := (ObjectProperty.isIso_hom_iff _).2 inferInstance
  obtain ⟨t, ht⟩ := h
  exact ⟨t, idealPowerMultiple_eq_bot_of_iso K (cokernelEpiComp e.hom.hom m.hom) t ht⟩

/-- **A local algebraization restricts to a local algebraization.** Let `h : V ⟶ X` factor as
`g ≫ f` through open immersions. If the datum of Stacks 0889 (2) restricted along `f` admits a
local algebraization `b : G|_Y ⟶ F` whose kernel and cokernel are annihilated by a power of
`ℐ|_Y`, then the datum restricted along `h` admits one out of `G|_V` with target `F|_V`, whose
kernel and cokernel are annihilated by a power of `ℐ|_V`. -/
public theorem exists_restricted_local_algebraization_dual {X Y V : Scheme.{u}} (g : V ⟶ Y)
    (f : Y ⟶ X) (h : V ⟶ X) [IsOpenImmersion g] [IsOpenImmersion f] [IsOpenImmersion h]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] (hgf : g ≫ f = h)
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (b : restrictCoherentModules f G ⟶ F)
    (β : ((completionFunctor Y (I.comap f)).obj F).obj ≅
      ((Stacks.Coherent.restrictFunctor I f).obj Fsys).obj)
    (hβ : restrictedSystemMapDual f I G Fsys α =
      ((completionFunctor Y (I.comap f)).map b).hom ≫ β.hom)
    (hKb : IsPowerAnnihilated (I.comap f) (kernel (C := Y.Modules) b.hom))
    (hCb : IsPowerAnnihilated (I.comap f) (cokernel (C := Y.Modules) b.hom)) :
    ∃ (b' : restrictCoherentModules h G ⟶ restrictCoherentModules g F)
      (β' : ((completionFunctor V (I.comap h)).obj (restrictCoherentModules g F)).obj ≅
        ((Stacks.Coherent.restrictFunctor I h).obj Fsys).obj),
      restrictedSystemMapDual h I G Fsys α =
          ((completionFunctor V (I.comap h)).map b').hom ≫ β'.hom ∧
        IsPowerAnnihilated (I.comap h) (kernel (C := V.Modules) b'.hom) ∧
          IsPowerAnnihilated (I.comap h) (cokernel (C := V.Modules) b'.hom) := by
  subst hgf
  refine ⟨compRestrictedAlgebraizationMap g f b, compRestrictedAlgebraizationIso g f I Fsys F β,
    restrictedSystemMapDual_eq_compRestrictedAlgebraization g f I G Fsys α F b β hβ, ?_, ?_⟩
  · rw [Scheme.IdealSheafData.comap_comp I g f]
    exact isPowerAnnihilated_kernel_iso_comp _ (restrictCoherentModulesCompIso g f G) _
      (isPowerAnnihilated_kernel_restrictCoherentModulesMap g (I.comap f) b hKb)
  · rw [Scheme.IdealSheafData.comap_comp I g f]
    exact isPowerAnnihilated_cokernel_iso_comp _ (restrictCoherentModulesCompIso g f G) _
      (isPowerAnnihilated_cokernel_restrictCoherentModulesMap g (I.comap f) b hCb)

/-! ### Transport along an equality of morphisms -/

/-- Restricting a coherent module along two equal open immersions. -/
public def restrictCoherentModulesCongrIso {X V : Scheme.{u}} [IsLocallyNoetherian X]
    {h h' : V ⟶ X} [IsOpenImmersion h] [IsOpenImmersion h'] (e : h = h')
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    restrictCoherentModules h G ≅ restrictCoherentModules h' G := by
  cases e
  exact Iso.refl _

/-- Restricting a coherent adic system along two equal open immersions. -/
public def restrictedSystemCongrIso {X V : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (Fsys : Stacks.Coherent.CoherentAdicSystems I) {h h' : V ⟶ X}
    [IsOpenImmersion h] [IsOpenImmersion h'] (e : h = h') :
    ((Stacks.Coherent.restrictFunctor I h).obj Fsys).obj ≅
      ((Stacks.Coherent.restrictFunctor I h').obj Fsys).obj := by
  cases e
  exact Iso.refl _

/-- **The datum read along an equality of the morphisms it is restricted along.** An
algebraization of the datum restricted along `h` is one of the datum restricted along any `h'`
equal to it. -/
public theorem restrictedSystemMapDual_eq_congr {X V : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian V] {h h' : V ⟶ X} [IsOpenImmersion h] [IsOpenImmersion h'] (e : h = h')
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules V.ringCatSheaf)
    (b : restrictCoherentModules h G ⟶ F)
    (β : ((completionFunctor V (I.comap h)).obj F).obj ≅
      ((Stacks.Coherent.restrictFunctor I h).obj Fsys).obj)
    (hβ : restrictedSystemMapDual h I G Fsys α =
      ((completionFunctor V (I.comap h)).map b).hom ≫ β.hom) :
    restrictedSystemMapDual h' I G Fsys α =
      ((completionFunctor V (I.comap h')).map
          ((restrictCoherentModulesCongrIso e G).inv ≫ b)).hom ≫
        (completionCongrIso (congrArg (fun m => I.comap m) e.symm) F ≪≫ β ≪≫
          restrictedSystemCongrIso I Fsys e).hom := by
  cases e
  rw [hβ]
  simp only [restrictCoherentModulesCongrIso, restrictedSystemCongrIso, completionCongrIso,
    Iso.refl_inv, Iso.trans_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]

/-! ### Associativity coherence of the transports -/

/-- Any two composites of restriction maps of one presheaf with the same source and target
agree: the category of opens is thin. -/
private theorem presheafMap_comp₃_eq {X : Scheme.{u}} (M : X.Modules)
    {P Q R S T : (X.Opens)ᵒᵖ} (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ S) (a' : P ⟶ T) (b' : T ⟶ S) :
    M.presheaf.map a ≫ M.presheaf.map b ≫ M.presheaf.map c =
      M.presheaf.map a' ≫ M.presheaf.map b' := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    Subsingleton.elim (a ≫ b ≫ c) (a' ≫ b')]

/-- The action on sections of the restriction of a morphism along an open immersion. -/
public theorem restrictFunctor_map_app {X V : Scheme.{u}} (h : V ⟶ X) [IsOpenImmersion h]
    {M N : X.Modules} (φ : M ⟶ N) (A : V.Opens) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor h).map φ) A =
      Scheme.Modules.Hom.app φ (h ''ᵁ A) := rfl

/-- **Associativity coherence of the restriction comparison of Mathlib.** For open immersions
`q : W ⟶ V`, `g : V ⟶ Y` and `f : Y ⟶ X`, the two ways of comparing the restriction of a module
along `(q ≫ g) ≫ f` with its restriction along `g` then `q`, through
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`, agree. -/
public theorem restrictFunctorComp_assoc_app {X Y V W : Scheme.{u}} (q : W ⟶ V) (g : V ⟶ Y)
    (f : Y ⟶ X) [IsOpenImmersion q] [IsOpenImmersion g] [IsOpenImmersion f] (M : X.Modules) :
    (Scheme.Modules.restrictFunctorCongr (Category.assoc q g f)).hom.app M ≫
        (Scheme.Modules.restrictFunctorComp q (g ≫ f)).hom.app M ≫
          (Scheme.Modules.restrictFunctor q).map
            ((Scheme.Modules.restrictFunctorComp g f).hom.app M) =
      (Scheme.Modules.restrictFunctorComp (q ≫ g) f).hom.app M ≫
        (Scheme.Modules.restrictFunctorComp q g).hom.app
          ((Scheme.Modules.restrictFunctor f).obj M) := by
  refine Scheme.Modules.hom_ext _ _ fun A => ?_
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app, restrictFunctor_map_app,
    Scheme.Modules.restrict_map]
  exact presheafMap_comp₃_eq M _ _ _ _ _

/-- The underlying morphism of `Stacks.Algebraization.restrictCoherentModulesCongrIso` is
Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr`. -/
public theorem restrictCoherentModulesCongrIso_hom_hom {X V : Scheme.{u}}
    [IsLocallyNoetherian X] {h h' : V ⟶ X} [IsOpenImmersion h] [IsOpenImmersion h'] (e : h = h')
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    (restrictCoherentModulesCongrIso e G).hom.hom =
      (Scheme.Modules.restrictFunctorCongr e).hom.app G.obj := by
  cases e
  refine Scheme.Modules.hom_ext _ _ fun A => ?_
  exact ((Scheme.Modules.presheaf (X := X) G.obj).map_id _).symm.trans
    (congrArg (Scheme.Modules.presheaf (X := X) G.obj).map (Subsingleton.elim _ _))

/-- The underlying morphism of `Stacks.Algebraization.restrictCoherentModulesMap`. -/
private theorem restrictCoherentModulesMap_hom {X V : Scheme.{u}} (h : V ⟶ X)
    [IsOpenImmersion h] [IsLocallyNoetherian X]
    {G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (b : G ⟶ F) :
    (restrictCoherentModulesMap h b).hom = (Scheme.Modules.restrictFunctor h).map b.hom := rfl

/-- **Associativity coherence of the transported algebraization morphism.** Transporting
`b : G|_Y ⟶ F` first along `g` and then along `q` agrees with transporting it along `q ≫ g` in
one step, through `Stacks.Algebraization.restrictCoherentModulesCongrIso` on the source and
`Stacks.Algebraization.restrictCoherentModulesCompIso` on the target. -/
public theorem compRestrictedAlgebraizationMap_comp {X Y V W : Scheme.{u}} (q : W ⟶ V)
    (g : V ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion q] [IsOpenImmersion g] [IsOpenImmersion f]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian V]
    {G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    {F : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf}
    (b : restrictCoherentModules f G ⟶ F) :
    (restrictCoherentModulesCongrIso (Category.assoc q g f) G).hom ≫
        compRestrictedAlgebraizationMap q (g ≫ f)
          (compRestrictedAlgebraizationMap g f b) =
      compRestrictedAlgebraizationMap (q ≫ g) f b ≫
        (restrictCoherentModulesCompIso q g F).hom := by
  refine ObjectProperty.hom_ext _ ?_
  change (restrictCoherentModulesCongrIso (Category.assoc q g f) G).hom.hom ≫
      (Scheme.Modules.restrictFunctorComp q (g ≫ f)).hom.app G.obj ≫
        (Scheme.Modules.restrictFunctor q).map
          ((Scheme.Modules.restrictFunctorComp g f).hom.app G.obj ≫
            (Scheme.Modules.restrictFunctor g).map b.hom) =
    ((Scheme.Modules.restrictFunctorComp (q ≫ g) f).hom.app G.obj ≫
        (Scheme.Modules.restrictFunctor (q ≫ g)).map b.hom) ≫
      (Scheme.Modules.restrictFunctorComp q g).hom.app F.obj
  rw [restrictCoherentModulesCongrIso_hom_hom, (Scheme.Modules.restrictFunctor q).map_comp]
  exact comp_regroup_eq (restrictFunctorComp_assoc_app q g f G.obj)
    ((Scheme.Modules.restrictFunctorComp q g).hom.naturality b.hom).symm

/-! ### The canonical local algebraization over a smaller open -/

/-- **The morphism of a local algebraization carried to a smaller open.** For `W ≤ U` the
morphism `b : G|_U ⟶ F` becomes a morphism `G|_W ⟶ F|_W`, the source being read along
`AlgebraicGeometry.Scheme.homOfLE_ι`. -/
public def restrictedAlgebraizationMapOfLE {X : Scheme.{u}} [IsLocallyNoetherian X]
    {U W : X.Opens} (hWU : W ≤ U)
    {G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    {F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    (b : restrictCoherentModules U.ι G ⟶ F) :
    restrictCoherentModules W.ι G ⟶ restrictCoherentModules (X.homOfLE hWU) F :=
  (restrictCoherentModulesCongrIso (X.homOfLE_ι hWU) G).inv ≫
    compRestrictedAlgebraizationMap (X.homOfLE hWU) U.ι b

/-- **The isomorphism of a local algebraization carried to a smaller open.** -/
public def restrictedAlgebraizationIsoOfLE {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (Fsys : Stacks.Coherent.CoherentAdicSystems I) {U W : X.Opens}
    (hWU : W ≤ U) {F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    (β : ((completionFunctor U.toScheme (I.comap U.ι)).obj F).obj ≅
      ((Stacks.Coherent.restrictFunctor I U.ι).obj Fsys).obj) :
    ((completionFunctor W.toScheme (I.comap W.ι)).obj
        (restrictCoherentModules (X.homOfLE hWU) F)).obj ≅
      ((Stacks.Coherent.restrictFunctor I W.ι).obj Fsys).obj :=
  completionCongrIso (congrArg (fun m => I.comap m) (X.homOfLE_ι hWU).symm)
      (restrictCoherentModules (X.homOfLE hWU) F) ≪≫
    compRestrictedAlgebraizationIso (X.homOfLE hWU) U.ι I Fsys F β ≪≫
      restrictedSystemCongrIso I Fsys (X.homOfLE_ι hWU)

/-- **The canonical local algebraization over a smaller open is one.** -/
public theorem restrictedSystemMapDual_eq_restrictedAlgebraizationOfLE {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj) {U W : X.Opens} (hWU : W ≤ U)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf)
    (b : restrictCoherentModules U.ι G ⟶ F)
    (β : ((completionFunctor U.toScheme (I.comap U.ι)).obj F).obj ≅
      ((Stacks.Coherent.restrictFunctor I U.ι).obj Fsys).obj)
    (hβ : restrictedSystemMapDual U.ι I G Fsys α =
      ((completionFunctor U.toScheme (I.comap U.ι)).map b).hom ≫ β.hom) :
    restrictedSystemMapDual W.ι I G Fsys α =
      ((completionFunctor W.toScheme (I.comap W.ι)).map
          (restrictedAlgebraizationMapOfLE hWU b)).hom ≫
        (restrictedAlgebraizationIsoOfLE I Fsys hWU β).hom :=
  restrictedSystemMapDual_eq_congr (X.homOfLE_ι hWU) I G Fsys α
    (restrictCoherentModules (X.homOfLE hWU) F)
    (compRestrictedAlgebraizationMap (X.homOfLE hWU) U.ι b)
    (compRestrictedAlgebraizationIso (X.homOfLE hWU) U.ι I Fsys F β)
    (restrictedSystemMapDual_eq_compRestrictedAlgebraization (X.homOfLE hWU) U.ι I G Fsys α F b β
      hβ)

/-- The kernel of the canonical local algebraization over a smaller open is annihilated by a
power of the restricted ideal sheaf. -/
public theorem isPowerAnnihilated_kernel_restrictedAlgebraizationMapOfLE {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) {U W : X.Opens} (hWU : W ≤ U)
    {G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    {F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    (b : restrictCoherentModules U.ι G ⟶ F)
    (hKb : IsPowerAnnihilated (I.comap U.ι) (kernel (C := U.toScheme.Modules) b.hom)) :
    IsPowerAnnihilated (I.comap W.ι)
      (kernel (C := W.toScheme.Modules) (restrictedAlgebraizationMapOfLE hWU b).hom) := by
  rw [show I.comap W.ι = (I.comap U.ι).comap (X.homOfLE hWU) by
    rw [← Scheme.IdealSheafData.comap_comp, X.homOfLE_ι]]
  exact isPowerAnnihilated_kernel_iso_comp _
    (restrictCoherentModulesCongrIso (X.homOfLE_ι hWU) G).symm _
    (isPowerAnnihilated_kernel_iso_comp _
      (restrictCoherentModulesCompIso (X.homOfLE hWU) U.ι G) _
      (isPowerAnnihilated_kernel_restrictCoherentModulesMap (X.homOfLE hWU) (I.comap U.ι) b hKb))

/-- The cokernel of the canonical local algebraization over a smaller open is annihilated by a
power of the restricted ideal sheaf. -/
public theorem isPowerAnnihilated_cokernel_restrictedAlgebraizationMapOfLE {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) {U W : X.Opens} (hWU : W ≤ U)
    {G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    {F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    (b : restrictCoherentModules U.ι G ⟶ F)
    (hCb : IsPowerAnnihilated (I.comap U.ι) (cokernel (C := U.toScheme.Modules) b.hom)) :
    IsPowerAnnihilated (I.comap W.ι)
      (cokernel (C := W.toScheme.Modules) (restrictedAlgebraizationMapOfLE hWU b).hom) := by
  rw [show I.comap W.ι = (I.comap U.ι).comap (X.homOfLE hWU) by
    rw [← Scheme.IdealSheafData.comap_comp, X.homOfLE_ι]]
  exact isPowerAnnihilated_cokernel_iso_comp _
    (restrictCoherentModulesCongrIso (X.homOfLE_ι hWU) G).symm _
    (isPowerAnnihilated_cokernel_iso_comp _
      (restrictCoherentModulesCompIso (X.homOfLE hWU) U.ι G) _
      (isPowerAnnihilated_cokernel_restrictCoherentModulesMap (X.homOfLE hWU) (I.comap U.ι) b hCb))

/-! ### The overlap comparisons and the cocycle identity -/

/-- **The overlap comparisons of a family of local algebraizations, and their cocycle
identity.** Let `α : G^∧ ⟶ (F_n)` be the datum of Stacks 0889 (2) and suppose given, over every
affine open `U` of `X`, a local algebraization `b U : G|_U ⟶ F U` with `β U : (F U)^∧ ≅ (F_n)|_U`
whose kernel and cokernel are annihilated by a power of `ℐ|_U`.

Then for every affine open `W` contained in two affine opens `U` and `U'` there is an
isomorphism `F U |_W ≅ F U' |_W` compatible with the two morphisms out of `G|_W` and with the two
identifications of `(F_n)|_W`, and these isomorphisms satisfy the **cocycle identity** on a
triple overlap. -/
public theorem exists_overlapComparison_of_localAlgebraizations {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj)
    (F : ∀ i : X.affineOpens,
      AlgebraicGeometry.SheafOfModules.CoherentModules i.1.toScheme.ringCatSheaf)
    (b : ∀ i : X.affineOpens, restrictCoherentModules i.1.ι G ⟶ F i)
    (β : ∀ i : X.affineOpens,
      ((completionFunctor i.1.toScheme (I.comap i.1.ι)).obj (F i)).obj ≅
        ((Stacks.Coherent.restrictFunctor I i.1.ι).obj Fsys).obj)
    (hβ : ∀ i : X.affineOpens, restrictedSystemMapDual i.1.ι I G Fsys α =
      ((completionFunctor i.1.toScheme (I.comap i.1.ι)).map (b i)).hom ≫ (β i).hom)
    (hK : ∀ i : X.affineOpens, IsPowerAnnihilated (I.comap i.1.ι)
      (kernel (C := i.1.toScheme.Modules) (b i).hom))
    (hC : ∀ i : X.affineOpens, IsPowerAnnihilated (I.comap i.1.ι)
      (cokernel (C := i.1.toScheme.Modules) (b i).hom)) :
    ∃ d : ∀ (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1),
        restrictCoherentModules (X.homOfLE hki) (F i) ≅
          restrictCoherentModules (X.homOfLE hkj) (F j),
      (∀ (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1),
          restrictedAlgebraizationMapOfLE hki (b i) ≫ (d k i j hki hkj).hom =
            restrictedAlgebraizationMapOfLE hkj (b j)) ∧
        (∀ (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1),
            ((completionFunctor k.1.toScheme (I.comap k.1.ι)).map
                (d k i j hki hkj).hom).hom ≫
              (restrictedAlgebraizationIsoOfLE I Fsys hkj (β j)).hom =
                (restrictedAlgebraizationIsoOfLE I Fsys hki (β i)).hom) ∧
          ∀ (k i j m : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1) (hkm : k.1 ≤ m.1),
            d k i j hki hkj ≪≫ d k j m hkj hkm = d k i m hki hkm := by
  choose d hd huniq using fun (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1) =>
    unique_local_algebraization_dual I G Fsys α k
      (restrictCoherentModules (X.homOfLE hki) (F i))
      (restrictCoherentModules (X.homOfLE hkj) (F j))
      (restrictedAlgebraizationMapOfLE hki (b i))
      (restrictedAlgebraizationMapOfLE hkj (b j))
      (restrictedAlgebraizationIsoOfLE I Fsys hki (β i))
      (restrictedAlgebraizationIsoOfLE I Fsys hkj (β j))
      (restrictedSystemMapDual_eq_restrictedAlgebraizationOfLE I G Fsys α hki (F i) (b i) (β i)
        (hβ i))
      (restrictedSystemMapDual_eq_restrictedAlgebraizationOfLE I G Fsys α hkj (F j) (b j) (β j)
        (hβ j))
      (isPowerAnnihilated_kernel_restrictedAlgebraizationMapOfLE I hki (b i) (hK i))
      (isPowerAnnihilated_cokernel_restrictedAlgebraizationMapOfLE I hki (b i) (hC i))
      (isPowerAnnihilated_kernel_restrictedAlgebraizationMapOfLE I hkj (b j) (hK j))
      (isPowerAnnihilated_cokernel_restrictedAlgebraizationMapOfLE I hkj (b j) (hC j))
  refine ⟨d, fun k i j hki hkj => (hd k i j hki hkj).1,
    fun k i j hki hkj => (hd k i j hki hkj).2, fun k i j m hki hkj hkm => ?_⟩
  refine huniq k i m hki hkm (d k i j hki hkj ≪≫ d k j m hkj hkm) ⟨?_, ?_⟩
  · rw [Iso.trans_hom, ← Category.assoc, (hd k i j hki hkj).1, (hd k j m hkj hkm).1]
  · have hmap : ((completionFunctor k.1.toScheme (I.comap k.1.ι)).map
          (d k i j hki hkj ≪≫ d k j m hkj hkm).hom).hom =
        ((completionFunctor k.1.toScheme (I.comap k.1.ι)).map (d k i j hki hkj).hom).hom ≫
          ((completionFunctor k.1.toScheme (I.comap k.1.ι)).map (d k j m hkj hkm).hom).hom := by
      rw [Iso.trans_hom, Functor.map_comp]
      exact fullSubcategory_comp_hom _ _
    rw [hmap, Category.assoc, (hd k j m hkj hkm).2, (hd k i j hki hkj).2]

/-! ### The comparisons as maps of sections over an open of `X` -/

/-- The direct image of a coherent module on an open subscheme, as a sheaf of modules on `X`.
Its sections over an open `V` of `X` are the sections of the coherent module over the preimage
of `V`. -/
public def coherentModulesPushforward {X V : Scheme.{u}} (f : V ⟶ X) [IsOpenImmersion f]
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules V.ringCatSheaf) : X.Modules :=
  (Scheme.Modules.pushforward f).obj M.obj

/-- **The direct image of a module restricted back along a factorization of the inclusion.** This
is the counit `AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso` of Mathlib, read
along a factorization `g ≫ f = h` of the morphism one restricts along. -/
public def restrictCoherentPushforwardCompIso {X Y V : Scheme.{u}} (g : V ⟶ Y) (f : Y ⟶ X)
    (h : V ⟶ X) [IsOpenImmersion g] [IsOpenImmersion f] [IsOpenImmersion h] (hgf : g ≫ f = h)
    (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor h).obj ((Scheme.Modules.pushforward f).obj M) ≅
      (Scheme.Modules.restrictFunctor g).obj M :=
  (Scheme.Modules.restrictFunctorCongr hgf).symm.app ((Scheme.Modules.pushforward f).obj M) ≪≫
    (Scheme.Modules.restrictFunctorComp g f).app ((Scheme.Modules.pushforward f).obj M) ≪≫
      (Scheme.Modules.restrictFunctor g).mapIso
        ((Scheme.Modules.restrictFunctorAdjCounitIso f).app M)

/-- The direct image of a coherent module is quasi-coherent on its own open subscheme. -/
public theorem isQuasicoherent_restrict_coherentModulesPushforward {X V : Scheme.{u}} (f : V ⟶ X)
    [IsOpenImmersion f] (M : AlgebraicGeometry.SheafOfModules.CoherentModules V.ringCatSheaf) :
    ((coherentModulesPushforward f M).restrict f).IsQuasicoherent :=
  have : M.obj.IsCoherent := M.property
  Stacks.Descent.isQuasicoherent_of_iso
    ((Scheme.Modules.restrictFunctorAdjCounitIso f).app M.obj).symm
    (isQuasicoherent_of_isCoherent M.obj)

/-- The direct image of a coherent module is of finite type on its own open subscheme. -/
public theorem isFiniteType_restrict_coherentModulesPushforward {X V : Scheme.{u}} (f : V ⟶ X)
    [IsOpenImmersion f] (M : AlgebraicGeometry.SheafOfModules.CoherentModules V.ringCatSheaf) :
    ((coherentModulesPushforward f M).restrict f).IsFiniteType :=
  Stacks.Coherent.isFiniteType_of_iso_local
    ((Scheme.Modules.restrictFunctorAdjCounitIso f).app M.obj).symm M.property.isFiniteType

/-- The action on sections of a composite of two morphisms of restrictions. -/
private theorem localApp_comp {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N P : Y.Modules} (ψ : M.restrict f ⟶ N.restrict f) (χ : N.restrict f ⟶ P.restrict f)
    {W : X.Opens} {V : Y.Opens} (hWV : f ''ᵁ W = V) :
    Stacks.AlgebraicGeometry.ModuleHomGlue.localApp f (ψ ≫ χ) hWV =
      Stacks.AlgebraicGeometry.ModuleHomGlue.localApp f ψ hWV ≫
        Stacks.AlgebraicGeometry.ModuleHomGlue.localApp f χ hWV := by
  subst hWV
  rfl

/-- **The action on sections is compatible with composition.** -/
public theorem localAppOpen_comp {X : Scheme.{u}} (U : X.Opens) {M N P : X.Modules}
    (ψ : M.restrict U.ι ⟶ N.restrict U.ι) (χ : N.restrict U.ι ⟶ P.restrict U.ι)
    {V : X.Opens} (hV : V ≤ U) :
    Stacks.Coherent.localAppOpen U (ψ ≫ χ) hV =
      Stacks.Coherent.localAppOpen U ψ hV ≫ Stacks.Coherent.localAppOpen U χ hV :=
  localApp_comp U.ι ψ χ _

/-- The action on sections of a composite, on an element. -/
public theorem localAppOpen_comp_apply {X : Scheme.{u}} (U : X.Opens) {M N P : X.Modules}
    (ψ : M.restrict U.ι ⟶ N.restrict U.ι) (χ : N.restrict U.ι ⟶ P.restrict U.ι)
    {V : X.Opens} (hV : V ≤ U) (x : Γ(M, V)) :
    Stacks.Coherent.localAppOpen U χ hV (Stacks.Coherent.localAppOpen U ψ hV x) =
      Stacks.Coherent.localAppOpen U (ψ ≫ χ) hV x := by
  rw [localAppOpen_comp]
  rfl

/-- The action on sections of the identity. -/
private theorem localAppOpen_id_apply {X : Scheme.{u}} (U : X.Opens) {M : X.Modules}
    {V : X.Opens} (hV : V ≤ U) (x : Γ(M, V)) :
    Stacks.Coherent.localAppOpen U (𝟙 (M.restrict U.ι)) hV x = x := by
  rw [← CategoryTheory.Functor.map_id (Scheme.Modules.restrictFunctor U.ι) M,
    Stacks.Coherent.localAppOpen_restrictFunctor_map]
  rfl

/-- **An isomorphism of the restrictions to an open acts on the sections over any smaller open as
a linear equivalence.** -/
public def localAppOpenEquiv {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules}
    (ψ : M.restrict U.ι ≅ N.restrict U.ι) {V : X.Opens} (hV : V ≤ U) :
    Γ(M, V) ≃ₗ[Γ(X, V)] Γ(N, V) where
  toFun x := Stacks.Coherent.localAppOpen U ψ.hom hV x
  map_add' x y := map_add _ x y
  map_smul' r s := Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_smul U.ι ψ.hom _ r s
  invFun x := Stacks.Coherent.localAppOpen U ψ.inv hV x
  left_inv x := by
    change Stacks.Coherent.localAppOpen U ψ.inv hV
      (Stacks.Coherent.localAppOpen U ψ.hom hV x) = x
    rw [localAppOpen_comp_apply, ψ.hom_inv_id, localAppOpen_id_apply]
  right_inv x := by
    change Stacks.Coherent.localAppOpen U ψ.hom hV
      (Stacks.Coherent.localAppOpen U ψ.inv hV x) = x
    rw [localAppOpen_comp_apply, ψ.inv_hom_id, localAppOpen_id_apply]

/-- The restriction to `W` of the direct image of a coherent module on an affine open `U ⊇ W`,
identified with the restriction of that module to `W`. -/
public def coherentModulesPushforwardRestrictIso {X : Scheme.{u}} [IsLocallyNoetherian X]
    {U W : X.Opens} (hWU : W ≤ U)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf) :
    (coherentModulesPushforward U.ι M).restrict W.ι ≅
      (restrictCoherentModules (X.homOfLE hWU) M).obj :=
  restrictCoherentPushforwardCompIso (X.homOfLE hWU) U.ι W.ι (X.homOfLE_ι hWU) M.obj

/-- The comparison of the restrictions to `W` of two direct images, from a comparison of the two
restricted coherent modules. -/
public def overlapRestrictIso {X : Scheme.{u}} [IsLocallyNoetherian X] {U U' W : X.Opens}
    (hWU : W ≤ U) (hWU' : W ≤ U')
    {M : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    {M' : AlgebraicGeometry.SheafOfModules.CoherentModules U'.toScheme.ringCatSheaf}
    (e : restrictCoherentModules (X.homOfLE hWU) M ≅
      restrictCoherentModules (X.homOfLE hWU') M') :
    (coherentModulesPushforward U.ι M).restrict W.ι ≅
      (coherentModulesPushforward U'.ι M').restrict W.ι :=
  coherentModulesPushforwardRestrictIso hWU M ≪≫ underlyingObjIso e ≪≫
    (coherentModulesPushforwardRestrictIso hWU' M').symm

/-- The comparisons of `Stacks.Algebraization.overlapRestrictIso` compose. -/
public theorem overlapRestrictIso_comp {X : Scheme.{u}} [IsLocallyNoetherian X]
    {U U' U'' W : X.Opens} (hWU : W ≤ U) (hWU' : W ≤ U') (hWU'' : W ≤ U'')
    {M : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    {M' : AlgebraicGeometry.SheafOfModules.CoherentModules U'.toScheme.ringCatSheaf}
    {M'' : AlgebraicGeometry.SheafOfModules.CoherentModules U''.toScheme.ringCatSheaf}
    (e : restrictCoherentModules (X.homOfLE hWU) M ≅
      restrictCoherentModules (X.homOfLE hWU') M')
    (e' : restrictCoherentModules (X.homOfLE hWU') M' ≅
      restrictCoherentModules (X.homOfLE hWU'') M'') :
    (overlapRestrictIso hWU hWU' e).hom ≫ (overlapRestrictIso hWU' hWU'' e').hom =
      (overlapRestrictIso hWU hWU'' (e ≪≫ e')).hom :=
  comp_cancel_mid _ _ _ _ _ _ (coherentModulesPushforwardRestrictIso hWU' M').inv_hom_id

/-- **The overlap comparisons as maps of sections over an open of `X`, with their cocycle
identity.** A family of isomorphisms of the restrictions of coherent modules on the opens `W`
contained in two members of the family, satisfying the cocycle identity on a triple overlap,
becomes a family of linear equivalences of the sections over `W` of the direct images
`Stacks.Algebraization.coherentModulesPushforward`, satisfying the cocycle identity there. -/
public theorem exists_sectionComparison_of_sheafComparison {X : Scheme.{u}}
    [IsLocallyNoetherian X] {ι : Type*} (U : ι → X.Opens)
    (F : ∀ i : ι, AlgebraicGeometry.SheafOfModules.CoherentModules (U i).toScheme.ringCatSheaf)
    (good : X.Opens → ι → Prop) (hgood : ∀ (W : X.Opens) (i : ι), good W i → W ≤ U i)
    (d : ∀ (W : X.Opens) (i j : ι) (hi : good W i) (hj : good W j),
      restrictCoherentModules (X.homOfLE (hgood W i hi)) (F i) ≅
        restrictCoherentModules (X.homOfLE (hgood W j hj)) (F j))
    (hcoc : ∀ (W : X.Opens) (i j m : ι) (hi : good W i) (hj : good W j) (hm : good W m),
      d W i j hi hj ≪≫ d W j m hj hm = d W i m hi hm) :
    ∃ e : ∀ (W : X.Opens) (i j : ι), good W i → good W j →
        Γ(coherentModulesPushforward (U i).ι (F i), W) ≃ₗ[Γ(X, W)]
          Γ(coherentModulesPushforward (U j).ι (F j), W),
      ∀ (W : X.Opens) (i j m : ι) (hi : good W i) (hj : good W j) (hm : good W m)
        (s : Γ(coherentModulesPushforward (U i).ι (F i), W)),
        e W j m hj hm (e W i j hi hj s) = e W i m hi hm s := by
  refine ⟨fun W i j hi hj =>
    localAppOpenEquiv W (overlapRestrictIso (hgood W i hi) (hgood W j hj) (d W i j hi hj))
      le_rfl, fun W i j m hi hj hm s => ?_⟩
  have hstep := localAppOpen_comp_apply W
    (overlapRestrictIso (hgood W i hi) (hgood W j hj) (d W i j hi hj)).hom
    (overlapRestrictIso (hgood W j hj) (hgood W m hm) (d W j m hj hm)).hom (le_refl W) s
  rwa [overlapRestrictIso_comp, hcoc W i j m hi hj hm] at hstep

/-! ### The comparisons on sections are restriction maps of one presheaf -/

/-- **The image of an open under the inclusion `W ⟶ U` of one open of `X` into another is the
preimage under `U.ι` of its image under `W.ι`.** -/
public theorem homOfLE_image_eq_ι_preimage_image {X : Scheme.{u}} {U W : X.Opens} (hWU : W ≤ U)
    (A : W.toScheme.Opens) : X.homOfLE hWU ''ᵁ A = U.ι ⁻¹ᵁ (W.ι ''ᵁ A) := by
  have key : ∀ (j : W.toScheme ⟶ U.toScheme) (k : W.toScheme ⟶ X) [IsOpenImmersion j]
      [IsOpenImmersion k], j ≫ U.ι = k → j ''ᵁ A = U.ι ⁻¹ᵁ (k ''ᵁ A) := by
    intro j k _ _ hj
    subst hj
    rw [Scheme.Hom.comp_image, Scheme.Hom.preimage_image_eq]
  exact key (X.homOfLE hWU) W.ι (X.homOfLE_ι hWU)

/-- Three restriction maps of one presheaf compose to a single restriction map: the category of
opens is thin. -/
private theorem presheafMap_comp₃_eq_map {X : Scheme.{u}} (M : X.Modules)
    {P Q R S : (X.Opens)ᵒᵖ} (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ S) (a' : P ⟶ S) :
    M.presheaf.map a ≫ M.presheaf.map b ≫ M.presheaf.map c = M.presheaf.map a' := by
  rw [← Functor.map_comp, ← Functor.map_comp, Subsingleton.elim (a ≫ b ≫ c) a']

/-- `Stacks.Algebraization.presheafMap_comp₃_eq_map` with the composite grouped to the left. -/
private theorem presheafMap_comp₃_assoc_eq_map {X : Scheme.{u}} (M : X.Modules)
    {P Q R S : (X.Opens)ᵒᵖ} (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ S) (a' : P ⟶ S) :
    (M.presheaf.map a ≫ M.presheaf.map b) ≫ M.presheaf.map c = M.presheaf.map a' := by
  rw [← Functor.map_comp, ← Functor.map_comp, Subsingleton.elim ((a ≫ b) ≫ c) a']

/-- The counit of Mathlib's restriction adjunction acts on the sections over an open as a
restriction map of the presheaf. This is
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction_counit_app_app` read on
`AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso`, which is the same natural
transformation. -/
private theorem restrictCounit_hom_app_app {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g]
    (F : X.Modules) (A : X.Opens) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorAdjCounitIso g).hom.app F) A =
      F.presheaf.map (eqToHom (g.preimage_image_eq A).symm).op := rfl

/-- The inverse of the counit of Mathlib's restriction adjunction acts on the sections over an
open as a restriction map of the presheaf. -/
private theorem restrictCounit_inv_app_app {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g]
    (F : X.Modules) (A : X.Opens) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorAdjCounitIso g).inv.app F) A =
      F.presheaf.map (eqToHom (g.preimage_image_eq A)).op := rfl

/-- **The counit coherence of `Stacks.Algebraization.restrictCoherentPushforwardCompIso`.** The
comparison of the direct image of `M` restricted back along a factorization `g ≫ f = h` with the
restriction of `M` along `g` acts on the sections over an open `A` as a *single* restriction map
of the presheaf of `M`, along any morphism of opens `i` with the right source and target. -/
public theorem restrictCoherentPushforwardCompIso_hom_app {X Y V : Scheme.{u}} (g : V ⟶ Y)
    (f : Y ⟶ X) (h : V ⟶ X) [IsOpenImmersion g] [IsOpenImmersion f] [IsOpenImmersion h]
    (hgf : g ≫ f = h) (M : Y.Modules) (A : V.Opens) (i : g ''ᵁ A ⟶ f ⁻¹ᵁ (h ''ᵁ A)) :
    Scheme.Modules.Hom.app (restrictCoherentPushforwardCompIso g f h hgf M).hom A =
      M.presheaf.map i.op := by
  simp only [restrictCoherentPushforwardCompIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Scheme.Modules.Hom.comp_app, restrictFunctor_map_app,
    restrictCounit_hom_app_app, Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.pushforward_obj_presheaf_map]
  exact presheafMap_comp₃_eq_map M _ _ _ _

/-- **The inverse of `Stacks.Algebraization.restrictCoherentPushforwardCompIso` on sections.** It
acts on the sections over an open `A` as a single restriction map of the presheaf of `M`. -/
public theorem restrictCoherentPushforwardCompIso_inv_app {X Y V : Scheme.{u}} (g : V ⟶ Y)
    (f : Y ⟶ X) (h : V ⟶ X) [IsOpenImmersion g] [IsOpenImmersion f] [IsOpenImmersion h]
    (hgf : g ≫ f = h) (M : Y.Modules) (A : V.Opens) (i : f ⁻¹ᵁ (h ''ᵁ A) ⟶ g ''ᵁ A) :
    Scheme.Modules.Hom.app (restrictCoherentPushforwardCompIso g f h hgf M).inv A =
      M.presheaf.map i.op := by
  simp only [restrictCoherentPushforwardCompIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.app_inv, Scheme.Modules.Hom.comp_app, restrictFunctor_map_app,
    restrictCounit_inv_app_app, Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.pushforward_obj_presheaf_map]
  exact presheafMap_comp₃_assoc_eq_map M _ _ _ _

/-- **The identification of the sections of a direct image over a smaller open is a restriction
map.** This is `Stacks.Algebraization.restrictCoherentPushforwardCompIso_hom_app` at the
factorization `AlgebraicGeometry.Scheme.homOfLE_ι`. -/
public theorem coherentModulesPushforwardRestrictIso_hom_app {X : Scheme.{u}}
    [IsLocallyNoetherian X] {U W : X.Opens} (hWU : W ≤ U)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf)
    (A : W.toScheme.Opens) (i : X.homOfLE hWU ''ᵁ A ⟶ U.ι ⁻¹ᵁ (W.ι ''ᵁ A)) :
    Scheme.Modules.Hom.app (coherentModulesPushforwardRestrictIso hWU M).hom A =
      (Scheme.Modules.presheaf (X := U.toScheme) M.obj).map i.op :=
  restrictCoherentPushforwardCompIso_hom_app (X.homOfLE hWU) U.ι W.ι (X.homOfLE_ι hWU) M.obj A i

/-- The inverse of `Stacks.Algebraization.coherentModulesPushforwardRestrictIso` on sections. -/
public theorem coherentModulesPushforwardRestrictIso_inv_app {X : Scheme.{u}}
    [IsLocallyNoetherian X] {U W : X.Opens} (hWU : W ≤ U)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf)
    (A : W.toScheme.Opens) (i : U.ι ⁻¹ᵁ (W.ι ''ᵁ A) ⟶ X.homOfLE hWU ''ᵁ A) :
    Scheme.Modules.Hom.app (coherentModulesPushforwardRestrictIso hWU M).inv A =
      (Scheme.Modules.presheaf (X := U.toScheme) M.obj).map i.op :=
  restrictCoherentPushforwardCompIso_inv_app (X.homOfLE hWU) U.ι W.ι (X.homOfLE_ι hWU) M.obj A i

/-- **An overlap comparison of two direct images acts on the sections over an open of `X` as the
comparison of the two restricted coherent modules, sandwiched between two restriction maps.**
The sections of the direct image of `M` over an open `V` of `X` are the sections of `M` over
`U.ι ⁻¹ᵁ V`, and the comparison is the action of `e` on the sections over `B`, read across the
equality of `X.homOfLE hki ''ᵁ B` with `U.ι ⁻¹ᵁ V`; both of the sandwiching morphisms of opens are
arguments, since the category of opens is thin. -/
public theorem localApp_overlapRestrictIso {X : Scheme.{u}} [IsLocallyNoetherian X]
    {U U' Wk : X.Opens} (hki : Wk ≤ U) (hkj : Wk ≤ U')
    {M : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    {M' : AlgebraicGeometry.SheafOfModules.CoherentModules U'.toScheme.ringCatSheaf}
    (e : restrictCoherentModules (X.homOfLE hki) M ≅ restrictCoherentModules (X.homOfLE hkj) M')
    {B : Wk.toScheme.Opens} {V : X.Opens} (hB : Wk.ι ''ᵁ B = V)
    (i₁ : X.homOfLE hki ''ᵁ B ⟶ U.ι ⁻¹ᵁ V) (i₂ : U'.ι ⁻¹ᵁ V ⟶ X.homOfLE hkj ''ᵁ B) :
    Stacks.AlgebraicGeometry.ModuleHomGlue.localApp Wk.ι
        (overlapRestrictIso hki hkj e).hom hB =
      (Scheme.Modules.presheaf (X := U.toScheme) M.obj).map i₁.op ≫
        Scheme.Modules.Hom.app e.hom.hom B ≫
          (Scheme.Modules.presheaf (X := U'.toScheme) M'.obj).map i₂.op := by
  subst hB
  change Scheme.Modules.Hom.app (coherentModulesPushforwardRestrictIso hki M).hom B ≫
      Scheme.Modules.Hom.app (underlyingObjIso e).hom B ≫
      Scheme.Modules.Hom.app (coherentModulesPushforwardRestrictIso hkj M').inv B = _
  rw [coherentModulesPushforwardRestrictIso_hom_app hki M B i₁,
    coherentModulesPushforwardRestrictIso_inv_app hkj M' B i₂]
  rfl

/-- **`Stacks.Algebraization.localApp_overlapRestrictIso` over an open `V ≤ Wk`**, in terms of
`Stacks.Coherent.localAppOpen`. -/
public theorem localAppOpen_overlapRestrictIso {X : Scheme.{u}} [IsLocallyNoetherian X]
    {U U' Wk : X.Opens} (hki : Wk ≤ U) (hkj : Wk ≤ U')
    {M : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    {M' : AlgebraicGeometry.SheafOfModules.CoherentModules U'.toScheme.ringCatSheaf}
    (e : restrictCoherentModules (X.homOfLE hki) M ≅ restrictCoherentModules (X.homOfLE hkj) M')
    {V : X.Opens} (hV : V ≤ Wk)
    (i₁ : X.homOfLE hki ''ᵁ (Wk.ι ⁻¹ᵁ V) ⟶ U.ι ⁻¹ᵁ V)
    (i₂ : U'.ι ⁻¹ᵁ V ⟶ X.homOfLE hkj ''ᵁ (Wk.ι ⁻¹ᵁ V)) :
    Stacks.Coherent.localAppOpen Wk (overlapRestrictIso hki hkj e).hom hV =
      (Scheme.Modules.presheaf (X := U.toScheme) M.obj).map i₁.op ≫
        Scheme.Modules.Hom.app e.hom.hom (Wk.ι ⁻¹ᵁ V) ≫
          (Scheme.Modules.presheaf (X := U'.toScheme) M'.obj).map i₂.op :=
  (Stacks.Coherent.localApp_eq_localAppOpen Wk (overlapRestrictIso hki hkj e).hom
        (Stacks.AlgebraicGeometry.ModuleHomGlue.image_preimage_eq_self Wk.ι
          (hV.trans Wk.ι_image_top.ge)) hV).symm.trans
    (localApp_overlapRestrictIso hki hkj e _ i₁ i₂)

/-! ### Naturality of the transported comparison isomorphism -/

/-- Regrouping a composite of four morphisms against a naturality square and a hypothesis. -/
private theorem comp_regroup_eq₃ {C : Type*} [Category C] {A B D E Z S : C} {m : A ⟶ B}
    {a' : B ⟶ D} {b' : D ⟶ E} {c : E ⟶ Z} {a : A ⟶ S} {m' : S ⟶ D} {b : S ⟶ E}
    (h₁ : m ≫ a' = a ≫ m') (h₂ : m' ≫ b' = b) : m ≫ a' ≫ b' ≫ c = a ≫ b ≫ c := by
  rw [← Category.assoc m, h₁, Category.assoc, ← Category.assoc m', h₂]

/-- **`Stacks.Algebraization.restrictedAlgebraizationIsoDual` is natural in the pair `(F, β)`.**
If `φ : F ⟶ F'` carries `β'` to `β` after completion, then its restriction carries the
transported `β'` to the transported `β`. -/
public theorem restrictedAlgebraizationIsoDual_naturality {Y V : Scheme.{u}} (g : V ⟶ Y)
    [IsOpenImmersion g] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] (K : Y.IdealSheafData)
    (Ssys : Stacks.Coherent.CoherentAdicSystems K)
    {F F' : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf} (φ : F ⟶ F')
    (β : ((completionFunctor Y K).obj F).obj ≅ Ssys.obj)
    (β' : ((completionFunctor Y K).obj F').obj ≅ Ssys.obj)
    (hφ : ((completionFunctor Y K).map φ).hom ≫ β'.hom = β.hom) :
    ((completionFunctor V (K.comap g)).map (restrictCoherentModulesMap g φ)).hom ≫
        (restrictedAlgebraizationIsoDual g K Ssys F' β').hom =
      (restrictedAlgebraizationIsoDual g K Ssys F β).hom := by
  have hw : Functor.whiskerRight (((completionFunctor Y K).map φ).hom)
        (Scheme.Modules.restrictFunctor g) ≫
      Functor.whiskerRight β'.hom (Scheme.Modules.restrictFunctor g) =
      Functor.whiskerRight β.hom (Scheme.Modules.restrictFunctor g) := by
    rw [← Functor.whiskerRight_comp, hφ]
  change ((completionFunctor V (K.comap g)).map (restrictCoherentModulesMap g φ)).hom ≫
      (completionRestrictOpenIso g K F').inv ≫
        Functor.whiskerRight β'.hom (Scheme.Modules.restrictFunctor g) =
    (completionRestrictOpenIso g K F).inv ≫
      Functor.whiskerRight β.hom (Scheme.Modules.restrictFunctor g)
  exact comp_assoc_eq_comp_of_eq₂ (completionRestrictOpenIso_inv_naturality g K φ).symm hw

/-- **`Stacks.Algebraization.compRestrictedAlgebraizationIso` is natural in the pair `(F, β)`.** -/
public theorem compRestrictedAlgebraizationIso_naturality {X Y V : Scheme.{u}} (g : V ⟶ Y)
    (f : Y ⟶ X) [IsOpenImmersion g] [IsOpenImmersion f] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian V] (I : X.IdealSheafData)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    {F F' : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf} (φ : F ⟶ F')
    (β : ((completionFunctor Y (I.comap f)).obj F).obj ≅
      ((Stacks.Coherent.restrictFunctor I f).obj Fsys).obj)
    (β' : ((completionFunctor Y (I.comap f)).obj F').obj ≅
      ((Stacks.Coherent.restrictFunctor I f).obj Fsys).obj)
    (hφ : ((completionFunctor Y (I.comap f)).map φ).hom ≫ β'.hom = β.hom) :
    ((completionFunctor V (I.comap (g ≫ f))).map (restrictCoherentModulesMap g φ)).hom ≫
        (compRestrictedAlgebraizationIso g f I Fsys F' β').hom =
      (compRestrictedAlgebraizationIso g f I Fsys F β).hom := by
  change ((completionFunctor V (I.comap (g ≫ f))).map (restrictCoherentModulesMap g φ)).hom ≫
      (completionCongrIso (Scheme.IdealSheafData.comap_comp I g f)
          (restrictCoherentModules g F')).hom ≫
        (restrictedAlgebraizationIsoDual g (I.comap f)
            ((Stacks.Coherent.restrictFunctor I f).obj Fsys) F' β').hom ≫
          (restrictedSystemCompIso g f I Fsys).inv =
    (completionCongrIso (Scheme.IdealSheafData.comap_comp I g f)
        (restrictCoherentModules g F)).hom ≫
      (restrictedAlgebraizationIsoDual g (I.comap f)
          ((Stacks.Coherent.restrictFunctor I f).obj Fsys) F β).hom ≫
        (restrictedSystemCompIso g f I Fsys).inv
  exact comp_regroup_eq₃
    (completionCongrIso_naturality (Scheme.IdealSheafData.comap_comp I g f)
      (restrictCoherentModulesMap g φ))
    (restrictedAlgebraizationIsoDual_naturality g (I.comap f)
      ((Stacks.Coherent.restrictFunctor I f).obj Fsys) φ β β' hφ)

/-- **`Stacks.Algebraization.restrictedAlgebraizationIsoOfLE` is natural in the pair `(F, β)`.**
A morphism of the local algebraizations over `U` carrying `β'` to `β` restricts to one over
`W ≤ U` carrying the transported `β'` to the transported `β`. -/
public theorem restrictedAlgebraizationIsoOfLE_naturality {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I) {U W : X.Opens} (hWU : W ≤ U)
    {F F' : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    (φ : F ⟶ F')
    (β : ((completionFunctor U.toScheme (I.comap U.ι)).obj F).obj ≅
      ((Stacks.Coherent.restrictFunctor I U.ι).obj Fsys).obj)
    (β' : ((completionFunctor U.toScheme (I.comap U.ι)).obj F').obj ≅
      ((Stacks.Coherent.restrictFunctor I U.ι).obj Fsys).obj)
    (hφ : ((completionFunctor U.toScheme (I.comap U.ι)).map φ).hom ≫ β'.hom = β.hom) :
    ((completionFunctor W.toScheme (I.comap W.ι)).map
          (restrictCoherentModulesMap (X.homOfLE hWU) φ)).hom ≫
        (restrictedAlgebraizationIsoOfLE I Fsys hWU β').hom =
      (restrictedAlgebraizationIsoOfLE I Fsys hWU β).hom := by
  change ((completionFunctor W.toScheme (I.comap W.ι)).map
        (restrictCoherentModulesMap (X.homOfLE hWU) φ)).hom ≫
      (completionCongrIso (congrArg (fun m => I.comap m) (X.homOfLE_ι hWU).symm)
          (restrictCoherentModules (X.homOfLE hWU) F')).hom ≫
        (compRestrictedAlgebraizationIso (X.homOfLE hWU) U.ι I Fsys F' β').hom ≫
          (restrictedSystemCongrIso I Fsys (X.homOfLE_ι hWU)).hom =
    (completionCongrIso (congrArg (fun m => I.comap m) (X.homOfLE_ι hWU).symm)
        (restrictCoherentModules (X.homOfLE hWU) F)).hom ≫
      (compRestrictedAlgebraizationIso (X.homOfLE hWU) U.ι I Fsys F β).hom ≫
        (restrictedSystemCongrIso I Fsys (X.homOfLE_ι hWU)).hom
  exact comp_regroup_eq₃
    (completionCongrIso_naturality (congrArg (fun m => I.comap m) (X.homOfLE_ι hWU).symm)
      (restrictCoherentModulesMap (X.homOfLE hWU) φ))
    (compRestrictedAlgebraizationIso_naturality (X.homOfLE hWU) U.ι I Fsys φ β β' hφ)

/-! ### Associativity of the transported comparison isomorphism -/

/-- A composite of six restriction maps of one presheaf agrees with a composite of two with the
same source and target: the category of opens is thin. -/
private theorem presheafMap_comp₆_eq₂ {X : Scheme.{u}} (M : X.Modules)
    {P₀ P₁ P₂ P₃ P₄ P₅ P₆ Q₁ : (X.Opens)ᵒᵖ} (a₁ : P₀ ⟶ P₁) (a₂ : P₁ ⟶ P₂) (a₃ : P₂ ⟶ P₃)
    (a₄ : P₃ ⟶ P₄) (a₅ : P₄ ⟶ P₅) (a₆ : P₅ ⟶ P₆) (b₁ : P₀ ⟶ Q₁) (b₂ : Q₁ ⟶ P₆) :
    M.presheaf.map a₁ ≫ M.presheaf.map a₂ ≫ (M.presheaf.map a₃ ≫ M.presheaf.map a₄) ≫
        (M.presheaf.map a₅ ≫ M.presheaf.map a₆) =
      M.presheaf.map b₁ ≫ M.presheaf.map b₂ := by
  simp only [← Functor.map_comp]
  exact congrArg M.presheaf.map (Subsingleton.elim _ _)

/-- Regrouping a composite against a naturality square and a second naturality square. -/
private theorem comp_nat_regroup {C : Type*} [Category C] {A B D E Z S : C} {k₁ : A ⟶ B}
    {k₂ : B ⟶ D} {a : D ⟶ E} {m : B ⟶ S} {k₂' : S ⟶ E} {w : A ⟶ Z} {k₁' : Z ⟶ S}
    (h₁ : k₂ ≫ a = m ≫ k₂') (h₂ : k₁ ≫ m = w ≫ k₁') :
    k₁ ≫ k₂ ≫ a = w ≫ k₁' ≫ k₂' := by
  rw [h₁, ← Category.assoc, h₂, Category.assoc]

/-- Regrouping a composite of four morphisms against a naturality square and a coherence. -/
private theorem comp_regroup_eq₅ {C : Type*} [Category C] {A B D E Z S : C} {k : A ⟶ B}
    {a : B ⟶ D} {b : D ⟶ E} {c : E ⟶ Z} {w : A ⟶ S} {k' : S ⟶ D} {ψ : S ⟶ Z}
    (h₁ : k ≫ a = w ≫ k') (h₂ : k' ≫ b ≫ c = ψ) : k ≫ (a ≫ b) ≫ c = w ≫ ψ := by
  rw [Category.assoc a, ← Category.assoc k, h₁, Category.assoc, h₂]

/-- Combining a naturality square and three equations of composites into an equation of
composites. -/
private theorem comp_chain_eq {C : Type*} [Category C] {A₀ B₀ D₀ E₀ Z₀ S₀ T₀ R₀ : C}
    {K : A₀ ⟶ B₀} {P' : B₀ ⟶ D₀} {Z : D₀ ⟶ Z₀} {Aa : B₀ ⟶ E₀} {c : E₀ ⟶ Z₀} {a : B₀ ⟶ S₀}
    {b : S₀ ⟶ E₀} {w : A₀ ⟶ T₀} {k' : T₀ ⟶ S₀} {ψ : T₀ ⟶ Z₀} {Pr : A₀ ⟶ R₀} {Y : R₀ ⟶ Z₀}
    (h₁ : P' ≫ Z = Aa ≫ c) (hA : Aa = a ≫ b) (h₂ : K ≫ a = w ≫ k')
    (h₃ : k' ≫ b ≫ c = ψ) (h₄ : Pr ≫ Y = w ≫ ψ) : (K ≫ P') ≫ Z = Pr ≫ Y := by
  rw [Category.assoc, h₁, hA, h₄]
  exact comp_regroup_eq₅ h₂ h₃

/-- **`Stacks.Algebraization.restrictedSystemCompIso` acts on a level as Mathlib's comparison of
the two restrictions.** -/
public theorem restrictedSystemCompIso_inv_app {X Y V : Scheme.{u}} (g : V ⟶ Y) (f : Y ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (I : X.IdealSheafData) (Fsys : Stacks.Coherent.CoherentAdicSystems I) (n : ℕᵒᵖ) :
    (restrictedSystemCompIso g f I Fsys).inv.app n =
      (Scheme.Modules.restrictFunctorComp g f).inv.app (Fsys.obj.obj n) := rfl

/-- **`Stacks.Algebraization.restrictedSystemCongrIso` acts on a level as Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr`.** -/
public theorem restrictedSystemCongrIso_hom_app {X V : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (Fsys : Stacks.Coherent.CoherentAdicSystems I) {h h' : V ⟶ X}
    [IsOpenImmersion h] [IsOpenImmersion h'] (e : h = h') (n : ℕᵒᵖ) :
    (restrictedSystemCongrIso I Fsys e).hom.app n =
      (Scheme.Modules.restrictFunctorCongr e).hom.app (Fsys.obj.obj n) := by
  cases e
  refine Scheme.Modules.hom_ext _ _ fun A => ?_
  exact ((Scheme.Modules.presheaf (X := X) (Fsys.obj.obj n)).map_id _).symm.trans
    (congrArg (Scheme.Modules.presheaf (X := X) (Fsys.obj.obj n)).map (Subsingleton.elim _ _))

/-- **The associativity coherence of the restriction transports on the target side.** For
`V ≤ W ≤ U`, restricting a module on `X` to `U` and then transporting down to `V` in two steps
agrees with transporting down in one, through
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr`. -/
public theorem restrictFunctorTransport_assoc_app {X : Scheme.{u}} {U W V : X.Opens}
    (hWU : W ≤ U) (hVW : V ≤ W) (S : X.Modules) :
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_homOfLE hVW hWU).symm).hom.app
          ((Scheme.Modules.restrictFunctor U.ι).obj S) ≫
        (Scheme.Modules.restrictFunctorComp (X.homOfLE hVW) (X.homOfLE hWU)).hom.app
          ((Scheme.Modules.restrictFunctor U.ι).obj S) ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE hVW)).map
          ((Scheme.Modules.restrictFunctorComp (X.homOfLE hWU) U.ι).inv.app S ≫
            (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hWU)).hom.app S) ≫
        ((Scheme.Modules.restrictFunctorComp (X.homOfLE hVW) W.ι).inv.app S ≫
          (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hVW)).hom.app S) =
    (Scheme.Modules.restrictFunctorComp (X.homOfLE (hVW.trans hWU)) U.ι).inv.app S ≫
      (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι (hVW.trans hWU))).hom.app S := by
  refine Scheme.Modules.hom_ext _ _ fun A => ?_
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app, restrictFunctor_map_app,
    Scheme.Modules.restrict_map]
  exact presheafMap_comp₆_eq₂ S _ _ _ _ _ _ _ _

/-- The level-`n` component of `Stacks.Algebraization.restrictedAlgebraizationIsoDual`. -/
private theorem restrictedAlgebraizationIsoDual_hom_app {Y V : Scheme.{u}} (g : V ⟶ Y)
    [IsOpenImmersion g] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] (K : Y.IdealSheafData)
    (Ssys : Stacks.Coherent.CoherentAdicSystems K)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (β : ((completionFunctor Y K).obj F).obj ≅ Ssys.obj) (n : ℕᵒᵖ) :
    (restrictedAlgebraizationIsoDual g K Ssys F β).hom.app n =
      (completionRestrictOpenIso g K F).inv.app n ≫
        (Scheme.Modules.restrictFunctor g).map (β.hom.app n) := rfl

/-- The level-`n` component of `Stacks.Algebraization.compRestrictedAlgebraizationIso`. -/
private theorem compRestrictedAlgebraizationIso_hom_app {X Y V : Scheme.{u}} (g : V ⟶ Y)
    (f : Y ⟶ X) [IsOpenImmersion g] [IsOpenImmersion f] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian V] (I : X.IdealSheafData)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (β : ((completionFunctor Y (I.comap f)).obj F).obj ≅
      ((Stacks.Coherent.restrictFunctor I f).obj Fsys).obj) (n : ℕᵒᵖ) :
    (compRestrictedAlgebraizationIso g f I Fsys F β).hom.app n =
      (completionCongrIso (Scheme.IdealSheafData.comap_comp I g f)
          (restrictCoherentModules g F)).hom.app n ≫
        (restrictedAlgebraizationIsoDual g (I.comap f)
            ((Stacks.Coherent.restrictFunctor I f).obj Fsys) F β).hom.app n ≫
          (restrictedSystemCompIso g f I Fsys).inv.app n := rfl

/-- The level-`n` component of a threefold composite of isomorphisms of functors. -/
private theorem isoTrans₃_hom_app {C J : Type*} [Category C] [Category J] {A B D E : J ⥤ C}
    (a : A ≅ B) (b : B ≅ D) (c : D ≅ E) (n : J) :
    (a ≪≫ b ≪≫ c).hom.app n = a.hom.app n ≫ b.hom.app n ≫ c.hom.app n := rfl

/-- `Stacks.Algebraization.restrictedAlgebraizationIsoOfLE` unfolded, at the level of
isomorphisms. -/
private theorem restrictedAlgebraizationIsoOfLE_eq {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (Fsys : Stacks.Coherent.CoherentAdicSystems I) {U W : X.Opens}
    (hWU : W ≤ U) (F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf)
    (β : ((completionFunctor U.toScheme (I.comap U.ι)).obj F).obj ≅
      ((Stacks.Coherent.restrictFunctor I U.ι).obj Fsys).obj) :
    restrictedAlgebraizationIsoOfLE I Fsys hWU β =
      completionCongrIso (congrArg (fun m => I.comap m) (X.homOfLE_ι hWU).symm)
          (restrictCoherentModules (X.homOfLE hWU) F) ≪≫
        compRestrictedAlgebraizationIso (X.homOfLE hWU) U.ι I Fsys F β ≪≫
          restrictedSystemCongrIso I Fsys (X.homOfLE_ι hWU) := rfl

/-- **`Stacks.Algebraization.restrictedAlgebraizationIsoDual` read through the projections.**
Precomposing it with the canonical projection of the restricted completion gives the restriction
of the projection on `Y` followed by `β`. -/
public theorem completionProjection_comp_restrictedAlgebraizationIsoDual {Y V : Scheme.{u}}
    (g : V ⟶ Y) [IsOpenImmersion g] [IsLocallyNoetherian Y] [IsLocallyNoetherian V]
    (K : Y.IdealSheafData) (Ssys : Stacks.Coherent.CoherentAdicSystems K)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (β : ((completionFunctor Y K).obj F).obj ≅ Ssys.obj) (n : ℕ) :
    completionProjection V (K.comap g) (restrictCoherentModules g F) n ≫
        (restrictedAlgebraizationIsoDual g K Ssys F β).hom.app (op n) =
      (Scheme.Modules.restrictFunctor g).map
        (completionProjection Y K F n ≫ β.hom.app (op n)) := by
  rw [restrictedAlgebraizationIsoDual_hom_app]
  exact comp_assoc_eq_of_eq₂
    (completionProjection_comp_completionRestrictOpenIso_inv g K F n)
    ((Scheme.Modules.restrictFunctor g).map_comp _ _).symm

/-- **`Stacks.Algebraization.compRestrictedAlgebraizationIso` read through the projections.** -/
public theorem completionProjection_comp_compRestrictedAlgebraizationIso {X Y V : Scheme.{u}}
    (g : V ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion g] [IsOpenImmersion f] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian V] (I : X.IdealSheafData)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (β : ((completionFunctor Y (I.comap f)).obj F).obj ≅
      ((Stacks.Coherent.restrictFunctor I f).obj Fsys).obj) (n : ℕ) :
    completionProjection V (I.comap (g ≫ f)) (restrictCoherentModules g F) n ≫
        (compRestrictedAlgebraizationIso g f I Fsys F β).hom.app (op n) =
      (Scheme.Modules.restrictFunctor g).map
          (completionProjection Y (I.comap f) F n ≫ β.hom.app (op n)) ≫
        (Scheme.Modules.restrictFunctorComp g f).inv.app (Fsys.obj.obj (op n)) := by
  rw [compRestrictedAlgebraizationIso_hom_app]
  exact comp_assoc_eq_of_eq₂ (completionProjection_comp_completionCongrIso
      (Scheme.IdealSheafData.comap_comp I g f) (restrictCoherentModules g F) n)
    (congrArg (fun z => z ≫ (restrictedSystemCompIso g f I Fsys).inv.app (op n))
      (completionProjection_comp_restrictedAlgebraizationIsoDual g (I.comap f)
        ((Stacks.Coherent.restrictFunctor I f).obj Fsys) F β n))

/-- `Stacks.Algebraization.completionProjection_comp_restrictedAlgebraizationIsoOfLE` with the
composite on the right grouped to the left. -/
private theorem completionProjection_comp_isoOfLE_aux {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (Fsys : Stacks.Coherent.CoherentAdicSystems I) {U W : X.Opens}
    (hWU : W ≤ U)
    {F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    (β : ((completionFunctor U.toScheme (I.comap U.ι)).obj F).obj ≅
      ((Stacks.Coherent.restrictFunctor I U.ι).obj Fsys).obj) (n : ℕ) :
    completionProjection W.toScheme (I.comap W.ι)
          (restrictCoherentModules (X.homOfLE hWU) F) n ≫
        (restrictedAlgebraizationIsoOfLE I Fsys hWU β).hom.app (op n) =
      ((Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map
            (completionProjection U.toScheme (I.comap U.ι) F n ≫ β.hom.app (op n)) ≫
          (Scheme.Modules.restrictFunctorComp (X.homOfLE hWU) U.ι).inv.app
            (Fsys.obj.obj (op n))) ≫
        (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hWU)).hom.app
          (Fsys.obj.obj (op n)) := by
  rw [restrictedAlgebraizationIsoOfLE_eq, isoTrans₃_hom_app, restrictedSystemCongrIso_hom_app]
  exact comp_assoc_eq_of_eq₂ (completionProjection_comp_completionCongrIso
      (congrArg (fun m => I.comap m) (X.homOfLE_ι hWU).symm)
      (restrictCoherentModules (X.homOfLE hWU) F) n)
    (congrArg (fun z => z ≫ (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hWU)).hom.app
        (Fsys.obj.obj (op n)))
      (completionProjection_comp_compRestrictedAlgebraizationIso (X.homOfLE hWU) U.ι I Fsys F
        β n))

/-- **`Stacks.Algebraization.restrictedAlgebraizationIsoOfLE` read through the projections.**
Precomposing it with the canonical projection of the completion over `W` gives the restriction to
`W` of the projection over `U` followed by `β`, read through the two transports on the target
side. -/
public theorem completionProjection_comp_restrictedAlgebraizationIsoOfLE {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I) {U W : X.Opens} (hWU : W ≤ U)
    {F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    (β : ((completionFunctor U.toScheme (I.comap U.ι)).obj F).obj ≅
      ((Stacks.Coherent.restrictFunctor I U.ι).obj Fsys).obj) (n : ℕ) :
    completionProjection W.toScheme (I.comap W.ι)
          (restrictCoherentModules (X.homOfLE hWU) F) n ≫
        (restrictedAlgebraizationIsoOfLE I Fsys hWU β).hom.app (op n) =
      (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map
          (completionProjection U.toScheme (I.comap U.ι) F n ≫ β.hom.app (op n)) ≫
        (Scheme.Modules.restrictFunctorComp (X.homOfLE hWU) U.ι).inv.app
            (Fsys.obj.obj (op n)) ≫
          (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hWU)).hom.app
            (Fsys.obj.obj (op n)) :=
  (completionProjection_comp_isoOfLE_aux I Fsys hWU β n).trans (Category.assoc _ _ _)

/-- **The canonical comparison of the two ways of restricting a coherent module from `U` to
`V ≤ W ≤ U`.** -/
public def restrictCoherentModulesTransportIso {X : Scheme.{u}} [IsLocallyNoetherian X]
    {U W V : X.Opens} (hWU : W ≤ U) (hVW : V ≤ W)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf) :
    restrictCoherentModules (X.homOfLE (hVW.trans hWU)) F ≅
      restrictCoherentModules (X.homOfLE hVW) (restrictCoherentModules (X.homOfLE hWU) F) :=
  restrictCoherentModulesCongrIso (X.homOfLE_homOfLE hVW hWU).symm F ≪≫
    restrictCoherentModulesCompIso (X.homOfLE hVW) (X.homOfLE hWU) F

/-- **`Stacks.Algebraization.restrictCoherentModulesTransportIso` is natural in the module.** -/
public theorem restrictCoherentModulesTransportIso_hom_naturality {X : Scheme.{u}}
    [IsLocallyNoetherian X] {U W V : X.Opens} (hWU : W ≤ U) (hVW : V ≤ W)
    {F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    {M : U.toScheme.Modules} (t : F.obj ⟶ M) :
    (restrictCoherentModulesTransportIso hWU hVW F).hom.hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hVW)).map
          ((Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map t) =
      (Scheme.Modules.restrictFunctor (X.homOfLE (hVW.trans hWU))).map t ≫
        ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_homOfLE hVW hWU).symm).hom.app M ≫
          (Scheme.Modules.restrictFunctorComp (X.homOfLE hVW) (X.homOfLE hWU)).hom.app M) := by
  have h₀ : (restrictCoherentModulesTransportIso hWU hVW F).hom.hom =
      (restrictCoherentModulesCongrIso (X.homOfLE_homOfLE hVW hWU).symm F).hom.hom ≫
        (restrictCoherentModulesCompIso (X.homOfLE hVW) (X.homOfLE hWU) F).hom.hom :=
    fullSubcategory_comp_hom _ _
  rw [h₀, restrictCoherentModulesCongrIso_hom_hom, restrictCoherentModulesCompIso_hom_hom]
  exact comp_nat_regroup
    ((Scheme.Modules.restrictFunctorComp (X.homOfLE hVW) (X.homOfLE hWU)).hom.naturality t).symm
    ((Scheme.Modules.restrictFunctorCongr
      (X.homOfLE_homOfLE hVW hWU).symm).hom.naturality t).symm

/-- **The associativity of `Stacks.Algebraization.restrictedAlgebraizationIsoOfLE`.** For
`V ≤ W ≤ U` the canonical comparison
`Stacks.Algebraization.restrictCoherentModulesTransportIso` carries the comparison isomorphism of
a local algebraization transported in two steps to the one transported in a single step. -/
public theorem restrictedAlgebraizationIsoOfLE_trans {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (Fsys : Stacks.Coherent.CoherentAdicSystems I) {U W V : X.Opens}
    (hWU : W ≤ U) (hVW : V ≤ W)
    {F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    (β : ((completionFunctor U.toScheme (I.comap U.ι)).obj F).obj ≅
      ((Stacks.Coherent.restrictFunctor I U.ι).obj Fsys).obj) :
    ((completionFunctor V.toScheme (I.comap V.ι)).map
          (restrictCoherentModulesTransportIso hWU hVW F).hom).hom ≫
        (restrictedAlgebraizationIsoOfLE I Fsys hVW
          (restrictedAlgebraizationIsoOfLE I Fsys hWU β)).hom =
      (restrictedAlgebraizationIsoOfLE I Fsys (hVW.trans hWU) β).hom := by
  refine completionSystemHom_ext V.toScheme (I.comap V.ι)
    (restrictCoherentModules (X.homOfLE (hVW.trans hWU)) F) _ _ fun n => ?_
  have key := comp_chain_eq
    (completionProjection_comp_restrictedAlgebraizationIsoOfLE I Fsys hVW
      (restrictedAlgebraizationIsoOfLE I Fsys hWU β) n)
    ((congrArg (Scheme.Modules.restrictFunctor (X.homOfLE hVW)).map
          (completionProjection_comp_restrictedAlgebraizationIsoOfLE I Fsys hWU β n)).trans
      ((Scheme.Modules.restrictFunctor (X.homOfLE hVW)).map_comp _ _))
    (restrictCoherentModulesTransportIso_hom_naturality hWU hVW
      (completionProjection U.toScheme (I.comap U.ι) F n ≫ β.hom.app (op n)))
    ((Category.assoc _ _ _).trans (restrictFunctorTransport_assoc_app hWU hVW
      (Fsys.obj.obj (op n))))
    (completionProjection_comp_restrictedAlgebraizationIsoOfLE I Fsys (hVW.trans hWU) β n)
  exact comp_assoc_eq_of_eq₂ (completionFunctor_map_quotient V.toScheme (I.comap V.ι)
    (restrictCoherentModulesTransportIso hWU hVW F).hom n) key

/-! ### Transitivity of the transported algebraization morphism -/

/-- A composite of four restriction maps of one presheaf agrees with any other composite of four
with the same source and target: the category of opens is thin. -/
private theorem presheafMap_comp₄_eq₄ {X : Scheme.{u}} (M : X.Modules)
    {P₀ P₁ P₂ P₃ P₄ Q₁ Q₂ Q₃ : (X.Opens)ᵒᵖ} (a₁ : P₀ ⟶ P₁) (a₂ : P₁ ⟶ P₂) (a₃ : P₂ ⟶ P₃)
    (a₄ : P₃ ⟶ P₄) (b₁ : P₀ ⟶ Q₁) (b₂ : Q₁ ⟶ Q₂) (b₃ : Q₂ ⟶ Q₃) (b₄ : Q₃ ⟶ P₄) :
    M.presheaf.map a₁ ≫ M.presheaf.map a₂ ≫ M.presheaf.map a₃ ≫ M.presheaf.map a₄ =
      M.presheaf.map b₁ ≫ M.presheaf.map b₂ ≫ M.presheaf.map b₃ ≫ M.presheaf.map b₄ := by
  simp only [← Functor.map_comp]
  exact congrArg M.presheaf.map (Subsingleton.elim _ _)

/-- Combining two naturality squares and two equations of composites into an equation of
composites. -/
private theorem comp_src_chain_eq {C : Type*} [Category C] {A B D E Z S R₁ R₂ T₁ T₂ T₃ : C}
    {c₁ : A ⟶ B} {c₂ : B ⟶ D} {bb : D ⟶ E} {c₃ : E ⟶ Z} {c₄ : Z ⟶ S} {g₃ : D ⟶ R₁}
    {bb' : R₁ ⟶ Z} {g₄ : R₁ ⟶ R₂} {dd : R₂ ⟶ S} {d₁ : A ⟶ T₁} {d₂ : T₁ ⟶ T₂}
    {d₃ : T₂ ⟶ T₃} {d₄ : T₃ ⟶ R₂} {m : T₂ ⟶ S}
    (n₁ : bb ≫ c₃ = g₃ ≫ bb') (n₂ : bb' ≫ c₄ = g₄ ≫ dd)
    (hsrc : c₁ ≫ c₂ ≫ g₃ ≫ g₄ = d₁ ≫ d₂ ≫ d₃ ≫ d₄) (hm : m = d₃ ≫ d₄ ≫ dd) :
    (c₁ ≫ c₂ ≫ bb) ≫ c₃ ≫ c₄ = d₁ ≫ d₂ ≫ m := by
  simp only [hm, Category.assoc]
  rw [reassoc_of% n₁, n₂, reassoc_of% hsrc]

/-- The underlying morphism of the inverse of
`Stacks.Algebraization.restrictCoherentModulesCongrIso`, matching
`Stacks.Algebraization.restrictCoherentModulesCongrIso_hom_hom`. -/
public theorem restrictCoherentModulesCongrIso_inv_hom {X V : Scheme.{u}}
    [IsLocallyNoetherian X] {h h' : V ⟶ X} [IsOpenImmersion h] [IsOpenImmersion h'] (e : h = h')
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    (restrictCoherentModulesCongrIso e G).inv.hom =
      (Scheme.Modules.restrictFunctorCongr e).inv.app G.obj := by
  cases e
  refine Scheme.Modules.hom_ext _ _ fun A => ?_
  exact ((Scheme.Modules.presheaf (X := X) G.obj).map_id _).symm.trans
    (congrArg (Scheme.Modules.presheaf (X := X) G.obj).map (Subsingleton.elim _ _))

/-- **The associativity coherence of the restriction transports on the source side.** For
`V ≤ W ≤ U` the two routes by which a module on `X` restricted to `V` is compared with its
restriction to `U` then down to `V` in two steps agree. -/
public theorem restrictFunctorTransport_source_assoc_app {X : Scheme.{u}} {U W V : X.Opens}
    (hWU : W ≤ U) (hVW : V ≤ W) (G : X.Modules) :
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι (hVW.trans hWU))).inv.app G ≫
        (Scheme.Modules.restrictFunctorComp (X.homOfLE (hVW.trans hWU)) U.ι).hom.app G ≫
      (Scheme.Modules.restrictFunctorCongr (X.homOfLE_homOfLE hVW hWU).symm).hom.app
          ((Scheme.Modules.restrictFunctor U.ι).obj G) ≫
        (Scheme.Modules.restrictFunctorComp (X.homOfLE hVW) (X.homOfLE hWU)).hom.app
          ((Scheme.Modules.restrictFunctor U.ι).obj G) =
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hVW)).inv.app G ≫
        (Scheme.Modules.restrictFunctorComp (X.homOfLE hVW) W.ι).hom.app G ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE hVW)).map
          ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hWU)).inv.app G) ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hVW)).map
          ((Scheme.Modules.restrictFunctorComp (X.homOfLE hWU) U.ι).hom.app G) := by
  refine Scheme.Modules.hom_ext _ _ fun A => ?_
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Scheme.Modules.restrictFunctorCongr_inv_app_app, restrictFunctor_map_app,
    Scheme.Modules.restrict_map]
  exact presheafMap_comp₄_eq₄ G _ _ _ _ _ _ _ _

/-- **The transitivity of `Stacks.Algebraization.restrictedAlgebraizationMapOfLE`.** Carrying
`b : G|_U ⟶ F` down to `V ≤ W ≤ U` in one step agrees, through the canonical comparison
`Stacks.Algebraization.restrictCoherentModulesTransportIso`, with carrying it down to `W` and
then to `V`. -/
public theorem restrictedAlgebraizationMapOfLE_trans {X : Scheme.{u}} [IsLocallyNoetherian X]
    {U W V : X.Opens} (hWU : W ≤ U) (hVW : V ≤ W)
    {G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    {F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    (b : restrictCoherentModules U.ι G ⟶ F) :
    restrictedAlgebraizationMapOfLE (hVW.trans hWU) b ≫
        (restrictCoherentModulesTransportIso hWU hVW F).hom =
      restrictedAlgebraizationMapOfLE hVW (restrictedAlgebraizationMapOfLE hWU b) := by
  refine ObjectProperty.hom_ext _ ?_
  simp only [restrictedAlgebraizationMapOfLE, compRestrictedAlgebraizationMap,
    restrictCoherentModulesTransportIso, Iso.trans_hom, fullSubcategory_comp_hom,
    restrictCoherentModulesMap_hom, restrictCoherentModulesCongrIso_inv_hom,
    restrictCoherentModulesCongrIso_hom_hom, restrictCoherentModulesCompIso_hom_hom]
  have hmc : (Scheme.Modules.restrictFunctor (X.homOfLE hVW)).map
        ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hWU)).inv.app G.obj ≫
          (Scheme.Modules.restrictFunctorComp (X.homOfLE hWU) U.ι).hom.app G.obj ≫
            (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map b.hom) =
      (Scheme.Modules.restrictFunctor (X.homOfLE hVW)).map
          ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hWU)).inv.app G.obj) ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hVW)).map
            ((Scheme.Modules.restrictFunctorComp (X.homOfLE hWU) U.ι).hom.app G.obj) ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE hVW)).map
            ((Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map b.hom) := by
    rw [Functor.map_comp, Functor.map_comp]
  exact comp_src_chain_eq
    ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_homOfLE hVW hWU).symm).hom.naturality b.hom)
    ((Scheme.Modules.restrictFunctorComp (X.homOfLE hVW) (X.homOfLE hWU)).hom.naturality b.hom)
    (restrictFunctorTransport_source_assoc_app hWU hVW G.obj) hmc

/-- An isomorphism of coherent modules restricted along an open immersion. -/
public def restrictCoherentModulesMapIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    [IsLocallyNoetherian X]
    {G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (e : G ≅ F) :
    restrictCoherentModules f G ≅ restrictCoherentModules f F :=
  ObjectProperty.isoMk _ ((Scheme.Modules.restrictFunctor f).mapIso (underlyingObjIso e))

/-! ### The overlap comparison over a smaller open is the transport of the one above it -/

/-- Two restriction maps of one presheaf compose to a restriction map. -/
public theorem presheafMap_comp₂_eq {X : Scheme.{u}} (M : X.Modules) {P Q R : (X.Opens)ᵒᵖ}
    (a : P ⟶ Q) (b : Q ⟶ R) (a' : P ⟶ R) :
    M.presheaf.map a ≫ M.presheaf.map b = M.presheaf.map a' := by
  rw [← Functor.map_comp, Subsingleton.elim (a ≫ b) a']

/-- Chaining three given composites through a composite of four morphisms. -/
private theorem comp_chain3_eq {C : Type*} [Category C] {A₁ A₂ A₃ A₄ A₅ : C} {a : A₁ ⟶ A₂}
    {t₁ : A₂ ⟶ A₃} {m : A₃ ⟶ A₄} {t₂ : A₄ ⟶ A₅} {a' : A₁ ⟶ A₃} {b' : A₁ ⟶ A₄} {b : A₁ ⟶ A₅}
    (e₁ : a ≫ t₁ = a') (e₂ : a' ≫ m = b') (e₃ : b' ≫ t₂ = b) : a ≫ t₁ ≫ m ≫ t₂ = b := by
  rw [← Category.assoc, ← Category.assoc, e₁, e₂, e₃]

/-- Chaining three given composites through a composite of three morphisms, from the right. -/
private theorem comp_chain3_eq_right {C : Type*} [Category C] {A₁ A₂ A₃ A₄ Z : C}
    {c₁ : A₁ ⟶ A₂} {c₂ : A₂ ⟶ A₃} {c₃ : A₃ ⟶ A₄} {z : A₄ ⟶ Z} {y₃ : A₃ ⟶ Z} {y₂ : A₂ ⟶ Z}
    {y₁ : A₁ ⟶ Z} (f₃ : c₃ ≫ z = y₃) (f₂ : c₂ ≫ y₃ = y₂) (f₁ : c₁ ≫ y₂ = y₁) :
    (c₁ ≫ c₂ ≫ c₃) ≫ z = y₁ := by
  rw [Category.assoc, Category.assoc, f₃, f₂, f₁]

/-- Reading a given composite through the inverse of an isomorphism. -/
private theorem comp_cancel_inv_chain {C : Type*} [Category C] {A B D : C} (x : A ⟶ B)
    (y : B ⟶ A) (z : B ⟶ D) (w : A ⟶ D) (hxy : x ≫ y = 𝟙 A) (h : y ≫ w = z) : x ≫ z = w := by
  rw [← h, ← Category.assoc, hxy, Category.id_comp]

/-- The underlying morphism of the inverse of
`Stacks.Algebraization.restrictCoherentModulesCompIso`. -/
public theorem restrictCoherentModulesCompIso_inv_hom {X Y V : Scheme.{u}} (g : V ⟶ Y)
    (f : Y ⟶ X) [IsOpenImmersion g] [IsOpenImmersion f] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y]
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    (restrictCoherentModulesCompIso g f G).inv.hom =
      (Scheme.Modules.restrictFunctorComp g f).inv.app G.obj := rfl

/-- The underlying morphism of `Stacks.Algebraization.restrictCoherentModulesMapIso`. -/
public theorem restrictCoherentModulesMapIso_hom {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] [IsLocallyNoetherian X]
    {G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (e : G ≅ F) :
    (restrictCoherentModulesMapIso f e).hom = restrictCoherentModulesMap f e.hom := rfl

/-- `Stacks.Algebraization.restrictCoherentModulesMap` is functorial. -/
public theorem restrictCoherentModulesMap_comp {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] [IsLocallyNoetherian X]
    {G F H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (x : G ⟶ F)
    (y : F ⟶ H) :
    restrictCoherentModulesMap f (x ≫ y) =
      restrictCoherentModulesMap f x ≫ restrictCoherentModulesMap f y := by
  refine ObjectProperty.hom_ext _ ?_
  exact (Scheme.Modules.restrictFunctor f).map_comp x.hom y.hom

/-- **Postcomposing the morphism of a local algebraization commutes with carrying it to a smaller
open.** -/
public theorem restrictedAlgebraizationMapOfLE_comp {X : Scheme.{u}} [IsLocallyNoetherian X]
    {U W : X.Opens} (hWU : W ≤ U)
    {G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    {F H : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    (x : restrictCoherentModules U.ι G ⟶ F) (y : F ⟶ H) :
    restrictedAlgebraizationMapOfLE hWU (x ≫ y) =
      restrictedAlgebraizationMapOfLE hWU x ≫
        restrictCoherentModulesMap (X.homOfLE hWU) y := by
  simp only [restrictedAlgebraizationMapOfLE, compRestrictedAlgebraizationMap,
    restrictCoherentModulesMap_comp, Category.assoc]

/-- The completion of a composite, read on the underlying morphisms of systems. -/
public theorem completionFunctor_map_comp_hom {V : Scheme.{u}} [IsLocallyNoetherian V]
    (K : V.IdealSheafData)
    {A B D : AlgebraicGeometry.SheafOfModules.CoherentModules V.ringCatSheaf} (x : A ⟶ B)
    (y : B ⟶ D) :
    ((completionFunctor V K).map (x ≫ y)).hom =
      ((completionFunctor V K).map x).hom ≫ ((completionFunctor V K).map y).hom := by
  rw [Functor.map_comp]
  exact fullSubcategory_comp_hom _ _

/-- The completion of the inverse of an isomorphism cancels the completion of the
isomorphism. -/
public theorem completionFunctor_map_inv_hom_id {V : Scheme.{u}} [IsLocallyNoetherian V]
    (K : V.IdealSheafData)
    {A B : AlgebraicGeometry.SheafOfModules.CoherentModules V.ringCatSheaf} (e : A ≅ B) :
    ((completionFunctor V K).map e.inv).hom ≫ ((completionFunctor V K).map e.hom).hom = 𝟙 _ := by
  rw [← completionFunctor_map_comp_hom, e.inv_hom_id, CategoryTheory.Functor.map_id]
  rfl

/-- **`Stacks.Algebraization.restrictCoherentModulesTransportIso` acts on the sections over an
open as a restriction map of the presheaf of the module**, along any morphism of opens `i` with
the right source and target. -/
public theorem restrictCoherentModulesTransportIso_hom_app {X : Scheme.{u}}
    [IsLocallyNoetherian X] {U W V : X.Opens} (hWU : W ≤ U) (hVW : V ≤ W)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf)
    (A : V.toScheme.Opens)
    (i : X.homOfLE hWU ''ᵁ (X.homOfLE hVW ''ᵁ A) ⟶ X.homOfLE (hVW.trans hWU) ''ᵁ A) :
    Scheme.Modules.Hom.app (restrictCoherentModulesTransportIso hWU hVW F).hom.hom A =
      (Scheme.Modules.presheaf (X := U.toScheme) F.obj).map i.op := by
  simp only [restrictCoherentModulesTransportIso, Iso.trans_hom, fullSubcategory_comp_hom,
    restrictCoherentModulesCongrIso_hom_hom, restrictCoherentModulesCompIso_hom_hom]
  exact presheafMap_comp₂_eq F.obj _ _ _

/-- The inverse of `Stacks.Algebraization.restrictCoherentModulesTransportIso` on sections. -/
public theorem restrictCoherentModulesTransportIso_inv_app {X : Scheme.{u}}
    [IsLocallyNoetherian X] {U W V : X.Opens} (hWU : W ≤ U) (hVW : V ≤ W)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf)
    (A : V.toScheme.Opens)
    (i : X.homOfLE (hVW.trans hWU) ''ᵁ A ⟶ X.homOfLE hWU ''ᵁ (X.homOfLE hVW ''ᵁ A)) :
    Scheme.Modules.Hom.app (restrictCoherentModulesTransportIso hWU hVW F).inv.hom A =
      (Scheme.Modules.presheaf (X := U.toScheme) F.obj).map i.op := by
  simp only [restrictCoherentModulesTransportIso, Iso.trans_inv, fullSubcategory_comp_hom,
    restrictCoherentModulesCongrIso_inv_hom, restrictCoherentModulesCompIso_inv_hom]
  exact presheafMap_comp₂_eq F.obj _ _ _

/-- **An overlap comparison over an affine open contained in a larger one is the transport of the
comparison over the larger one.** Let `α : G^∧ ⟶ (F_n)` be the datum of Stacks 0889 (2), let
`(F_i, b_i, β_i)` and `(F_j, b_j, β_j)` be local algebraizations over opens `U_i`, `U_j`, and let
`W ⊆ U_i ∩ U_j` carry a comparison `d_W` of the two transported algebraizations. Then over any
affine open `l ⊆ W` the comparison of the two algebraizations transported directly from `U_i` and
`U_j` is the transport of `d_W` along `l ⊆ W`. -/
public theorem overlapComparison_eq_transport {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj)
    {Ui Uj Wk : X.Opens} (l : X.affineOpens)
    (hki : Wk ≤ Ui) (hkj : Wk ≤ Uj) (hlk : l.1 ≤ Wk)
    {Fi : AlgebraicGeometry.SheafOfModules.CoherentModules Ui.toScheme.ringCatSheaf}
    {Fj : AlgebraicGeometry.SheafOfModules.CoherentModules Uj.toScheme.ringCatSheaf}
    (bi : restrictCoherentModules Ui.ι G ⟶ Fi) (bj : restrictCoherentModules Uj.ι G ⟶ Fj)
    (βi : ((completionFunctor Ui.toScheme (I.comap Ui.ι)).obj Fi).obj ≅
      ((Stacks.Coherent.restrictFunctor I Ui.ι).obj Fsys).obj)
    (βj : ((completionFunctor Uj.toScheme (I.comap Uj.ι)).obj Fj).obj ≅
      ((Stacks.Coherent.restrictFunctor I Uj.ι).obj Fsys).obj)
    (hβi : restrictedSystemMapDual Ui.ι I G Fsys α =
      ((completionFunctor Ui.toScheme (I.comap Ui.ι)).map bi).hom ≫ βi.hom)
    (hβj : restrictedSystemMapDual Uj.ι I G Fsys α =
      ((completionFunctor Uj.toScheme (I.comap Uj.ι)).map bj).hom ≫ βj.hom)
    (hKi : IsPowerAnnihilated (I.comap Ui.ι) (kernel (C := Ui.toScheme.Modules) bi.hom))
    (hCi : IsPowerAnnihilated (I.comap Ui.ι) (cokernel (C := Ui.toScheme.Modules) bi.hom))
    (hKj : IsPowerAnnihilated (I.comap Uj.ι) (kernel (C := Uj.toScheme.Modules) bj.hom))
    (hCj : IsPowerAnnihilated (I.comap Uj.ι) (cokernel (C := Uj.toScheme.Modules) bj.hom))
    (dk : restrictCoherentModules (X.homOfLE hki) Fi ≅
      restrictCoherentModules (X.homOfLE hkj) Fj)
    (hdk₁ : restrictedAlgebraizationMapOfLE hki bi ≫ dk.hom =
      restrictedAlgebraizationMapOfLE hkj bj)
    (hdk₂ : ((completionFunctor Wk.toScheme (I.comap Wk.ι)).map dk.hom).hom ≫
        (restrictedAlgebraizationIsoOfLE I Fsys hkj βj).hom =
      (restrictedAlgebraizationIsoOfLE I Fsys hki βi).hom)
    (dl : restrictCoherentModules (X.homOfLE (hlk.trans hki)) Fi ≅
      restrictCoherentModules (X.homOfLE (hlk.trans hkj)) Fj)
    (hdl₁ : restrictedAlgebraizationMapOfLE (hlk.trans hki) bi ≫ dl.hom =
      restrictedAlgebraizationMapOfLE (hlk.trans hkj) bj)
    (hdl₂ : ((completionFunctor l.1.toScheme (I.comap l.1.ι)).map dl.hom).hom ≫
        (restrictedAlgebraizationIsoOfLE I Fsys (hlk.trans hkj) βj).hom =
      (restrictedAlgebraizationIsoOfLE I Fsys (hlk.trans hki) βi).hom) :
    dl = restrictCoherentModulesTransportIso hki hlk Fi ≪≫
      restrictCoherentModulesMapIso (X.homOfLE hlk) dk ≪≫
        (restrictCoherentModulesTransportIso hkj hlk Fj).symm := by
  obtain ⟨d₀, -, huniq⟩ := unique_local_algebraization_dual I G Fsys α l
    (restrictCoherentModules (X.homOfLE (hlk.trans hki)) Fi)
    (restrictCoherentModules (X.homOfLE (hlk.trans hkj)) Fj)
    (restrictedAlgebraizationMapOfLE (hlk.trans hki) bi)
    (restrictedAlgebraizationMapOfLE (hlk.trans hkj) bj)
    (restrictedAlgebraizationIsoOfLE I Fsys (hlk.trans hki) βi)
    (restrictedAlgebraizationIsoOfLE I Fsys (hlk.trans hkj) βj)
    (restrictedSystemMapDual_eq_restrictedAlgebraizationOfLE I G Fsys α (hlk.trans hki) Fi bi
      βi hβi)
    (restrictedSystemMapDual_eq_restrictedAlgebraizationOfLE I G Fsys α (hlk.trans hkj) Fj bj
      βj hβj)
    (isPowerAnnihilated_kernel_restrictedAlgebraizationMapOfLE I (hlk.trans hki) bi hKi)
    (isPowerAnnihilated_cokernel_restrictedAlgebraizationMapOfLE I (hlk.trans hki) bi hCi)
    (isPowerAnnihilated_kernel_restrictedAlgebraizationMapOfLE I (hlk.trans hkj) bj hKj)
    (isPowerAnnihilated_cokernel_restrictedAlgebraizationMapOfLE I (hlk.trans hkj) bj hCj)
  refine (huniq dl ⟨hdl₁, hdl₂⟩).trans (huniq _ ⟨?_, ?_⟩).symm
  · exact comp_chain3_eq (restrictedAlgebraizationMapOfLE_trans hki hlk bi)
      ((restrictedAlgebraizationMapOfLE_comp hlk (restrictedAlgebraizationMapOfLE hki bi)
          dk.hom).symm.trans
        (congrArg (restrictedAlgebraizationMapOfLE hlk) hdk₁))
      ((Iso.comp_inv_eq _).2 (restrictedAlgebraizationMapOfLE_trans hkj hlk bj).symm)
  · rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, completionFunctor_map_comp_hom,
      completionFunctor_map_comp_hom]
    refine comp_chain3_eq_right (comp_cancel_inv_chain _ _ _ _
        (completionFunctor_map_inv_hom_id (I.comap l.1.ι)
          (restrictCoherentModulesTransportIso hkj hlk Fj))
        (restrictedAlgebraizationIsoOfLE_trans I Fsys hkj hlk βj)) ?_
      (restrictedAlgebraizationIsoOfLE_trans I Fsys hki hlk βi)
    rw [restrictCoherentModulesMapIso_hom]
    exact restrictedAlgebraizationIsoOfLE_naturality I Fsys hlk dk.hom
      (restrictedAlgebraizationIsoOfLE I Fsys hki βi)
      (restrictedAlgebraizationIsoOfLE I Fsys hkj βj) hdk₂

/-! ### The overlap comparisons on sections are compatible with shrinking the overlap -/

/-- **The image of a composite of two open immersions, read along a morphism equal to it.** -/
public theorem image_comp_eq_of_eq {X Y Z : Scheme.{u}} (p : X ⟶ Y) (q : Y ⟶ Z) (m : X ⟶ Z)
    [IsOpenImmersion p] [IsOpenImmersion q] [IsOpenImmersion m] (h : p ≫ q = m) (A : X.Opens) :
    q ''ᵁ (p ''ᵁ A) = m ''ᵁ A := by
  subst h
  rw [Scheme.Hom.comp_image]

/-- The whole of `W`, read as an open of `U ⊇ W`, is the preimage of `W` under the inclusion of
`U`. This is `Stacks.Algebraization.homOfLE_image_eq_ι_preimage_image` at the top open. -/
public theorem homOfLE_image_top_eq_ι_preimage {X : Scheme.{u}} {U W : X.Opens} (hWU : W ≤ U) :
    X.homOfLE hWU ''ᵁ (⊤ : W.toScheme.Opens) = U.ι ⁻¹ᵁ W :=
  (homOfLE_image_eq_ι_preimage_image hWU ⊤).trans
    (congrArg (fun V => U.ι ⁻¹ᵁ V) W.ι_image_top)

/-- A map sandwiched between restriction maps of two presheaves does not depend on how the
sandwich is split: the category of opens is thin. -/
private theorem presheafMap_sandwich_eq {X Y : Scheme.{u}} (M : X.Modules) (N : Y.Modules)
    {P Q R : (X.Opens)ᵒᵖ} {P' Q' R' : (Y.Opens)ᵒᵖ} (a₁ : P ⟶ Q) (a₂ : Q ⟶ R) (b₁ : P' ⟶ Q')
    (b₂ : Q' ⟶ R') (c₁ : P ⟶ R) (c₂ : P' ⟶ R') (D : M.presheaf.obj R ⟶ N.presheaf.obj P') :
    M.presheaf.map a₁ ≫ (M.presheaf.map a₂ ≫ D ≫ N.presheaf.map b₁) ≫ N.presheaf.map b₂ =
      M.presheaf.map c₁ ≫ D ≫ N.presheaf.map c₂ := by
  rw [← presheafMap_comp₂_eq M a₁ a₂ c₁, ← presheafMap_comp₂_eq N b₁ b₂ c₂]
  simp only [Category.assoc]

/-- The action on sections of a composite of three isomorphisms of coherent modules, the last of
them read backwards. -/
private theorem coherentIsoConjugate_hom_app {X : Scheme.{u}}
    {A B D E : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (a : A ≅ B)
    (b : B ≅ D) (c : E ≅ D) (W : X.Opens) :
    Scheme.Modules.Hom.app (a ≪≫ b ≪≫ c.symm).hom.hom W =
      Scheme.Modules.Hom.app a.hom.hom W ≫ Scheme.Modules.Hom.app b.hom.hom W ≫
        Scheme.Modules.Hom.app c.inv.hom W := rfl

/-- **The transport of an overlap comparison acts on sections as the comparison itself,
sandwiched between restriction maps.** -/
public theorem transportConjugate_app {X : Scheme.{u}} [IsLocallyNoetherian X]
    {Ui Uj Wk V : X.Opens} (hki : Wk ≤ Ui) (hkj : Wk ≤ Uj) (hlk : V ≤ Wk)
    {Fi : AlgebraicGeometry.SheafOfModules.CoherentModules Ui.toScheme.ringCatSheaf}
    {Fj : AlgebraicGeometry.SheafOfModules.CoherentModules Uj.toScheme.ringCatSheaf}
    (dk : restrictCoherentModules (X.homOfLE hki) Fi ≅
      restrictCoherentModules (X.homOfLE hkj) Fj) (A : V.toScheme.Opens)
    (a : X.homOfLE hki ''ᵁ (X.homOfLE hlk ''ᵁ A) ⟶ X.homOfLE (hlk.trans hki) ''ᵁ A)
    (b : X.homOfLE (hlk.trans hkj) ''ᵁ A ⟶ X.homOfLE hkj ''ᵁ (X.homOfLE hlk ''ᵁ A)) :
    Scheme.Modules.Hom.app (restrictCoherentModulesTransportIso hki hlk Fi ≪≫
        restrictCoherentModulesMapIso (X.homOfLE hlk) dk ≪≫
          (restrictCoherentModulesTransportIso hkj hlk Fj).symm).hom.hom A =
      (Scheme.Modules.presheaf (X := Ui.toScheme) Fi.obj).map a.op ≫
        Scheme.Modules.Hom.app dk.hom.hom (X.homOfLE hlk ''ᵁ A) ≫
          (Scheme.Modules.presheaf (X := Uj.toScheme) Fj.obj).map b.op := by
  rw [coherentIsoConjugate_hom_app,
    restrictCoherentModulesTransportIso_hom_app hki hlk Fi A a,
    restrictCoherentModulesTransportIso_inv_app hkj hlk Fj A b,
    restrictCoherentModulesMapIso_hom, restrictCoherentModulesMap_hom]
  rfl

/-- **The overlap comparisons on sections are compatible with shrinking the overlap.** Let
`α : G^∧ ⟶ (F_n)` be the datum of Stacks 0889 (2), let `(F_i, b_i, β_i)` and `(F_j, b_j, β_j)` be
local algebraizations over opens `U_i`, `U_j`, let `d_W` be a comparison of the two
algebraizations transported to an open `W ⊆ U_i ∩ U_j`, and let `d_l` be one over an affine open
`l ⊆ W`. Then the two act on the sections over `l` of the direct images by the *same* map. -/
public theorem localAppOpen_overlapRestrictIso_restrict {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj)
    {Ui Uj Wk : X.Opens} (l : X.affineOpens)
    (hki : Wk ≤ Ui) (hkj : Wk ≤ Uj) (hlk : l.1 ≤ Wk)
    {Fi : AlgebraicGeometry.SheafOfModules.CoherentModules Ui.toScheme.ringCatSheaf}
    {Fj : AlgebraicGeometry.SheafOfModules.CoherentModules Uj.toScheme.ringCatSheaf}
    (bi : restrictCoherentModules Ui.ι G ⟶ Fi) (bj : restrictCoherentModules Uj.ι G ⟶ Fj)
    (βi : ((completionFunctor Ui.toScheme (I.comap Ui.ι)).obj Fi).obj ≅
      ((Stacks.Coherent.restrictFunctor I Ui.ι).obj Fsys).obj)
    (βj : ((completionFunctor Uj.toScheme (I.comap Uj.ι)).obj Fj).obj ≅
      ((Stacks.Coherent.restrictFunctor I Uj.ι).obj Fsys).obj)
    (hβi : restrictedSystemMapDual Ui.ι I G Fsys α =
      ((completionFunctor Ui.toScheme (I.comap Ui.ι)).map bi).hom ≫ βi.hom)
    (hβj : restrictedSystemMapDual Uj.ι I G Fsys α =
      ((completionFunctor Uj.toScheme (I.comap Uj.ι)).map bj).hom ≫ βj.hom)
    (hKi : IsPowerAnnihilated (I.comap Ui.ι) (kernel (C := Ui.toScheme.Modules) bi.hom))
    (hCi : IsPowerAnnihilated (I.comap Ui.ι) (cokernel (C := Ui.toScheme.Modules) bi.hom))
    (hKj : IsPowerAnnihilated (I.comap Uj.ι) (kernel (C := Uj.toScheme.Modules) bj.hom))
    (hCj : IsPowerAnnihilated (I.comap Uj.ι) (cokernel (C := Uj.toScheme.Modules) bj.hom))
    (dk : restrictCoherentModules (X.homOfLE hki) Fi ≅
      restrictCoherentModules (X.homOfLE hkj) Fj)
    (hdk₁ : restrictedAlgebraizationMapOfLE hki bi ≫ dk.hom =
      restrictedAlgebraizationMapOfLE hkj bj)
    (hdk₂ : ((completionFunctor Wk.toScheme (I.comap Wk.ι)).map dk.hom).hom ≫
        (restrictedAlgebraizationIsoOfLE I Fsys hkj βj).hom =
      (restrictedAlgebraizationIsoOfLE I Fsys hki βi).hom)
    (dl : restrictCoherentModules (X.homOfLE (hlk.trans hki)) Fi ≅
      restrictCoherentModules (X.homOfLE (hlk.trans hkj)) Fj)
    (hdl₁ : restrictedAlgebraizationMapOfLE (hlk.trans hki) bi ≫ dl.hom =
      restrictedAlgebraizationMapOfLE (hlk.trans hkj) bj)
    (hdl₂ : ((completionFunctor l.1.toScheme (I.comap l.1.ι)).map dl.hom).hom ≫
        (restrictedAlgebraizationIsoOfLE I Fsys (hlk.trans hkj) βj).hom =
      (restrictedAlgebraizationIsoOfLE I Fsys (hlk.trans hki) βi).hom) :
    Stacks.Coherent.localAppOpen l.1
        (overlapRestrictIso (hlk.trans hki) (hlk.trans hkj) dl).hom le_rfl =
      Stacks.Coherent.localAppOpen Wk (overlapRestrictIso hki hkj dk).hom hlk := by
  have E1i : X.homOfLE (hlk.trans hki) ''ᵁ (⊤ : l.1.toScheme.Opens) = Ui.ι ⁻¹ᵁ l.1 :=
    homOfLE_image_top_eq_ι_preimage (hlk.trans hki)
  have E1j : X.homOfLE (hlk.trans hkj) ''ᵁ (⊤ : l.1.toScheme.Opens) = Uj.ι ⁻¹ᵁ l.1 :=
    homOfLE_image_top_eq_ι_preimage (hlk.trans hkj)
  have E2i : X.homOfLE hki ''ᵁ (X.homOfLE hlk ''ᵁ (⊤ : l.1.toScheme.Opens)) =
      X.homOfLE (hlk.trans hki) ''ᵁ (⊤ : l.1.toScheme.Opens) :=
    image_comp_eq_of_eq _ _ _ (X.homOfLE_homOfLE hlk hki) ⊤
  have E2j : X.homOfLE hkj ''ᵁ (X.homOfLE hlk ''ᵁ (⊤ : l.1.toScheme.Opens)) =
      X.homOfLE (hlk.trans hkj) ''ᵁ (⊤ : l.1.toScheme.Opens) :=
    image_comp_eq_of_eq _ _ _ (X.homOfLE_homOfLE hlk hkj) ⊤
  have E3 : Wk.ι ''ᵁ (X.homOfLE hlk ''ᵁ (⊤ : l.1.toScheme.Opens)) = l.1 :=
    (image_comp_eq_of_eq _ _ _ (X.homOfLE_ι hlk) ⊤).trans (l.1).ι_image_top
  have hdl := overlapComparison_eq_transport I G Fsys α l hki hkj hlk bi bj βi βj hβi hβj
    hKi hCi hKj hCj dk hdk₁ hdk₂ dl hdl₁ hdl₂
  rw [← Stacks.Coherent.localApp_eq_localAppOpen l.1
      (overlapRestrictIso (hlk.trans hki) (hlk.trans hkj) dl).hom (l.1).ι_image_top le_rfl,
    ← Stacks.Coherent.localApp_eq_localAppOpen Wk (overlapRestrictIso hki hkj dk).hom E3 hlk,
    localApp_overlapRestrictIso (hlk.trans hki) (hlk.trans hkj) dl (l.1).ι_image_top
      (eqToHom E1i) (eqToHom E1j.symm),
    localApp_overlapRestrictIso hki hkj dk E3 (eqToHom (E2i.trans E1i))
      (eqToHom (E2j.trans E1j).symm), hdl,
    transportConjugate_app hki hkj hlk dk ⊤ (eqToHom E2i) (eqToHom E2j.symm)]
  exact presheafMap_sandwich_eq Fi.obj Fj.obj _ _ _ _ _ _ _

/-- **The level-`n` component of `Stacks.Algebraization.restrictedAlgebraizationIsoOfLE`,
unfolded.** The transported comparison isomorphism of a local algebraization is, level by level,
the comparison `β` of the chart restricted along `W ⟶ U`, between the two ideal-sheaf transports
and the comparison of Stacks 0880 on one side and the two transports of the restricted system on
the other. -/
public theorem restrictedAlgebraizationIsoOfLE_hom_app {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (Fsys : Stacks.Coherent.CoherentAdicSystems I) {U W : X.Opens}
    (hWU : W ≤ U) (F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf)
    (β : ((completionFunctor U.toScheme (I.comap U.ι)).obj F).obj ≅
      ((Stacks.Coherent.restrictFunctor I U.ι).obj Fsys).obj) (n : ℕᵒᵖ) :
    (restrictedAlgebraizationIsoOfLE I Fsys hWU β).hom.app n =
      (completionCongrIso (congrArg (fun m => I.comap m) (X.homOfLE_ι hWU).symm)
            (restrictCoherentModules (X.homOfLE hWU) F)).hom.app n ≫
        ((completionCongrIso (Scheme.IdealSheafData.comap_comp I (X.homOfLE hWU) U.ι)
              (restrictCoherentModules (X.homOfLE hWU) F)).hom.app n ≫
            ((completionRestrictOpenIso (X.homOfLE hWU) (I.comap U.ι) F).inv.app n ≫
                (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map (β.hom.app n)) ≫
              (restrictedSystemCompIso (X.homOfLE hWU) U.ι I Fsys).inv.app n) ≫
          (restrictedSystemCongrIso I Fsys (X.homOfLE_ι hWU)).hom.app n := by
  rw [restrictedAlgebraizationIsoOfLE_eq, isoTrans₃_hom_app,
    compRestrictedAlgebraizationIso_hom_app, restrictedAlgebraizationIsoDual_hom_app]
  rfl

end Stacks.Algebraization

end
