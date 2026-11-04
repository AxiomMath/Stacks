module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Effective
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fpqc descent for quasi-coherent modules

This file compares the geometric and the algebraic base-change functors for quasi-coherent
modules on affine schemes.  For a ring map `φ : R ⟶ S` the functor `M ↦ M^~` intertwines
extension of scalars along `φ` with pullback along `Spec.map φ`.  Transporting Mathlib's
comonadicity of extension of scalars along a faithfully flat ring map through this comparison
gives faithfully flat descent for quasi-coherent modules on affine schemes.

It then assembles the two assertions of fpqc descent for quasi-coherent sheaves — full
faithfulness of the canonical descent functor, and effectivity of every quasi-coherent descent
datum — into a single equivalence of categories between the quasi-coherent modules on the base
and the quasi-coherent descent data for the family, and deduces from the affine comonadicity the
faithfulness of the canonical descent functor for a covering by one faithfully flat morphism of
affine schemes.

## Main definitions

* `Stacks.Descent.pullbackQcoh` and `Stacks.Descent.pushforwardQcoh` are pullback and
  pushforward of quasi-coherent modules along a morphism of affine schemes, and
  `Stacks.Descent.pullbackQcohAdjunction` is the adjunction between them.

## Main results

* `Stacks.Descent.pushforwardSpecΓIso` identifies the global sections of a pushforward along
  `Spec.map φ` with the global sections restricted along `φ`.
* `Stacks.Descent.extendScalarsCompTildeIso` identifies `(S ⊗[R] M)^~` with the pullback of
  `M^~` along `Spec.map φ`, naturally in the `R`-module `M`.
* `Stacks.Descent.isQuasicoherent_pullback_specMap` states that pullback along `Spec.map φ`
  preserves quasi-coherence, and `Stacks.Descent.isQuasicoherent_pushforward_specMap` says the
  same for pushforward.  The statement for an arbitrary morphism of affine schemes is
  `Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isAffine`.
* `Stacks.Descent.pullbackQcohConjugateIso` identifies `pullbackQcoh φ` with extension of
  scalars along `φ`, conjugated by `AlgebraicGeometry.tildeEquiv`.
* `Stacks.Descent.comonadicPullbackQcoh` is faithfully flat descent for quasi-coherent modules
  in the affine case: for a faithfully flat `φ`, pullback along `Spec.map φ` is comonadic, so
  quasi-coherent modules on `Spec R` are the coalgebras of the resulting comonad.
* `Stacks.Descent.faithful_pullbackQcoh` is the faithfulness consequence.
* `Stacks.Descent.descentDataComponentFunctor` evaluates a descent datum at one index of the
  family, and `Stacks.Descent.toDescentData_comp_descentDataComponentFunctor` identifies its
  composite with the canonical descent functor of a pseudofunctor with the pullback along the
  corresponding member of the family.
* `Stacks.Descent.isEquivalence_canonicalDescentFunctor_iff` says that the conjunction of full
  faithfulness of `AlgebraicGeometry.canonicalDescentFunctor` and effectivity of every
  quasi-coherent descent datum is exactly the assertion that the canonical descent functor is an
  equivalence, and `Stacks.Descent.canonicalDescentEquivalence` is that equivalence.
* `Stacks.Descent.isEquivalence_canonicalDescentFunctor_of_essSurj` derives the equivalence from
  descent for arbitrary sheaves of modules together with descent of quasi-coherence.
* `Stacks.Descent.ofArrows_specMap_mem_fpqcPrecoverage`: a faithfully flat map of rings gives an
  fpqc covering family of the base.
* `Stacks.Descent.faithful_canonicalDescentFunctor_specMap` is the faithfulness half of fpqc
  descent for that covering family.

## Implementation notes

The natural isomorphism `extendScalarsCompTildeIso` is obtained by conjugating an isomorphism
of right adjoints.  Both `extendScalars φ ⋙ tilde` and `tilde ⋙ pullback (Spec.map φ)` are
left adjoints, of `moduleSpecΓFunctor ⋙ restrictScalars φ` and of
`pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor` respectively; the latter two are identified by
`pushforwardSpecΓIso`, which is in turn a whiskering of Mathlib's
`AlgebraicGeometry.pushforwardCompModulesSpecToSheafIso`.  Conjugating with
`CategoryTheory.conjugateIsoEquiv` avoids computing either side on sections.

Quasi-coherence of a pullback then follows for a morphism of affine schemes, because a
quasi-coherent module on `Spec R` is in the essential image of `tilde` by
`AlgebraicGeometry.essImage_tilde`.  For a morphism between arbitrary affine schemes one
factors it through `Spec` of its map on global sections and uses that pullback along an open
immersion is restriction, which Mathlib already knows preserves quasi-coherence.

Comonadicity is obtained from Beck's comonadicity theorem in the form
`CategoryTheory.Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms`:
quasi-coherent modules on `Spec R` have all limits because they are equivalent to `ModuleCat R`,
and `pullbackQcoh φ` preserves finite limits and reflects isomorphisms because, after
conjugation, extension of scalars along a flat, respectively faithfully flat, ring map does.

Effectivity of a quasi-coherent descent datum is membership in the essential image of
`AlgebraicGeometry.canonicalDescentFunctor`, so effectivity of every datum is literally the
essential surjectivity of that functor; the equivalence is therefore assembled from full
faithfulness and effectivity with no further input.

Faithfulness in the affine case is checked after evaluating a descent datum at one index.
That evaluation is `descentDataComponentFunctor`, whose target is the bundled category
`modulePullbackPseudofunctor.obj (.mk (op (X i)))` rather than the type
`SheafOfModules (X i).ringCatSheaf`: identifying the two `Category` instances forces the
elaborator to unfold the whole pullback adjunction, whereas the composite of functors reduces
definitionally to `Scheme.Modules.pullback` and the comparison is `rfl`.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory Opposite TopologicalSpace

universe t v' u' v₁ u₁ v u

namespace Stacks.Descent

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Taking global sections of a pushforward along `Spec.map φ` is restriction of scalars along
`φ` of taking global sections. -/
noncomputable def pushforwardSpecΓIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom :=
  Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso φ)
    (TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op ⊤))

/-- The module associated to an extension of scalars is the pullback of the associated module:
`(S ⊗[R] M)^~ ≅ (Spec.map φ)^* (M^~)`, naturally in `M`. -/
noncomputable def extendScalarsCompTildeIso :
    ModuleCat.extendScalars φ.hom ⋙ tilde.functor S ≅
      tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) :=
  (conjugateIsoEquiv
      (tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)))
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction)).symm
    (pushforwardSpecΓIso φ)

/-- Quasi-coherence is invariant under isomorphism of modules. -/
lemma isQuasicoherent_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (h : M.IsQuasicoherent) : N.IsQuasicoherent :=
  ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent X.ringCatSheaf) e h

/-- Pullback along a morphism of affine schemes preserves quasi-coherence. -/
lemma isQuasicoherent_pullback_specMap (M : (Spec R).Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback (Spec.map φ)).obj M).IsQuasicoherent := by
  obtain ⟨N, ⟨e⟩⟩ : (tilde.functor R).essImage M := by
    rw [essImage_tilde]; exact ‹M.IsQuasicoherent›
  exact isQuasicoherent_of_iso
    ((extendScalarsCompTildeIso φ).app N ≪≫ (Scheme.Modules.pullback (Spec.map φ)).mapIso e)
    (show ((tilde.functor S).obj ((ModuleCat.extendScalars φ.hom).obj N)).IsQuasicoherent from
      inferInstance)

/-- Pushforward along a morphism of affine schemes preserves quasi-coherence. -/
lemma isQuasicoherent_pushforward_specMap (M : (Spec S).Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward (Spec.map φ)).obj M).IsQuasicoherent := by
  have : IsIso (Scheme.Modules.fromTildeΓ M) := (isQuasicoherent_iff_isIso_fromTildeΓ M).mp ‹_›
  rw [isQuasicoherent_iff_isIso_fromTildeΓ]
  exact isIso_fromTildeΓ_pushforward φ M

/-- Pullback of quasi-coherent modules along a morphism of affine schemes. -/
noncomputable def pullbackQcoh :
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Scheme.Modules.pullback (Spec.map φ))
    fun M ↦ isQuasicoherent_pullback_specMap φ M.obj

/-- Pushforward of quasi-coherent modules along a morphism of affine schemes. -/
noncomputable def pushforwardQcoh :
    (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Scheme.Modules.pushforward (Spec.map φ))
    fun M ↦ isQuasicoherent_pushforward_specMap φ M.obj

/-- Forgetting quasi-coherence identifies `pullbackQcoh` with pullback of modules. -/
lemma pullbackQcoh_comp_ι :
    pullbackQcoh φ ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙ Scheme.Modules.pullback (Spec.map φ) := rfl

/-- Forgetting quasi-coherence identifies `pushforwardQcoh` with pushforward of modules. -/
lemma pushforwardQcoh_comp_ι :
    pushforwardQcoh φ ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙ Scheme.Modules.pushforward (Spec.map φ) := rfl

/-- Pullback is left adjoint to pushforward on quasi-coherent modules over affine schemes. -/
noncomputable def pullbackQcohAdjunction : pullbackQcoh φ ⊣ pushforwardQcoh φ :=
  Adjunction.restrictFullyFaithful
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
    (.ofFullyFaithful (ObjectProperty.ι _)) (.ofFullyFaithful (ObjectProperty.ι _))
    (Iso.refl _) (Iso.refl _)

/-- `tildeEquiv` intertwines extension of scalars with pullback of quasi-coherent modules. -/
noncomputable def extendScalarsCompTildeEquivIso :
    ModuleCat.extendScalars φ.hom ⋙ (tildeEquiv (R := S)).functor ≅
      (tildeEquiv (R := R)).functor ⋙ pullbackQcoh φ :=
  Functor.fullyFaithfulCancelRight (ObjectProperty.ι _) (extendScalarsCompTildeIso φ)

/-- Pullback of quasi-coherent modules along `Spec.map φ` is, up to the equivalence
`AlgebraicGeometry.tildeEquiv`, extension of scalars along `φ`. -/
noncomputable def pullbackQcohConjugateIso :
    pullbackQcoh φ ≅
      (tildeEquiv (R := R)).inverse ⋙ ModuleCat.extendScalars φ.hom ⋙
        (tildeEquiv (R := S)).functor :=
  (tildeEquiv.invFunIdAssoc (pullbackQcoh φ)).symm ≪≫
    Functor.isoWhiskerLeft tildeEquiv.inverse (extendScalarsCompTildeEquivIso φ).symm

/-- Pullback of quasi-coherent modules along a flat morphism of affine schemes preserves finite
limits. -/
lemma preservesFiniteLimits_pullbackQcoh (hφ : φ.hom.Flat) :
    Limits.PreservesFiniteLimits (pullbackQcoh φ) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  exact Limits.preservesFiniteLimits_of_natIso (pullbackQcohConjugateIso φ).symm

/-- Pullback of quasi-coherent modules along a faithfully flat morphism of affine schemes
reflects isomorphisms. -/
lemma reflectsIsomorphisms_pullbackQcoh (hφ : φ.hom.FaithfullyFlat) :
    (pullbackQcoh φ).ReflectsIsomorphisms := by
  have := ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat hφ
  exact reflectsIsomorphisms_of_iso (pullbackQcohConjugateIso φ).symm

/-- **Faithfully flat descent for quasi-coherent modules, affine case.**  Pullback of
quasi-coherent modules along a faithfully flat morphism of affine schemes is comonadic: the
category of quasi-coherent modules on `Spec R` is equivalent to the category of coalgebras for
the comonad of the pullback-pushforward adjunction along `Spec.map φ`. -/
@[instance_reducible]
noncomputable def comonadicPullbackQcoh (hφ : φ.hom.FaithfullyFlat) :
    ComonadicLeftAdjoint (pullbackQcoh φ) := by
  have : Limits.HasLimits
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
    Adjunction.has_limits_of_equivalence (tildeEquiv (R := R)).inverse
  have := preservesFiniteLimits_pullbackQcoh φ hφ.flat
  have := reflectsIsomorphisms_pullbackQcoh φ hφ
  have : Comonad.HasEqualizerOfIsCosplitPair (pullbackQcoh φ) := ⟨fun _ _ ↦ inferInstance⟩
  have : Comonad.PreservesLimitOfIsCosplitPair (pullbackQcoh φ) := ⟨fun _ _ ↦ inferInstance⟩
  exact Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms
    (pullbackQcohAdjunction φ)

/-- Pullback along a faithfully flat morphism of affine schemes is faithful on quasi-coherent
modules: two morphisms of quasi-coherent modules agreeing after pullback are equal.  This is the
affine case of the faithfulness half of fpqc descent. -/
lemma faithful_pullbackQcoh (hφ : φ.hom.FaithfullyFlat) : (pullbackQcoh φ).Faithful := by
  have := comonadicPullbackQcoh φ hφ
  have : (Comonad.comparison (comonadicAdjunction (pullbackQcoh φ))).IsEquivalence :=
    inferInstance
  exact Functor.Faithful.of_iso
    (F := Comonad.comparison (comonadicAdjunction (pullbackQcoh φ)) ⋙
      (comonadicAdjunction (pullbackQcoh φ)).toComonad.forget)
    (Comonad.comparisonForget _)

section Component

variable {C : Type u₁} [Category.{v₁} C] {J : Type t} {T : C} {Y : J → C}
  (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) (g : ∀ j, Y j ⟶ T) (j : J)

/-- Evaluation of a descent datum at one index of the family, as a functor.  The target is the
bundled category `F.obj (.mk (op (Y j)))` rather than its underlying type, so that no instance
of the ambient pseudofunctor has to be unfolded. -/
@[simps]
def descentDataComponentFunctor : F.DescentData g ⥤ F.obj (.mk (op (Y j))) where
  obj D := D.obj j
  map φ := φ.hom j

/-- Evaluating the canonical descent datum of an object at one index is pullback along the
corresponding member of the family. -/
theorem toDescentData_comp_descentDataComponentFunctor :
    F.toDescentData g ⋙ descentDataComponentFunctor F g j =
      (F.map (g j).op.toLoc).toFunctor :=
  rfl

end Component

section Equivalence

variable {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}

/-- Effectivity of every quasi-coherent descent datum is exactly essential surjectivity of the
canonical descent functor. -/
theorem essSurj_canonicalDescentFunctor_iff :
    (canonicalDescentFunctor f).EssSurj ↔
      ∀ D : QuasicoherentDescentData f, D.IsEffective :=
  ⟨fun _ D ↦ Functor.EssSurj.mem_essImage _ D, fun h ↦ ⟨h⟩⟩

/-- **The two halves of Stacks 023T assemble into an equivalence.**  If the canonical descent
functor is fully faithful and every quasi-coherent descent datum is effective, then the canonical
descent functor is an equivalence of categories. -/
theorem isEquivalence_canonicalDescentFunctor
    (hff : Nonempty (canonicalDescentFunctor f).FullyFaithful)
    (heff : ∀ D : QuasicoherentDescentData f, D.IsEffective) :
    (canonicalDescentFunctor f).IsEquivalence := by
  obtain ⟨h⟩ := hff
  have := h.full
  have := h.faithful
  have : (canonicalDescentFunctor f).EssSurj := ⟨heff⟩
  exact { }

/-- Full faithfulness is one half of the conclusion of Stacks 023T. -/
theorem nonempty_fullyFaithful_of_isEquivalence [(canonicalDescentFunctor f).IsEquivalence] :
    Nonempty (canonicalDescentFunctor f).FullyFaithful :=
  ⟨.ofFullyFaithful _⟩

/-- Effectivity of every quasi-coherent descent datum is the other half of the conclusion of
Stacks 023T. -/
theorem isEffective_of_isEquivalence [(canonicalDescentFunctor f).IsEquivalence]
    (D : QuasicoherentDescentData f) : D.IsEffective :=
  Functor.EssSurj.mem_essImage _ D

/-- **Stacks 023T as a single statement.**  The conjunction of the two assertions of Stacks 023T
— full faithfulness of the canonical descent functor, and effectivity of every quasi-coherent
descent datum — says exactly that the canonical descent functor is an equivalence between the
quasi-coherent modules on the base and the quasi-coherent descent data for the family. -/
theorem isEquivalence_canonicalDescentFunctor_iff :
    (canonicalDescentFunctor f).IsEquivalence ↔
      Nonempty (canonicalDescentFunctor f).FullyFaithful ∧
        ∀ D : QuasicoherentDescentData f, D.IsEffective :=
  ⟨fun _ ↦ ⟨nonempty_fullyFaithful_of_isEquivalence, isEffective_of_isEquivalence⟩,
    fun ⟨h₁, h₂⟩ ↦ isEquivalence_canonicalDescentFunctor h₁ h₂⟩

/-- **The descent equivalence.**  Under the two assertions of Stacks 023T, the category of
quasi-coherent modules on `S` is equivalent to the category of quasi-coherent descent data for
the family `f`, the equivalence being the canonical descent functor. -/
noncomputable def canonicalDescentEquivalence
    (hff : Nonempty (canonicalDescentFunctor f).FullyFaithful)
    (heff : ∀ D : QuasicoherentDescentData f, D.IsEffective) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      QuasicoherentDescentData f :=
  have := isEquivalence_canonicalDescentFunctor hff heff
  (canonicalDescentFunctor f).asEquivalence

/-- **Stacks 023T from descent for sheaves of modules.**  If descent of morphisms and of objects
holds for all sheaves of modules along the family `f`, and quasi-coherence descends along `f`,
then the canonical descent functor on quasi-coherent modules is an equivalence. -/
theorem isEquivalence_canonicalDescentFunctor_of_essSurj
    (hqc : ∀ M : S.Modules,
      (∀ i, ((Scheme.Modules.pullback (f i)).obj M).IsQuasicoherent) → M.IsQuasicoherent)
    (hff : (modulePullbackPseudofunctor.toDescentData f).FullyFaithful)
    [(modulePullbackPseudofunctor.toDescentData f).EssSurj] :
    (canonicalDescentFunctor f).IsEquivalence :=
  isEquivalence_canonicalDescentFunctor
    (nonempty_fullyFaithful_canonicalDescentFunctor_of_fullyFaithful hff)
    fun _ ↦ isEffective_of_essSurj hqc _

end Equivalence

section Affine

/-- A faithfully flat map of rings `φ : R ⟶ S` gives an fpqc covering family of `Spec R`
consisting of copies of `Spec.map φ`: that morphism is flat and surjective by
`AlgebraicGeometry.flat_and_surjective_SpecMap_iff`, and quasi-compact because it is affine. -/
@[sga "3 IV 6.3.1" "(v), special case"]
theorem ofArrows_specMap_mem_fpqcPrecoverage (hφ : φ.hom.FaithfullyFlat) {I : Type*} [Unique I] :
    Presieve.ofArrows (fun _ : I ↦ Spec S) (fun _ ↦ Spec.map φ) ∈
      Scheme.fpqcPrecoverage.{u} (Spec R) := by
  obtain ⟨h₁, h₂⟩ := (flat_and_surjective_SpecMap_iff φ).2 hφ
  rw [Presieve.ofArrows_of_unique]
  exact (Spec.map φ).singleton_mem_fpqcPrecoverage

/-- **The faithfulness half of Stacks 023T, affine case.**  For a faithfully flat map of rings
`φ : R ⟶ S` and a nonempty family all of whose members are `Spec.map φ`, the canonical descent
functor from quasi-coherent modules on `Spec R` to quasi-coherent descent data is faithful.

Faithfulness is checked after evaluating a descent datum at one index of the family, where the
canonical descent functor becomes pullback along `Spec.map φ`; that functor is faithful by
`Stacks.Descent.faithful_pullbackQcoh`. -/
theorem faithful_canonicalDescentFunctor_specMap (hφ : φ.hom.FaithfullyFlat) {I : Type v}
    (i : I) : (canonicalDescentFunctor (fun _ : I ↦ Spec.map φ)).Faithful := by
  have := faithful_pullbackQcoh φ hφ
  have h : (canonicalDescentFunctor (fun _ : I ↦ Spec.map φ) ⋙
      (ObjectProperty.ι _ ⋙ descentDataComponentFunctor modulePullbackPseudofunctor
        (fun _ : I ↦ Spec.map φ) i)).Faithful :=
    inferInstanceAs ((pullbackQcoh φ ⋙ ObjectProperty.ι _).Faithful)
  exact Functor.Faithful.of_comp (F := canonicalDescentFunctor (fun _ : I ↦ Spec.map φ))
    (ObjectProperty.ι _ ⋙ descentDataComponentFunctor modulePullbackPseudofunctor
      (fun _ : I ↦ Spec.map φ) i)

end Affine

end Stacks.Descent

end
