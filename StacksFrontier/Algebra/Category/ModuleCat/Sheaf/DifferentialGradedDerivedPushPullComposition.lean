module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushPullLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackCompositeUniversal

/-!
# Derived pushforward and derived pullback along a composition

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` and `g : (Sh(C'), O') ⟶ (Sh(C''), O'')` be morphisms of
ringed sites with homomorphisms `φ : A' ⟶ f_*A` and `ψ : A'' ⟶ g_*A'` of sheaves of differential
graded algebras, so that `ψ.trans φ : A'' ⟶ (g ∘ f)_*A` is the composite homomorphism. This file
proves

`L(g ∘ f)^* ≅ Lg^* ⋙ Lf^*` and `R(g ∘ f)_* ≅ Rf_* ⋙ Rg_*`,

the second for exact direct images and arbitrary derived pushforwards. The tag
[Stacks, Tag 0FTU](https://stacks.math.columbia.edu/tag/0FTU) itself, for the derived pushforwards
along morphisms of ringed topoi constructed from K-injective resolutions, with no exactness, is
`SheafOfModules.DifferentialGradedModule.derivedToposPushforward_comp`.

The pullback statement is for an *exact pair* in the sense of
`DifferentialGradedDerivedPushPullLocalization.lean`: the chosen pullback inverts
quasi-isomorphisms, so the derived pullback is the factorisation of `K(f^*)` through the
localization, and since all three derived pullbacks are such factorisations the module-level
comparison `PullbackData.transIso` descends to them by uniqueness of the factorisation.

The pushforward statement does not go through adjunctions, and in particular does not go through
the pullback at all. The direct image along a composition *is* the composite of the two direct
images, already on differential graded modules and hence on the homotopy categories; so once
`K(f_*)` and `K(g_*)` invert the quasi-isomorphisms, all three derived pushforwards are
factorisations through the localizations and the same uniqueness argument applies. And the two
hypotheses that they do are read off exactness of the two direct images of sheaves of modules,
which is a condition on the two morphisms of ringed sites. Finally the resulting functors are
compared with *arbitrary* derived pushforwards: for a functor inverting a class of morphisms the
comparison map of any right derived extension in the sense of
[Stacks, Tag 05S9](https://stacks.math.columbia.edu/tag/05S9) is an isomorphism
(`isIso_pushforwardComparison`), so any such extension is the factorisation up to isomorphism.
That is what makes the statement below a statement about the derived pushforwards of the source
rather than about the particular functors constructed here.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.homotopyPullbackFunctorCompIso` is
  `K(g^*) ⋙ K(f^*) ≅ K((g ∘ f)^*)`, and
  `SheafOfModules.DifferentialGradedModule.derivedPullbackOfInvertsCompIso` is
  `L(g ∘ f)^* ≅ Lg^* ⋙ Lf^*` for exact pairs.
* `SheafOfModules.DifferentialGradedModule.derivedPushforwardOfInvertsCompIso` is
  `R(g ∘ f)_* ≅ Rf_* ⋙ Rg_*` for the three constructed derived pushforwards, and
  `SheafOfModules.DifferentialGradedModule.derivedPushforwardCompIso` is the same isomorphism
  between three arbitrary carried derived pushforwards.

## Main results

* `SheafOfModules.DifferentialGradedModule.pushforwardFunctor_trans` and
  `...homotopyPushforwardFunctor_trans`: the direct image along a composition of morphisms of
  ringed sites is the composite of the two direct images, on right differential graded modules
  and on their homotopy categories.
* `SheafOfModules.DifferentialGradedModule.quasiIso_pushforwardFunctor_trans_map`: the direct
  image along the composition carries quasi-isomorphisms to quasi-isomorphisms as soon as the
  two direct images do.
* `SheafOfModules.DifferentialGradedModule.nonempty_derivedPushforward_comp_iso`: for exact
  direct images, any derived pushforward along `g ∘ f` is isomorphic to any derived pushforward
  along `f` followed by any derived pushforward along `g`. Tag 0FTU itself is
  `SheafOfModules.DifferentialGradedModule.derivedToposPushforward_comp`, in
  `DifferentialGradedToposDerivedPushforwardComp.lean`.

## Main results

* `SheafOfModules.DifferentialGradedModule.pushforwardFunctor_trans` and
  `SheafOfModules.DifferentialGradedModule.homotopyPushforwardFunctor_trans`: the direct image
  along a composition is the composition of the direct images, on differential graded modules
  and on their homotopy categories. No exactness and no pullback enters these two.

## Implementation notes

**The derived pushforwards are quantified over, not constructed.** Over a morphism of ringed sites
in the sense of this file, presented by an arbitrary continuous functor, no resolution theory is
available, so the statement here ranges over all triples of functors satisfying, with their
comparison maps, the derived-value condition of Tag 05S9 — that is, over all triples of terms of
`SheafOfModules.DifferentialGradedModule.DerivedPushPullData`, whose inhabitants include the
identity (`idDerivedPushPullData`) and every exact pair (`derivedPushPullDataOfInverts`). The
conclusion is an isomorphism rather than the source's equality, since functors pinned by a
universal property are pinned only up to isomorphism, and it is `Nonempty` of one only in the
registered theorem; the isomorphism itself is `derivedPushforwardCompIso`.

**Exactness of the two direct images.** This is the one hypothesis beyond the source's setup, and
it is what replaces the source's resolutions: the source builds `Rf_*` from K-injective resolutions
and deduces Tag 0FTU from Tag 0FTI and uniqueness of adjoints. Exactness is a condition on the
morphism of ringed sites and on nothing else; it is met by the identity morphism
(`preservesHomology_sitePushforward_id`), so the statement is not vacuous.

**The pullback is still carried.** On the pullback side `f^*` is the datum `PullbackData`
together with `PullbackData.HomotopyExtension`, and the composite pullback datum `Pχ` and the
universality datum of `PullbackData.transIso` are the hypotheses of that lemma; none of them
enters the pushforward statement. Tag 0FTI is registered elsewhere, on
`SheafOfModules.DifferentialGradedModule.derivedPullbackRingedToposCompIso`, for the derived
pullback along a morphism of ringed topoi; `derivedPullbackOfInvertsCompIso` here is the same
comparison for an exact pair and carries no attribute.

**Continuity of the composite functor.** `Functor.isContinuous_comp` is a lemma and not an
instance — the intermediate topology cannot be inferred from the goal — so continuity of `v ⋙ u`
for `J''` and `J` is an instance argument alongside continuity of `u` and of `v`.

## References

* [Stacks Project, Tag 0FTU](https://stacks.math.columbia.edu/tag/0FTU)
* [Stacks Project, Tag 0FTI](https://stacks.math.columbia.edu/tag/0FTI)
* [Stacks Project, Tag 0FTR](https://stacks.math.columbia.edu/tag/0FTR)
* [Stacks Project, Tag 05S9](https://stacks.math.columbia.edu/tag/05S9)
-/

@[expose] public section

open CategoryTheory

universe t a a' a'' m v u v' u' v'' u''

namespace SheafOfModules

namespace DifferentialGradedModule
/-! ### The composition -/

section Composition

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  {C'' : Type u''} [Category.{v''} C''] {J'' : GrothendieckTopology C''}
  {R'' : Sheaf J'' RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J' AddCommGrpCat.{m}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J'' AddCommGrpCat.{m}] [J''.WEqualsLocallyBijective AddCommGrpCat.{m}]
  {A : DifferentialGradedAlgebra.{t, a} R} {A' : DifferentialGradedAlgebra.{t, a'} R'}
  {A'' : DifferentialGradedAlgebra.{t, a''} R''}
  {u : C' ⥤ C} [u.IsContinuous J' J] {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {v : C'' ⥤ C'} [v.IsContinuous J'' J'] {τ : R''.obj ⟶ v.op ⋙ R'.obj}
  [(v ⋙ u).IsContinuous J'' J]
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A}
  {ψ : DifferentialGradedAlgebra.SemilinearHom v τ A'' A'}
  (Pφ : PullbackData φ) (Eφ : Pφ.HomotopyExtension)
  (Pψ : PullbackData ψ) (Eψ : Pψ.HomotopyExtension)
  (Pχ : PullbackData (ψ.trans φ)) (Eχ : Pχ.HomotopyExtension)

/-- `K(g^*) ⋙ K(f^*) ≅ K((g ∘ f)^*)` on the homotopy categories: the module-level comparison
`PullbackData.transIso`, descended; its universality datum is
`PullbackData.isUniversal_unit`, a theorem about every pullback datum. -/
noncomputable def homotopyPullbackFunctorCompIso :
    homotopyPullbackFunctor Pψ Eψ ⋙ homotopyPullbackFunctor Pφ Eφ ≅
      homotopyPullbackFunctor Pχ Eχ :=
  eqToIso (HomotopyCategory.descend_comp Pψ.functor Eψ.preservesHomotopic Pφ.functor
      Eφ.preservesHomotopic).symm ≪≫
    HomotopyCategory.descendNatIso _ _
      (Pφ.transIso Pψ Pχ fun M N => Pψ.isUniversal_unit M N)

variable (hφ : (quasiIsomorphisms.{t, a', m} A').IsInvertedBy
    (homotopyPullbackFunctor Pφ Eφ ⋙ toDerivedCategory.{t, a, m} A))
  (hψ' : (quasiIsomorphisms.{t, a'', m} A'').IsInvertedBy
    (homotopyPullbackFunctor Pψ Eψ ⋙ toDerivedCategory.{t, a', m} A'))
  (hχ : (quasiIsomorphisms.{t, a'', m} A'').IsInvertedBy
    (homotopyPullbackFunctor Pχ Eχ ⋙ toDerivedCategory.{t, a, m} A))

/-- **Stacks 0FTI for exact pairs**: the derived pullback along a composition is the composition
of the derived pullbacks. Both sides lift `K((g ∘ f)^*)` followed by the localization, so they
agree by uniqueness of the factorisation through a localization. -/
noncomputable def derivedPullbackOfInvertsCompIso :
    derivedPullbackOfInverts hχ ≅
      derivedPullbackOfInverts hψ' ⋙ derivedPullbackOfInverts hφ := by
  letI : Localization.Lifting (toDerivedCategory.{t, a'', m} A'')
      (quasiIsomorphisms.{t, a'', m} A'')
      (homotopyPullbackFunctor Pχ Eχ ⋙ toDerivedCategory.{t, a, m} A)
      (derivedPullbackOfInverts hψ' ⋙ derivedPullbackOfInverts hφ) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pullbackComparisonIsoOfInverts hψ')
        (derivedPullbackOfInverts hφ) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (homotopyPullbackFunctor Pψ Eψ)
        (pullbackComparisonIsoOfInverts hφ) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (homotopyPullbackFunctorCompIso Pφ Eφ Pψ Eψ Pχ Eχ) (toDerivedCategory.{t, a, m} A)⟩
  exact Localization.liftNatIso (toDerivedCategory.{t, a'', m} A'')
    (quasiIsomorphisms.{t, a'', m} A'')
    (homotopyPullbackFunctor Pχ Eχ ⋙ toDerivedCategory.{t, a, m} A)
    (homotopyPullbackFunctor Pχ Eχ ⋙ toDerivedCategory.{t, a, m} A)
    (derivedPullbackOfInverts hχ)
    (derivedPullbackOfInverts hψ' ⋙ derivedPullbackOfInverts hφ) (Iso.refl _)

end Composition

/-! ### Derived pushforward along a composition -/

section PushforwardComposition

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  {C'' : Type u''} [Category.{v''} C''] {J'' : GrothendieckTopology C''}
  {R'' : Sheaf J'' RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J' AddCommGrpCat.{m}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J'' AddCommGrpCat.{m}] [J''.WEqualsLocallyBijective AddCommGrpCat.{m}]
  {A : DifferentialGradedAlgebra.{t, a} R} {A' : DifferentialGradedAlgebra.{t, a'} R'}
  {A'' : DifferentialGradedAlgebra.{t, a''} R''}
  {u : C' ⥤ C} [u.IsContinuous J' J] {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {v : C'' ⥤ C'} [v.IsContinuous J'' J'] {τ : R''.obj ⟶ v.op ⋙ R'.obj}
  [(v ⋙ u).IsContinuous J'' J]
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A}
  {ψ : DifferentialGradedAlgebra.SemilinearHom v τ A'' A'}

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify J' AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify J'' AddCommGrpCat] [J''.WEqualsLocallyBijective AddCommGrpCat] in
/-- The direct image of a right differential graded module along a composition of morphisms of
ringed sites is the direct image along the first followed by the direct image along the second.
Both are the degreewise direct image along `v ⋙ u` of the underlying complex, with a
homogeneous section `b` of `A''` acting through `φ(ψ b)`. -/
theorem pushforwardObj_trans (M : DifferentialGradedModule.{t, a, m} A) :
    pushforwardObj (ψ.trans φ) M = pushforwardObj ψ (pushforwardObj φ M) :=
  rfl

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify J' AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify J'' AddCommGrpCat] [J''.WEqualsLocallyBijective AddCommGrpCat] in
/-- The direct image of sheaves of modules along a composition of morphisms of ringed sites is
the direct image along the first followed by the direct image along the second, on the nose. -/
theorem sitePushforward_comp :
    sitePushforward (v ⋙ u) (compRingMap u σ v τ) =
      (sitePushforward u σ : SheafOfModules.{m} R ⥤ _) ⋙ sitePushforward v τ :=
  rfl

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify J' AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify J'' AddCommGrpCat] [J''.WEqualsLocallyBijective AddCommGrpCat] in
/-- `pushforwardObj_trans` at the spelling of the two direct image functors. -/
theorem pushforwardFunctor_obj_trans (M : DifferentialGradedModule.{t, a, m} A) :
    (pushforwardFunctor.{t, a, m} (ψ.trans φ)).obj M =
      (pushforwardFunctor.{t, a, m} φ ⋙ pushforwardFunctor.{t, a', m} ψ).obj M :=
  pushforwardObj_trans M

omit [HasSheafify J'' AddCommGrpCat] [J''.WEqualsLocallyBijective AddCommGrpCat] in
/-- A component of `eqToHom` between right differential graded modules is `eqToHom`. -/
theorem eqToHom_toHomologicalComplex_f {M M' : DifferentialGradedModule.{t, a'', m} A''}
    (h : M = M') (n : ℤ) :
    (eqToHom h).toHomologicalComplex.f n = eqToHom (congrArg (fun K => K.complex.X n) h) := by
  subst h
  rfl

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify J' AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify J'' AddCommGrpCat] [J''.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The direct image along a composition**: `(g ∘ f)_* = g_* ∘ f_*` as functors of right
differential graded modules. The underlying complexes agree because the direct image of sheaves
of modules along `v ⋙ u` with the composite structure map *is* the composite of the two direct
images, which is `SheafOfModules.pushforwardComp`, an identity isomorphism. -/
theorem pushforwardFunctor_trans :
    pushforwardFunctor.{t, a, m} (ψ.trans φ) =
      pushforwardFunctor.{t, a, m} φ ⋙ pushforwardFunctor.{t, a', m} ψ :=
  CategoryTheory.Functor.ext pushforwardFunctor_obj_trans fun M N k => Hom.ext fun n => by
    rw [comp_f, comp_f, eqToHom_toHomologicalComplex_f, eqToHom_toHomologicalComplex_f,
      pushforwardFunctor_map_f, Functor.comp_map, pushforwardFunctor_map_f,
      pushforwardFunctor_map_f]
    exact Functor.congr_hom sitePushforward_comp (k.toHomologicalComplex.f n)

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify J' AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify J'' AddCommGrpCat] [J''.WEqualsLocallyBijective AddCommGrpCat] in
/-- `K((g ∘ f)_*) = K(f_*) ⋙ K(g_*)` on the homotopy categories: the direct image along the
composition is the composite of the two direct images already on modules, and descent to the
homotopy categories is compatible with composition. -/
theorem homotopyPushforwardFunctor_trans :
    (homotopyPushforwardFunctor (ψ.trans φ) :
        HomotopyCategory.{t, a, m} A ⥤ HomotopyCategory.{t, a'', m} A'') =
      homotopyPushforwardFunctor φ ⋙ homotopyPushforwardFunctor ψ :=
  (HomotopyCategory.eq_descend _
      (PreservesHomotopic.comp (preservesHomotopic_pushforwardFunctor φ)
        (preservesHomotopic_pushforwardFunctor ψ))
      (homotopyPushforwardFunctor (ψ.trans φ))
      ((HomotopyCategory.quotient_comp_descend (pushforwardFunctor.{t, a, m} (ψ.trans φ))
          (preservesHomotopic_pushforwardFunctor (ψ.trans φ))).trans
        (congrArg (fun F => F ⋙ HomotopyCategory.quotient A'')
          pushforwardFunctor_trans))).trans
    (HomotopyCategory.descend_comp _ _ _ _)

/-- If the direct images along `f` and along `g` both carry quasi-isomorphisms of the underlying
complexes of sheaves of modules to quasi-isomorphisms, so does the direct image along `g ∘ f`,
being their composite. -/
theorem quasiIso_pushforwardFunctor_trans_map
    (hf : ∀ {M N : DifferentialGradedModule.{t, a, m} A} (k : M ⟶ N),
      QuasiIso k.toHomologicalComplex →
        QuasiIso ((pushforwardFunctor.{t, a, m} φ).map k).toHomologicalComplex)
    (hg : ∀ {M N : DifferentialGradedModule.{t, a', m} A'} (k : M ⟶ N),
      QuasiIso k.toHomologicalComplex →
        QuasiIso ((pushforwardFunctor.{t, a', m} ψ).map k).toHomologicalComplex)
    {M N : DifferentialGradedModule.{t, a, m} A} (k : M ⟶ N)
    (hk : QuasiIso k.toHomologicalComplex) :
    QuasiIso ((pushforwardFunctor.{t, a, m} (ψ.trans φ)).map k).toHomologicalComplex := by
  rw [pushforwardFunctor_trans]
  exact hg _ (hf k hk)

variable (gφ : (quasiIsomorphisms.{t, a, m} A).IsInvertedBy
    (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{t, a', m} A'))
  (gψ : (quasiIsomorphisms.{t, a', m} A').IsInvertedBy
    (homotopyPushforwardFunctor ψ ⋙ toDerivedCategory.{t, a'', m} A''))
  (gχ : (quasiIsomorphisms.{t, a, m} A).IsInvertedBy
    (homotopyPushforwardFunctor (ψ.trans φ) ⋙ toDerivedCategory.{t, a'', m} A''))

/-- **Composition for exact pairs**: the derived pushforward along a composition is the derived
pushforward along `f` followed by the derived pushforward along `g`. Both sides lift
`K((g ∘ f)_*)` followed by the localization — the right-hand side through the two comparison
isomorphisms and `homotopyPushforwardFunctor_trans` — so they agree by uniqueness of the
factorisation through a localization. No adjunction and no pullback enter. -/
noncomputable def derivedPushforwardOfInvertsCompIso :
    derivedPushforwardOfInverts gχ ≅
      derivedPushforwardOfInverts gφ ⋙ derivedPushforwardOfInverts gψ := by
  letI : Localization.Lifting (toDerivedCategory.{t, a, m} A) (quasiIsomorphisms.{t, a, m} A)
      (homotopyPushforwardFunctor (ψ.trans φ) ⋙ toDerivedCategory.{t, a'', m} A'')
      (derivedPushforwardOfInverts gφ ⋙ derivedPushforwardOfInverts gψ) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pushforwardComparisonIsoOfInverts gφ).symm
        (derivedPushforwardOfInverts gψ) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (homotopyPushforwardFunctor φ)
        (pushforwardComparisonIsoOfInverts gψ).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (eqToIso homotopyPushforwardFunctor_trans.symm)
        (toDerivedCategory.{t, a'', m} A'')⟩
  exact Localization.liftNatIso (toDerivedCategory.{t, a, m} A) (quasiIsomorphisms.{t, a, m} A)
    (homotopyPushforwardFunctor (ψ.trans φ) ⋙ toDerivedCategory.{t, a'', m} A'')
    (homotopyPushforwardFunctor (ψ.trans φ) ⋙ toDerivedCategory.{t, a'', m} A'')
    (derivedPushforwardOfInverts gχ)
    (derivedPushforwardOfInverts gφ ⋙ derivedPushforwardOfInverts gψ) (Iso.refl _)

/-! ### Composition for arbitrary derived pushforwards and exact direct images -/

section Tag

variable {Pφ : PullbackData φ} {Eφ : Pφ.HomotopyExtension}
  {Pψ : PullbackData ψ} {Eψ : Pψ.HomotopyExtension}
  {Pχ : PullbackData (ψ.trans φ)} {Eχ : Pχ.HomotopyExtension}
  (Dφ : DerivedPushPullData Pφ Eφ) (Dψ : DerivedPushPullData Pψ Eψ)
  (Dχ : DerivedPushPullData Pχ Eχ)
  (hf : (sitePushforward u σ :
    SheafOfModules.{m} R ⥤ SheafOfModules.{m} R').PreservesHomology)
  (hg : (sitePushforward v τ :
    SheafOfModules.{m} R' ⥤ SheafOfModules.{m} R'').PreservesHomology)

/-- **The composition isomorphism for exact direct images**: `R(g ∘ f)_* ≅ Rf_* ⋙ Rg_*`. Exactness
of the two direct images of sheaves of modules makes `K(f_*)`, `K(g_*)` and `K((g ∘ f)_*)` invert
the quasi-isomorphisms after localization; each of the three carried derived pushforwards is then
the functor induced on the derived categories, because the comparison map of any derived extension
of an inverting functor is an isomorphism; and those three induced functors compose by
`derivedPushforwardOfInvertsCompIso`. -/
noncomputable def derivedPushforwardCompIso :
    Dχ.derivedPushforward ≅ Dφ.derivedPushforward ⋙ Dψ.derivedPushforward := by
  have gφ : (quasiIsomorphisms.{t, a, m} A).IsInvertedBy
      (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{t, a', m} A') :=
    isInvertedBy_homotopyPushforwardFunctor_comp (φ := φ)
      fun k hk => quasiIso_pushforwardFunctor_map hf k hk
  have gψ : (quasiIsomorphisms.{t, a', m} A').IsInvertedBy
      (homotopyPushforwardFunctor ψ ⋙ toDerivedCategory.{t, a'', m} A'') :=
    isInvertedBy_homotopyPushforwardFunctor_comp (φ := ψ)
      fun k hk => quasiIso_pushforwardFunctor_map hg k hk
  have gχ : (quasiIsomorphisms.{t, a, m} A).IsInvertedBy
      (homotopyPushforwardFunctor (ψ.trans φ) ⋙ toDerivedCategory.{t, a'', m} A'') :=
    isInvertedBy_homotopyPushforwardFunctor_comp (φ := ψ.trans φ)
      fun k hk => quasiIso_pushforwardFunctor_trans_map
        (fun k' hk' => quasiIso_pushforwardFunctor_map hf k' hk')
        (fun k' hk' => quasiIso_pushforwardFunctor_map hg k' hk') k hk
  exact (derivedPushforwardIsoOfInverts gχ Dχ).symm ≪≫
    derivedPushforwardOfInvertsCompIso gφ gψ gχ ≪≫
    Functor.isoWhiskerRight (derivedPushforwardIsoOfInverts gφ Dφ)
      (derivedPushforwardOfInverts gψ) ≪≫
    Functor.isoWhiskerLeft Dφ.derivedPushforward (derivedPushforwardIsoOfInverts gψ Dψ)

include hf hg in
/-- Derived pushforward along a composition of morphisms of ringed sites with exact direct
images, for arbitrary derived pushforwards. Let
`(f, f♯) : (Sh(C), O) ⟶ (Sh(C'), O')` and `(g, g♯) : (Sh(C'), O') ⟶ (Sh(C''), O'')` be morphisms
of ringed sites, presented by continuous functors `u : C' ⥤ C` and `v : C'' ⥤ C'` in the
opposite directions together with the structure maps `σ` and `τ` of their sheaves of rings. Let
`A`, `A'`, `A''` be sheaves of differential graded algebras over `O`, `O'`, `O''` and let
`φ : A' ⟶ f_*A` and `ψ : A'' ⟶ g_*A'` be homomorphisms, so that `ψ.trans φ : A'' ⟶ (g ∘ f)_*A`
is the composite homomorphism. Assume that the direct images of sheaves of modules along `f` and
along `g` preserve homology. Then
`R(g ∘ f)_* = Rg_* ∘ Rf_* : D(A, d) ⟶ D(A'', d)`,
in the form available here: for *any* derived pushforwards `Rf_*`, `Rg_*` and `R(g ∘ f)_*` —
any functors on the derived categories satisfying, with their comparison maps, the derived-value
condition of [Stacks, Tag 05S9](https://stacks.math.columbia.edu/tag/05S9) for `K(f_*)`,
`K(g_*)` and `K((g ∘ f)_*)` — the functor `R(g ∘ f)_*` is isomorphic to `Rf_*` followed by
`Rg_*`. The isomorphism is `derivedPushforwardCompIso`. Tag 0FTU itself, for the derived
pushforwards along morphisms of ringed topoi, is
`SheafOfModules.DifferentialGradedModule.derivedToposPushforward_comp`. -/
theorem nonempty_derivedPushforward_comp_iso :
    Nonempty (Dχ.derivedPushforward ≅ Dφ.derivedPushforward ⋙ Dψ.derivedPushforward) :=
  ⟨derivedPushforwardCompIso Dφ Dψ Dχ hf hg⟩

end Tag

end PushforwardComposition

end DifferentialGradedModule

end SheafOfModules

end
