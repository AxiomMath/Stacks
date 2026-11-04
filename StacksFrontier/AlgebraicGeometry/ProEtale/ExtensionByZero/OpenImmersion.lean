module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.Abelian
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.Modules
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.Sets
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Big
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Slices
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallToBigTopos
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.Subtopos.Open
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksCore.Tactic.StacksAttribute

/-!
# Open immersions and pro-étale sheaves

For an open immersion, restriction after extension by zero and inverse image after direct
image are canonically the identity. Consequently both extension by zero and direct image are
fully faithful. The assertions hold for sheaves of sets, abelian groups, and modules.

## Main results

* `AlgebraicGeometry.ProEtale.extensionByZero_unit_isIso_sets`,
  `AlgebraicGeometry.ProEtale.extensionByZero_unit_isIso_abelian` and
  `AlgebraicGeometry.ProEtale.extensionByZero_unit_isIso_modules` give the canonical unit
  isomorphisms.
* `AlgebraicGeometry.ProEtale.directImage_counit_isIso_sets`,
  `AlgebraicGeometry.ProEtale.directImage_counit_isIso_abelian` and
  `AlgebraicGeometry.ProEtale.directImage_counit_isIso_modules` give the canonical counit
  isomorphisms.
* `AlgebraicGeometry.ProEtale.extensionByZero_fullyFaithful_sets`,
  `AlgebraicGeometry.ProEtale.directImage_fullyFaithful_sets` and their abelian and module
  counterparts give full faithfulness.

## Implementation notes

For sheaves of sets, the direct-image adjunction is the small pro-étale morphism of topoi in a
chosen big site. For abelian and module sheaves, the right adjoint to restriction is specified
by its adjunction; existence and the counit property are stated separately. The canonical unit
and counit are used rather than unspecified functor isomorphisms.

## References

* [Stacks Project, Tag 09BN](https://stacks.math.columbia.edu/tag/09BN)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.ProEtale

private theorem proetalePostcompose_fullFaithful {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    Nonempty (proetalePostcompose j).FullyFaithful := by
  let j' : X.ProEt := Scheme.ProEt.mk j
  have hsub : IsSubterminal j' := by
    intro Y f g
    apply (Scheme.ProEt.forget X).map_injective
    apply Over.OverMorphism.ext
    apply (cancel_mono j).1
    exact (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm
  have : (Over.forget j').Full := (full_overForget_iff_isSubterminal j').2 hsub
  let e := localizationEquivalence j'
  have hcomp : (e.functor ⋙ Over.forget j').FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful e.functor).comp
      (Functor.FullyFaithful.ofFullyFaithful (Over.forget j'))
  exact ⟨hcomp.ofIso (eqToIso (localizationEquivalence_forget (j := j')))⟩

private theorem proetalePostcompose_isCocontinuous_of_object {X : Scheme.{u}}
    (j : X.ProEt) :
    (proetalePostcompose j.hom).IsCocontinuous
      (Scheme.ProEt.topology j.left) (Scheme.ProEt.topology X) := by
  let e := localizationEquivalence j
  have he : e.functor.IsCocontinuous (Scheme.ProEt.topology j.left)
      ((Scheme.ProEt.topology X).over j) := by
    rw [localizationEquivalence_inducedTopology]
    infer_instance
  have : (Over.forget j).IsCocontinuous
      ((Scheme.ProEt.topology X).over j) (Scheme.ProEt.topology X) := inferInstance
  have : (e.functor ⋙ Over.forget j).IsCocontinuous
      (Scheme.ProEt.topology j.left) (Scheme.ProEt.topology X) :=
    isCocontinuous_comp e.functor (Over.forget j)
      (Scheme.ProEt.topology j.left) ((Scheme.ProEt.topology X).over j)
  exact Functor.IsCocontinuous.of_iso (eqToIso (localizationEquivalence_forget j))

private theorem proetalePostcompose_isCocontinuous {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (proetalePostcompose j).IsCocontinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) :=
  proetalePostcompose_isCocontinuous_of_object (Scheme.ProEt.mk j)

private theorem proetalePostcompose_unit_isIso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : Type w} [Category.{v} A]
    [(proetalePostcompose j).IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)]
    [∀ F : U.ProEtᵒᵖ ⥤ A,
      (proetalePostcompose j).op.HasPointwiseRightKanExtension F]
    {L : Sheaf (Scheme.ProEt.topology U) A ⥤ Sheaf (Scheme.ProEt.topology X) A}
    (adj : L ⊣ (proetalePostcompose j).sheafPushforwardContinuous
      A (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)) :
    IsIso adj.unit := by
  have := proetalePostcompose_isCocontinuous j
  obtain ⟨hff⟩ := proetalePostcompose_fullFaithful j
  have := hff.full
  have := hff.faithful
  exact Functor.isIso_unit_of_sheafPushforwardContinuous
    (proetalePostcompose j) A
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) adj

/-- Restriction along an open immersion has a right adjoint. -/
private theorem exists_adjoint_proetalePostcompose
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type w) [Category.{v} A]
    [(proetalePostcompose j).IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)]
    [∀ F : U.ProEtᵒᵖ ⥤ A,
      (proetalePostcompose j).op.HasPointwiseRightKanExtension F] :
    Nonempty (Σ R : Sheaf (Scheme.ProEt.topology U) A ⥤ Sheaf (Scheme.ProEt.topology X) A,
      (proetalePostcompose j).sheafPushforwardContinuous
        A (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) ⊣ R) := by
  have := proetalePostcompose_isCocontinuous j
  exact ⟨⟨_, (proetalePostcompose j).sheafAdjunctionCocontinuous A _ _⟩⟩

/-- The extension-by-zero unit for sheaves of sets along an open immersion
is a natural isomorphism. -/
@[stacks 09BN "sets: extension-by-zero unit"]
theorem extensionByZero_unit_isIso_sets {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (Sets.extensionByZeroAdjunction.{u, v} j).unit := by
  have := proetalePostcompose_isContinuous j
  exact proetalePostcompose_unit_isIso j (Sets.extensionByZeroAdjunction.{u, v} j)

/-- Extension by zero of pro-étale sheaves of sets is fully faithful. -/
@[stacks 09BN "sets: extension by zero fully faithful"]
theorem extensionByZero_fullyFaithful_sets {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty (Sets.extensionByZero.{u, v} j).FullyFaithful := by
  let adj := Sets.extensionByZeroAdjunction.{u, v} j
  have hu : IsIso adj.unit := extensionByZero_unit_isIso_sets j
  exact ⟨Adjunction.fullyFaithfulLOfIsIsoUnit adj⟩

private def smallProetalePostcompose
    (B : BigProetaleSite.{u}) {T S : B.Scheme} (j : T ⟶ S)
    [IsOpenImmersion (B.inclusion.map j)] :
    SmallProetale B T.obj T.property ⥤ SmallProetale B S.obj S.property := by
  refine (IsWeaklyEtaleOver B S.obj S.property).lift
    (SmallProetale.inclusion B T.obj T.property ⋙ Over.map j) ?_
  intro X
  change WeaklyEtale (B.inclusion.map X.obj.hom ≫ B.inclusion.map j)
  infer_instance

private theorem smallProetalePostcompose_comp_inclusion
    (B : BigProetaleSite.{u}) {T S : B.Scheme} (j : T ⟶ S)
    [IsOpenImmersion (B.inclusion.map j)] :
    smallProetalePostcompose B j ⋙ SmallProetale.inclusion B S.obj S.property =
      SmallProetale.inclusion B T.obj T.property ⋙ Over.map j :=
  rfl

private noncomputable def smallProetalePostcompose_adj
    (B : BigProetaleSite.{u}) {T S : B.Scheme} (j : T ⟶ S)
    [IsOpenImmersion (B.inclusion.map j)] :
    smallProetalePostcompose B j ⊣ smallProetaleBaseChange B T S j := by
  let iT := SmallProetale.inclusion B T.obj T.property
  let iS := SmallProetale.inclusion B S.obj S.property
  have hcomm₁ : iT ⋙ Over.map j ≅ smallProetalePostcompose B j ⋙ iS :=
    eqToIso (smallProetalePostcompose_comp_inclusion B j).symm
  have hcomm₂ : iS ⋙ Over.pullback j ≅
      smallProetaleBaseChange B T S j ⋙ iT :=
    eqToIso (smallProetaleBaseChange_comp_inclusion B T S j).symm
  exact (Over.mapPullbackAdj j).restrictFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful iT)
    (Functor.FullyFaithful.ofFullyFaithful iS) hcomm₁ hcomm₂

private theorem openImmersion_mono_in_bigSite
    (B : BigProetaleSite.{u}) {T S : B.Scheme} (j : T ⟶ S)
    [IsOpenImmersion (B.inclusion.map j)] : Mono j := by
  refine ⟨fun {Y} f g h => ?_⟩
  apply B.inclusion.map_injective
  apply (cancel_mono (B.inclusion.map j)).1
  simpa using congrArg (fun k => B.inclusion.map k) h

/-- Postcomposition with a monomorphism is a fully faithful functor of slice categories. -/
private noncomputable def overMap_fullyFaithful_of_mono
    {C : Type u} [Category.{v} C] {T S : C} (j : T ⟶ S) [Mono j] :
    (Over.map j).FullyFaithful := by
  have : (Over.map j).Full := {
    map_surjective := by
      intro X Y f
      refine ⟨Over.homMk f.left (by
        apply (cancel_mono j).1
        simpa [Category.assoc] using (Over.w f)), ?_⟩
      ext
      rfl }
  have : (Over.map j).Faithful := {
    map_injective := by
      intro X Y f g h
      apply Over.OverMorphism.ext
      simpa using congrArg Over.Hom.left h }
  exact Functor.FullyFaithful.ofFullyFaithful (Over.map j)

private noncomputable def smallProetalePostcompose_fullFaithful
    (B : BigProetaleSite.{u}) {T S : B.Scheme} (j : T ⟶ S)
    [IsOpenImmersion (B.inclusion.map j)] :
    (smallProetalePostcompose B j).FullyFaithful := by
  have : Mono j := openImmersion_mono_in_bigSite B j
  let iT := SmallProetale.inclusion B T.obj T.property
  let iS := SmallProetale.inclusion B S.obj S.property
  have hmap := overMap_fullyFaithful_of_mono j
  have hcomp : (iT ⋙ Over.map j).FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful iT).comp hmap
  have heq := smallProetalePostcompose_comp_inclusion B j
  have : (smallProetalePostcompose B j ⋙ iS).Full := by
    rw [heq]
    exact hcomp.full
  have : (smallProetalePostcompose B j ⋙ iS).Faithful := by
    rw [heq]
    exact hcomp.faithful
  have hf : (smallProetalePostcompose B j).Full :=
    Functor.Full.of_comp_faithful (smallProetalePostcompose B j) iS
  have hfaith : (smallProetalePostcompose B j).Faithful :=
    Functor.Faithful.of_comp (smallProetalePostcompose B j) iS
  exact Functor.FullyFaithful.ofFullyFaithful (smallProetalePostcompose B j)

private theorem smallProetalePostcompose_siteProperties
    (B : BigProetaleSite.{u}) {T S : B.Scheme} (j : T ⟶ S)
    [IsOpenImmersion (B.inclusion.map j)] :
    (smallProetalePostcompose B j).IsContinuous
        (SmallProetale.topology B T.obj T.property)
        (SmallProetale.topology B S.obj S.property) ∧
    (smallProetalePostcompose B j).IsCocontinuous
        (SmallProetale.topology B T.obj T.property)
        (SmallProetale.topology B S.obj S.property) := by
  have : (smallProetalePostcompose B j).Full :=
    (smallProetalePostcompose_fullFaithful B j).full
  have : (smallProetalePostcompose B j).Faithful :=
    (smallProetalePostcompose_fullFaithful B j).faithful
  let u := smallProetalePostcompose B j
  let iS := SmallProetale.inclusion B S.obj S.property
  let v := smallProetaleToBigProetaleFunctor B T S j
  have heq : u ⋙ iS = v := by
    simpa [u, v, smallProetaleToBigProetaleFunctor] using
      smallProetalePostcompose_comp_inclusion B j
  have : v.IsCocontinuous (SmallProetale.topology B T.obj T.property)
      (BigProetaleOver.topology B S.obj S.property) :=
    smallProetaleToBigProetaleFunctor_isCocontinuous B T S j
  have : v.IsContinuous (SmallProetale.topology B T.obj T.property)
      (BigProetaleOver.topology B S.obj S.property) :=
    smallProetaleToBigProetaleFunctor_isContinuous B T S j
  let uAdj := smallProetalePostcompose_adj B j
  let F := smallProetaleBaseChange B T S j
  have : F.IsContinuous (SmallProetale.topology B S.obj S.property)
      (SmallProetale.topology B T.obj T.property) :=
    (smallProetaleBaseChange_isMorphismOfSites B T S j).toIsContinuous
  have hcovF : CoverPreserving (SmallProetale.topology B S.obj S.property)
      (SmallProetale.topology B T.obj T.property) F :=
    CoverPreserving.of_isContinuous F _ _
  have : u.IsCocontinuous (SmallProetale.topology B T.obj T.property)
      (SmallProetale.topology B S.obj S.property) :=
    (uAdj.isCocontinuous_iff_coverPreserving _ _).2 hcovF
  let eId := smallProetaleToBigProetaleFunctor B S S (𝟙 S)
  have eId_eq : eId = iS := by
    dsimp [eId, smallProetaleToBigProetaleFunctor]
    rw [Over.mapId_eq]
    rfl
  have : eId.IsCocontinuous (SmallProetale.topology B S.obj S.property)
      (BigProetaleOver.topology B S.obj S.property) :=
    smallProetaleToBigProetaleFunctor_isCocontinuous B S S (𝟙 S)
  have : iS.IsCocontinuous (SmallProetale.topology B S.obj S.property)
      (BigProetaleOver.topology B S.obj S.property) :=
    Functor.IsCocontinuous.of_iso (eqToIso eId_eq)
  have hcovV : CoverPreserving (SmallProetale.topology B T.obj T.property)
      (BigProetaleOver.topology B S.obj S.property) v :=
    CoverPreserving.of_isContinuous v _ _
  have hcovU : CoverPreserving (SmallProetale.topology B T.obj T.property)
      (SmallProetale.topology B S.obj S.property) u := by
    have hcovcomp : CoverPreserving (SmallProetale.topology B T.obj T.property)
        (BigProetaleOver.topology B S.obj S.property) (u ⋙ iS) := by
      rw [heq]
      exact hcovV
    exact CoverPreserving.of_comp_of_isCocontinuous
      (SmallProetale.topology B T.obj T.property)
      (SmallProetale.topology B S.obj S.property) iS hcovcomp
  have hdown : ∀ {X : SmallProetale B T.obj T.property}
      {Y : SmallProetale B S.obj S.property} (_ : Y ⟶ u.obj X),
      Σ X', u.obj X' ≅ Y := by
    intro X Y f
    let k : Y.obj.left ⟶ T := f.hom.left ≫ X.obj.hom
    have hw : k ≫ j = Y.obj.hom := by
      dsimp [k]
      simpa [u, smallProetalePostcompose, Category.assoc] using Over.w f.hom
    let hWeak : WeaklyEtale (B.inclusion.map k) := by
      have hY := Y.property
      change WeaklyEtale (B.inclusion.map Y.obj.hom) at hY
      have : WeaklyEtale (B.inclusion.map k ≫ B.inclusion.map j) := by
        rw [← Functor.map_comp, hw]
        exact hY
      exact WeaklyEtale.of_comp (B.inclusion.map k) (B.inclusion.map j)
    let X' : SmallProetale B T.obj T.property :=
      ⟨Over.mk k, hWeak⟩
    refine ⟨X', ObjectProperty.isoMk _ (Over.isoMk (Iso.refl _) ?_)⟩
    simpa [X', u, smallProetalePostcompose, k, Category.assoc] using hw.symm
  have hcompat : CompatiblePreserving (SmallProetale.topology B S.obj S.property) u :=
    compatiblePreservingOfDownwardsClosed
      (SmallProetale.topology B S.obj S.property) u hdown
  exact ⟨Functor.isContinuous_of_coverPreserving hcompat hcovU, inferInstance⟩

/-- The direct-image counit for sheaves of sets along an open immersion
is a natural isomorphism. -/
@[stacks 09BN "sets: direct-image counit", sga "4 I 5.7" "u_* half, sheaves of"]
theorem directImage_counit_isIso_sets
    (B : BigProetaleSite.{u}) {T S : B.Scheme} (j : T ⟶ S)
    [IsOpenImmersion (B.inclusion.map j)] :
    IsIso (smallProetaleMorphism B T S j).adj.counit := by
  let post := smallProetalePostcompose B j
  let siteAdj := smallProetalePostcompose_adj B j
  have hprops := smallProetalePostcompose_siteProperties B j
  have : post.IsContinuous (SmallProetale.topology B T.obj T.property)
      (SmallProetale.topology B S.obj S.property) := hprops.1
  have : post.IsCocontinuous (SmallProetale.topology B T.obj T.property)
      (SmallProetale.topology B S.obj S.property) := hprops.2
  have hff := smallProetalePostcompose_fullFaithful B j
  have : post.Full := hff.full
  have : post.Faithful := hff.faithful
  have : ∀ F : (SmallProetale B T.obj T.property)ᵒᵖ ⥤ Type (u + 1),
      post.op.HasPointwiseRightKanExtension F := by
    intro F
    infer_instance
  let A := Type (u + 1)
  let JT := SmallProetale.topology B T.obj T.property
  let JS := SmallProetale.topology B S.obj S.property
  have : (smallProetaleBaseChange B T S j).IsContinuous JS JT :=
    (smallProetaleBaseChange_isMorphismOfSites B T S j).toIsContinuous
  let canonical := post.sheafAdjunctionCocontinuous A JT JS
  have : IsIso canonical.counit :=
    Functor.isIso_sheafAdjunctionCocontinuous_counit post A JT JS
  have hpush : post.sheafPushforwardCocontinuous A JT JS ≅
      (smallProetaleBaseChange B T S j).sheafPushforwardContinuous A JS JT :=
    siteAdj.sheafPushforwardCocontinuousIso A
  have hffR : (post.sheafPushforwardCocontinuous A JT JS).FullyFaithful :=
    Adjunction.fullyFaithfulROfIsIsoCounit canonical
  let hff' : ((smallProetaleBaseChange B T S j).sheafPushforwardContinuous
      A JS JT).FullyFaithful := hffR.ofIso hpush
  have : ((smallProetaleBaseChange B T S j).sheafPushforwardContinuous
      A JS JT).Full := hff'.full
  have : ((smallProetaleBaseChange B T S j).sheafPushforwardContinuous
      A JS JT).Faithful := hff'.faithful
  have : (smallProetaleMorphism B T S j).pushforward.Full := by
    simpa [smallProetaleMorphism, A, JT, JS] using hff'.full
  have : (smallProetaleMorphism B T S j).pushforward.Faithful := by
    simpa [smallProetaleMorphism, A, JT, JS] using hff'.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful
    (smallProetaleMorphism B T S j).adj

/-- Direct image of pro-étale sheaves of sets is fully faithful. -/
@[stacks 09BN "sets: direct image fully faithful"]
theorem directImage_fullyFaithful_sets
    (B : BigProetaleSite.{u}) {T S : B.Scheme} (j : T ⟶ S)
    [IsOpenImmersion (B.inclusion.map j)] :
    Nonempty (smallProetaleMorphism B T S j).pushforward.FullyFaithful := by
  let adj := (smallProetaleMorphism B T S j).adj
  have hc : IsIso adj.counit := directImage_counit_isIso_sets B j
  exact ⟨Adjunction.fullyFaithfulROfIsIsoCounit adj⟩

/-- The extension-by-zero unit for abelian pro-étale sheaves along an open
immersion is a natural isomorphism. -/
@[stacks 09BN "abelian: extension-by-zero unit"]
theorem extensionByZero_unit_isIso_abelian {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (Abelian.extensionByZero_adjunction.{u, v} j).unit := by
  let adj := Abelian.extensionByZero_adjunction.{u, v} j
  have := proetalePostcompose_isContinuous j
  exact proetalePostcompose_unit_isIso j adj

/-- Extension by zero of abelian pro-étale sheaves is fully faithful. -/
@[stacks 09BN "abelian: extension by zero fully faithful"]
theorem extensionByZero_fullyFaithful_abelian {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty (Abelian.extensionByZero.{u, v} j).FullyFaithful := by
  let adj := Abelian.extensionByZero_adjunction.{u, v} j
  have hu : IsIso adj.unit := extensionByZero_unit_isIso_abelian j
  exact ⟨Adjunction.fullyFaithfulLOfIsIsoUnit adj⟩

/-- Restriction of abelian pro-étale sheaves has a right adjoint. -/
@[stacks 09BN "abelian: direct-image functor"]
theorem exists_directImage_abelian {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty (Σ R : Sheaf (Scheme.ProEt.topology U) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v},
      Abelian.proetaleRestriction j ⊣ R) := by
  have := proetalePostcompose_isContinuous j
  exact exists_adjoint_proetalePostcompose j _

/-- The counit of restriction and any of its right adjoints is invertible. -/
@[stacks 09BN "abelian: direct-image counit", sga "4 I 5.7" "u_* half, pro-étale"]
theorem directImage_counit_isIso_abelian {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology U) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v})
    (adj : Abelian.proetaleRestriction j ⊣ R) :
    IsIso adj.counit := by
  let left := Abelian.extensionByZero_adjunction j
  have hu : IsIso left.unit := extensionByZero_unit_isIso_abelian j
  exact (Adjunction.Triple.isIso_unit_iff_isIso_counit ⟨left, adj⟩).mp hu

/-- Direct image of abelian pro-étale sheaves is fully faithful. -/
@[stacks 09BN "abelian: direct image fully faithful"]
theorem directImage_fullyFaithful_abelian {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology U) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v})
    (adj : Abelian.proetaleRestriction j ⊣ R) :
    Nonempty R.FullyFaithful := by
  have hc : IsIso adj.counit := directImage_counit_isIso_abelian j R adj
  exact ⟨Adjunction.fullyFaithfulROfIsIsoCounit adj⟩

/-- The extension-by-zero unit for module pro-étale sheaves along an open
immersion is a natural isomorphism. -/
@[stacks 09BN "modules: extension-by-zero unit"]
theorem extensionByZero_unit_isIso_modules {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (Λ : Type v) [Ring Λ] :
    IsIso (Modules.extensionByZero_adjunction.{u, v, w} j Λ).unit := by
  let adj := Modules.extensionByZero_adjunction j Λ
  have := proetalePostcompose_isContinuous j
  exact proetalePostcompose_unit_isIso j adj

/-- Extension by zero of module pro-étale sheaves is fully faithful. -/
@[stacks 09BN "modules: extension by zero fully faithful"]
theorem extensionByZero_fullyFaithful_modules {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (Λ : Type v) [Ring Λ] :
    Nonempty (Modules.extensionByZero.{u, v, w} j Λ).FullyFaithful := by
  let adj := Modules.extensionByZero_adjunction j Λ
  have hu : IsIso adj.unit := extensionByZero_unit_isIso_modules j Λ
  exact ⟨Adjunction.fullyFaithfulLOfIsIsoUnit adj⟩

/-- Restriction of module pro-étale sheaves has a right adjoint. -/
@[stacks 09BN "modules: direct-image functor"]
theorem exists_directImage_modules {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (Λ : Type v) [Ring Λ] :
    Nonempty (Σ R : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ) ⥤
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ),
      Modules.proetaleRestriction j Λ ⊣ R) := by
  have := proetalePostcompose_isContinuous j
  exact exists_adjoint_proetalePostcompose j _

/-- The counit of restriction and any of its right adjoints is invertible. -/
@[stacks 09BN "modules: direct-image counit", sga "4 I 5.7" "u_* half, Λ-modules"]
theorem directImage_counit_isIso_modules {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (Λ : Type v) [Ring Λ]
    (R : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ) ⥤
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (adj : Modules.proetaleRestriction j Λ ⊣ R) :
    IsIso adj.counit := by
  let left := Modules.extensionByZero_adjunction j Λ
  have hu : IsIso left.unit := extensionByZero_unit_isIso_modules j Λ
  exact (Adjunction.Triple.isIso_unit_iff_isIso_counit ⟨left, adj⟩).mp hu

/-- Direct image of module pro-étale sheaves is fully faithful. -/
@[stacks 09BN "modules: direct image fully faithful"]
theorem directImage_fullyFaithful_modules {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (Λ : Type v) [Ring Λ]
    (R : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ) ⥤
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (adj : Modules.proetaleRestriction j Λ ⊣ R) :
    Nonempty R.FullyFaithful := by
  have hc : IsIso adj.counit := directImage_counit_isIso_modules j Λ R adj
  exact ⟨Adjunction.fullyFaithfulROfIsIsoCounit adj⟩

end AlgebraicGeometry.ProEtale

end
