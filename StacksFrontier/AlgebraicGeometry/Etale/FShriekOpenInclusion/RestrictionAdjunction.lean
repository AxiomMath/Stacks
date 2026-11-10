module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import StacksFrontier.AlgebraicGeometry.Cohomology.ProperOverBase.Functoriality
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekSubsheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.Etale.SupportedSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition

/-!
# Restriction of étale sheaves along an open immersion

Let `j : X' ⟶ X` be an open immersion in a big étale site. Post-composition with `j` is left
adjoint to base change along `j` as functors between the small étale sites of `X'` and `X`, so
restriction of abelian sheaves along `j` is a right adjoint at every coefficient universe. This
file records that adjunction, the identification of the restriction of a sheaf with the
pushforward along post-composition, and how supports of sections behave under it: the support of
a restricted section is the preimage of the support of the original one, and a section supported
on a closed subscheme of an open piece extends to a section of the ambient object with the
image support.

This is the first part of the construction of the extension-by-zero monomorphism
`(j ≫ f)_! F' ⟶ f_! F` of proper-support direct images.

## Main results

* `AlgebraicGeometry.SmallEtale.smallEtalePostcomposeAdjunction`: post-composition with an open
  immersion is left adjoint to base change along it.
* `AlgebraicGeometry.SmallEtale.openInclusionSheafPushforward_isRightAdjoint`: restriction of
  abelian sheaves along an open immersion is a right adjoint at every coefficient universe,
  its left adjoint being direct image along post-composition with the open immersion.

## References

* [Stacks Project, Tag 0F53](https://stacks.math.columbia.edu/tag/0F53)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.SmallEtale

/-- An open immersion of a big étale site, viewed as an object of the small étale site of its
target. -/
public abbrev openSiteObject (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)] : SmallEtale B X.obj X.property :=
  ⟨Over.mk j, inferInstanceAs (Etale (B.inclusion.map j))⟩

/-- Post-composition with an open immersion `j : X' ⟶ X`, as a functor from the small étale
site of `X'` to the small étale site of `X`. -/
private noncomputable def postcompose (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)] :
    SmallEtale B X'.obj X'.property ⥤ SmallEtale B X.obj X.property :=
  smallEtalePostcompose B X.obj X.property (openSiteObject B j)

private theorem postcompose_incl (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)] :
    postcompose B j ⋙ SmallEtale.inclusion B X.obj X.property =
      SmallEtale.inclusion B X'.obj X'.property ⋙ Over.map j := rfl

private instance postcompose_preservesPullbacks (B : BigEtaleSite.{u}) {X' X : B.Scheme}
    (j : X' ⟶ X) [IsOpenImmersion (B.inclusion.map j)] :
    PreservesLimitsOfShape WalkingCospan (postcompose B j) :=
  preservesPullbacks_smallEtalePostcompose B X.obj X.property (openSiteObject B j)

private instance postcompose_isContinuous (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)] :
    (postcompose B j).IsContinuous
      (SmallEtale.topology B X'.obj X'.property) (SmallEtale.topology B X.obj X.property) :=
  smallEtalePostcompose_isContinuous B X.obj X.property (openSiteObject B j)

private def openBaseChangeMap (B : BigEtaleSite.{u}) {X' X : B.Scheme}
    (j : X' ⟶ X) [IsOpenImmersion (B.inclusion.map j)]
    (W : SmallEtale B X.obj X.property) :
    (postcompose B j).obj ((smallEtaleBaseChange B j).obj W) ⟶ W :=
  letI := hasPullbacks_bigEtaleSite B
  CategoryTheory.ObjectProperty.homMk
    (Over.homMk (pullback.fst W.obj.hom j) (by
      change pullback.fst W.obj.hom j ≫ W.obj.hom =
        pullback.snd W.obj.hom j ≫ j
      exact pullback.condition))

private theorem openBaseChangeMap_isOpenImmersion (B : BigEtaleSite.{u})
    {X' X : B.Scheme} (j : X' ⟶ X) [IsOpenImmersion (B.inclusion.map j)]
    (W : SmallEtale B X.obj X.property) :
    IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map
      (openBaseChangeMap B j W)) := by
  let := hasPullbacks_bigEtaleSite B
  let : PreservesLimitsOfShape WalkingCospan B.inclusion :=
    preservesPullbacks_bigEtaleSiteInclusion B
  change IsOpenImmersion (B.inclusion.map (pullback.fst W.obj.hom j))
  exact MorphismProperty.of_isPullback
    (IsPullback.map B.inclusion (IsPullback.of_hasPullback W.obj.hom j).flip)
    (show IsOpenImmersion (B.inclusion.map j) from inferInstance)

private theorem openBaseChangeMap_range (B : BigEtaleSite.{u})
    {X' X : B.Scheme} (j : X' ⟶ X) [IsOpenImmersion (B.inclusion.map j)]
    (W : SmallEtale B X.obj X.property) :
    Set.range ((SmallEtale.toScheme B X.obj X.property).map
      (openBaseChangeMap B j W)).base =
      Set.preimage (B.inclusion.map W.obj.hom).base
        (Set.range (B.inclusion.map j).base) := by
  classical
  change Set.range (B.inclusion.map (pullback.fst W.obj.hom j)).base =
    Set.preimage (B.inclusion.map W.obj.hom).base
      (Set.range (B.inclusion.map j).base)
  let := hasPullbacks_bigEtaleSite B
  let : PreservesLimitsOfShape WalkingCospan B.inclusion :=
    preservesPullbacks_bigEtaleSiteInclusion B
  have hp : IsPullback
      (B.inclusion.map (pullback.fst W.obj.hom j))
      (B.inclusion.map (pullback.snd W.obj.hom j))
      (B.inclusion.map W.obj.hom) (B.inclusion.map j) :=
    IsPullback.map B.inclusion (IsPullback.of_hasPullback W.obj.hom j)
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(B.inclusion.map (pullback.snd W.obj.hom j)).base z, ?_⟩
    have h := congrArg (fun q : Scheme.Hom _ _ => q.base z) hp.w
    simpa [Scheme.Hom.comp_base, TopCat.coe_comp] using h.symm
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback hp x y hy.symm
    exact ⟨z, hz₁⟩

/-- Post-composition with an open immersion `j : X' ⟶ X` of a big étale site is left adjoint
to base change along it, as functors between the corresponding small étale sites. -/
public noncomputable def smallEtalePostcomposeAdjunction (B : BigEtaleSite.{u})
    {X' X : B.Scheme} (j : X' ⟶ X) [IsOpenImmersion (B.inclusion.map j)] :
    smallEtalePostcompose B X.obj X.property (openSiteObject B j) ⊣
      smallEtaleBaseChange B j :=
  (Over.mapPullbackAdj j).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι (BigEtaleOver.IsEtaleOver B X'.obj X'.property))
    (ObjectProperty.fullyFaithfulι (BigEtaleOver.IsEtaleOver B X.obj X.property))
    (eqToIso (smallEtalePostcompose_comp_inclusion B X.obj X.property (openSiteObject B j)))
    (eqToIso (smallEtaleBaseChange_comp_inclusion B j).symm)

private noncomputable abbrev adj (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)] :
    postcompose B j ⊣ smallEtaleBaseChange B j :=
  smallEtalePostcomposeAdjunction B j

private theorem openBaseChangeMap_naturality (B : BigEtaleSite.{u})
    {X' X : B.Scheme} (j : X' ⟶ X) [IsOpenImmersion (B.inclusion.map j)]
    (W₁ W₂ : SmallEtale B X.obj X.property) (g : W₁ ⟶ W₂) :
    (postcompose B j).map ((smallEtaleBaseChange B j).map g) ≫
        openBaseChangeMap B j W₂ = openBaseChangeMap B j W₁ ≫ g := by
  exact (adj B j).counit.naturality g

/-- Restriction of abelian sheaves to an open subscheme is the inverse image
of its small-étale site morphism, at every coefficient universe. -/
public instance openInclusionSheafPushforward_isRightAdjoint
    (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)] :
    ((smallEtaleBaseChange B j).sheafPushforwardContinuous AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).IsRightAdjoint := by
  let : (postcompose B j).IsContinuous
      (SmallEtale.topology B X'.obj X'.property) (SmallEtale.topology B X.obj X.property) :=
    postcompose_isContinuous B j
  let := smallEtaleBaseChange_isContinuous B j
  exact (Adjunction.sheafPushforwardContinuous (adj B j)
    (SmallEtale.topology B X'.obj X'.property)
    (SmallEtale.topology B X.obj X.property)).isRightAdjoint

private noncomputable def openRestrictionIso (B : BigEtaleSite.{u})
    {X' X : B.Scheme} (j : X' ⟶ X) [IsOpenImmersion (B.inclusion.map j)] :
    (postcompose B j).sheafPushforwardContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B X'.obj X'.property)
        (SmallEtale.topology B X.obj X.property) ≅
      (smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property) := by
  letI : (postcompose B j).IsContinuous
      (SmallEtale.topology B X'.obj X'.property)
      (SmallEtale.topology B X.obj X.property) := postcompose_isContinuous B j
  letI := smallEtaleBaseChange_isContinuous B j
  let adj₁ :
      (postcompose B j).sheafPushforwardContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B X'.obj X'.property)
        (SmallEtale.topology B X.obj X.property) ⊣
      (smallEtaleBaseChange B j).sheafPushforwardContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property) :=
    Adjunction.sheafPushforwardContinuous (adj B j)
      (SmallEtale.topology B X'.obj X'.property)
      (SmallEtale.topology B X.obj X.property)
  let adj₂ := (smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X'.obj X'.property)
  exact Adjunction.leftAdjointUniq adj₁ adj₂

private theorem openRestrictionIso_unit_app (B : BigEtaleSite.{u})
    {X' X : B.Scheme} (j : X' ⟶ X) [IsOpenImmersion (B.inclusion.map j)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (W : SmallEtale B X.obj X.property) (s : F.obj.obj (op W)) :
    ((openRestrictionIso B j).hom.app F).hom.app
        (op ((smallEtaleBaseChange B j).obj W))
        (F.obj.map (openBaseChangeMap B j W).op s) =
      (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app (op W) s := by
  let : (postcompose B j).IsContinuous
      (SmallEtale.topology B X'.obj X'.property)
      (SmallEtale.topology B X.obj X.property) := postcompose_isContinuous B j
  let := smallEtaleBaseChange_isContinuous B j
  let adj₁ :
      (postcompose B j).sheafPushforwardContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B X'.obj X'.property)
        (SmallEtale.topology B X.obj X.property) ⊣
      (smallEtaleBaseChange B j).sheafPushforwardContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property) :=
    Adjunction.sheafPushforwardContinuous (adj B j)
      (SmallEtale.topology B X'.obj X'.property)
      (SmallEtale.topology B X.obj X.property)
  let adj₂ :
      (smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property) ⊣
      (smallEtaleBaseChange B j).sheafPushforwardContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property) :=
    (smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)
  exact congrArg (fun η => η.hom.app (op W) s)
    (Adjunction.unit_leftAdjointUniq_hom_app adj₁ adj₂ F)

private theorem supportSection_iso_app_eq
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (e : F ≅ G) (U : SmallEtale B S hS) (s : F.obj.obj (op U)) :
    SmallEtale.supportSection B S hS G U
        (e.hom.hom.app (op U) s) =
      SmallEtale.supportSection B S hS F U s := by
  apply Set.Subset.antisymm
  · exact SmallEtale.supportSection_map_subset
      B S hS F G e.hom U s
  · have h := SmallEtale.supportSection_map_subset
      B S hS G F e.inv U (e.hom.hom.app (op U) s)
    have hs : e.inv.hom.app (op U) (e.hom.hom.app (op U) s) = s := by
      rw [← ConcreteCategory.comp_apply]
      simp
    rwa [hs] at h

private theorem supportSection_postcompose_eq (B : BigEtaleSite.{u})
    {X' X : B.Scheme} (j : X' ⟶ X) [IsOpenImmersion (B.inclusion.map j)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (U : SmallEtale B X'.obj X'.property)
    (s : F.obj.obj (op ((postcompose B j).obj U))) :
    SmallEtale.supportSection B X'.obj X'.property
        (((postcompose B j).sheafPushforwardContinuous AddCommGrpCat.{v}
          (SmallEtale.topology B X'.obj X'.property)
          (SmallEtale.topology B X.obj X.property)).obj F) U s =
      SmallEtale.supportSection B X.obj X.property F
        ((postcompose B j).obj U) s := by
  let : (postcompose B j).IsContinuous
      (SmallEtale.topology B X'.obj X'.property)
      (SmallEtale.topology B X.obj X.property) := postcompose_isContinuous B j
  let PF := ((postcompose B j).sheafPushforwardContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B X'.obj X'.property)
    (SmallEtale.topology B X.obj X.property)).obj F
  have eU : (SmallEtale.toScheme B X'.obj X'.property).obj U =
      (SmallEtale.toScheme B X.obj X.property).obj ((postcompose B j).obj U) := rfl
  cases eU
  have hzero :
      SmallEtale.zeroOpen B X'.obj X'.property PF U s =
        SmallEtale.zeroOpen B X.obj X.property F
          ((postcompose B j).obj U) s := by
    apply congrArg sSup
    ext W
    change SmallEtale.IsZeroOpen B X'.obj X'.property PF U s W ↔
      SmallEtale.IsZeroOpen B X.obj X.property F
        ((postcompose B j).obj U) s W
    constructor
    · rintro ⟨V, g, hg, hW, hz⟩
      exact ⟨(postcompose B j).obj V, (postcompose B j).map g, hg, hW, hz⟩
    · rintro ⟨V, g, hg, hW, hz⟩
      let V' : SmallEtale B X'.obj X'.property :=
        ⟨Over.mk (g.hom.left ≫ U.obj.hom), by
          change IsOpenImmersion (B.inclusion.map g.hom.left) at hg
          have : IsOpenImmersion (B.inclusion.map g.hom.left) := hg
          exact B.etale_map_comp g.hom.left U.obj.hom inferInstance U.property⟩
      let g' : V' ⟶ U := CategoryTheory.ObjectProperty.homMk
        (Over.homMk g.hom.left (by rfl))
      let eVOver : V.obj ≅ ((postcompose B j).obj V').obj :=
        Over.isoMk (Iso.refl V.obj.left) (by
          simpa [postcompose, smallEtalePostcompose, V', Category.assoc] using (Over.w g.hom))
      let eV : V ≅ (postcompose B j).obj V' :=
        CategoryTheory.ObjectProperty.isoMk _ eVOver
      have hcomp : eV.hom ≫ (postcompose B j).map g' = g := by
        apply (SmallEtale.inclusion B X.obj X.property).map_injective
        apply Over.OverMorphism.ext
        rfl
      refine ⟨V', g', ?_, ?_, ?_⟩
      · change IsOpenImmersion (B.inclusion.map g.hom.left) at hg
        change IsOpenImmersion (B.inclusion.map g.hom.left)
        simpa [g'] using hg
      · exact hW
      · have hinj : Function.Injective (F.obj.map eV.hom.op) :=
          (AddCommGrpCat.mono_iff_injective _).mp inferInstance
        have hmaps :
            F.obj.map ((postcompose B j).map g').op ≫ F.obj.map eV.hom.op =
              F.obj.map g.op := by
          rw [← Functor.map_comp]
          congr 1
        have hpoint := congrArg (fun k => k s) hmaps
        have hzeroMap : F.obj.map eV.hom.op (F.obj.map ((postcompose B j).map g').op s) = 0 := by
          simpa [hz] using hpoint
        change F.obj.map ((postcompose B j).map g').op s = 0
        exact hinj (by simpa [map_zero] using hzeroMap)
  change (SmallEtale.zeroOpen B X'.obj X'.property PF U s).carrierᶜ =
    (SmallEtale.zeroOpen B X.obj X.property F
      ((postcompose B j).obj U) s).carrierᶜ
  exact congrArg Set.compl (congrArg TopologicalSpace.Opens.carrier hzero)

/-- A point whose image lies in the zero-open of `s` lies in the zero-open of its restriction. -/
private theorem mem_zeroOpen_restrict_of_map_mem (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U U' : SmallEtale B S hS) (φ : U' ⟶ U) (s : F.obj.obj (op U))
    (x : (SmallEtale.toScheme B S hS).obj U')
    (hx : ((SmallEtale.toScheme B S hS).map φ).base x ∈
      (SmallEtale.zeroOpen B S hS F U s : Set _)) :
    x ∈ SmallEtale.zeroOpen B S hS F U' (F.obj.map φ.op s) := by
  classical
  let T := SmallEtale.toScheme B S hS
  obtain ⟨W, hW, hxW⟩ := TopologicalSpace.Opens.mem_sSup.mp hx
  rcases hW with ⟨V, g, hg, hWr, hzero⟩
  let : HasPullbacks (SmallEtale B S hS) :=
    hasPullbacks_smallEtale B S hS
  let p₁ := pullback.fst g φ
  let p₂ := pullback.snd g φ
  let hpb : IsPullback (T.map p₁) (T.map p₂) (T.map g) (T.map φ) := by
    let : PreservesLimitsOfShape WalkingCospan T :=
      preservesPullbacks_smallEtaleToScheme B S hS
    exact IsPullback.map T (IsPullback.of_hasPullback g φ)
  let : IsOpenImmersion (T.map p₂) := by
    let : IsOpenImmersion (T.map g) := hg
    exact MorphismProperty.of_isPullback hpb hg
  have hzero' : F.obj.map p₂.op (F.obj.map φ.op s) = 0 := by
    calc
      F.obj.map p₂.op (F.obj.map φ.op s) = F.obj.map (φ.op ≫ p₂.op) s := by
        change (F.obj.map φ.op ≫ F.obj.map p₂.op) s = _
        rw [← F.obj.map_comp]
      _ = F.obj.map (p₂ ≫ φ).op s := by rw [← op_comp]
      _ = F.obj.map (p₁ ≫ g).op s := by
        congr 1
        rw [← pullback.condition]
      _ = F.obj.map p₁.op (F.obj.map g.op s) := by
        simp only [op_comp, F.obj.map_comp, ConcreteCategory.comp_apply]
      _ = 0 := by simp [hzero]
  have himage := (SmallEtale.map_eq_zero_iff_le_zeroOpen
    B S hS F U' (F.obj.map φ.op s) (pullback g φ) p₂).mp hzero'
  obtain ⟨y, hy⟩ : (T.map φ).base x ∈ Set.range (T.map g).base := hWr ▸ hxW
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback hpb y x hy
  exact himage ⟨z, hz₂⟩

private theorem supportSection_restrict_subset (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U U' : SmallEtale B S hS) (φ : U' ⟶ U)
    (s : F.obj.obj (op U)) :
    SmallEtale.supportSection B S hS F U'
        (F.obj.map φ.op s) ⊆
      Set.preimage ((SmallEtale.toScheme B S hS).map φ).base
        (SmallEtale.supportSection B S hS F U s) := by
  classical
  let T := SmallEtale.toScheme B S hS
  let φs := T.map φ
  let Z := SmallEtale.zeroOpen B S hS F U s
  let Z' := SmallEtale.zeroOpen B S hS F U' (F.obj.map φ.op s)
  change (Z' : Set (T.obj U'))ᶜ ⊆ φs.base ⁻¹' ((Z : Set (T.obj U))ᶜ)
  intro x hx
  simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
  intro hxZ
  exact hx (mem_zeroOpen_restrict_of_map_mem B S hS F U U' φ s x hxZ)

private theorem supportSection_restrict_eq (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U U' : SmallEtale B S hS) (φ : U' ⟶ U)
    [IsOpenImmersion ((SmallEtale.toScheme B S hS).map φ)]
    (s : F.obj.obj (op U)) :
    SmallEtale.supportSection B S hS F U'
        (F.obj.map φ.op s) =
      Set.preimage ((SmallEtale.toScheme B S hS).map φ).base
        (SmallEtale.supportSection B S hS F U s) := by
  let T := SmallEtale.toScheme B S hS
  let φs := T.map φ
  let Z := SmallEtale.zeroOpen B S hS F U s
  let Z' := SmallEtale.zeroOpen B S hS F U' (F.obj.map φ.op s)
  let Q : (T.obj U').Opens := ⟨φs.base ⁻¹' (Z : Set (T.obj U)),
    Z.2.preimage φs.continuous⟩
  have hzero : Z' = Q := by
    apply le_antisymm
    · apply sSup_le
      intro W hW
      rcases hW with ⟨V, g, hg, hWr, hzero⟩
      have hzeroComp : F.obj.map (g ≫ φ).op s = 0 := by
        simpa only [op_comp, F.obj.map_comp, ConcreteCategory.comp_apply] using hzero
      have hcompOpen : IsOpenImmersion (T.map (g ≫ φ)) := by
        change IsOpenImmersion (T.map g ≫ T.map φ)
        infer_instance
      let : IsOpenImmersion (T.map (g ≫ φ)) := hcompOpen
      have himage := (SmallEtale.map_eq_zero_iff_le_zeroOpen
        B S hS F U s V (g ≫ φ)).mp hzeroComp
      intro x hx
      have hxg : x ∈ Set.range (T.map g).base := hWr ▸ hx
      change φs.base x ∈ (Z : Set (T.obj U))
      have hxcomp : φs.base x ∈ Set.range (T.map (g ≫ φ)).base := by
        rw [T.map_comp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
        exact ⟨x, hxg, rfl⟩
      exact himage hxcomp
    · intro x hx
      exact mem_zeroOpen_restrict_of_map_mem B S hS F U U' φ s x hx
  change ((Z' : Set (T.obj U'))ᶜ) =
    φs.base ⁻¹' ((Z : Set (T.obj U))ᶜ)
  rw [hzero]
  simp [Q, Set.preimage_compl]

private noncomputable def extendSupportedSection
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{v})
    (U U' : SmallEtale B X hX) (φ : U' ⟶ U) (Z' : Scheme.{u})
    (i : Z' ⟶ (SmallEtale.toScheme B X hX).obj U')
    [IsClosedImmersion i]
    [IsClosedImmersion (i ≫ (SmallEtale.toScheme B X hX).map φ)]
    (s' : {s : F.obj.obj (op U') //
      SmallEtale.supportSection B X hX F U' s ⊆ Set.range i.base}) :
    {s : F.obj.obj (op U) //
      SmallEtale.supportSection B X hX F U s ⊆
        Set.range (i ≫ (SmallEtale.toScheme B X hX).map φ).base} :=
  (SmallEtale.supportedSectionsEquiv B X hX F U U' φ Z' i).symm s'

private theorem extendSupportedSection_restrict
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{v})
    (U U' : SmallEtale B X hX) (φ : U' ⟶ U) [IsOpenImmersion
      ((SmallEtale.toScheme B X hX).map φ)] (Z' : Scheme.{u})
    (i : Z' ⟶ (SmallEtale.toScheme B X hX).obj U')
    [IsClosedImmersion i]
    [IsClosedImmersion (i ≫ (SmallEtale.toScheme B X hX).map φ)]
    (s' : {s : F.obj.obj (op U') //
      SmallEtale.supportSection B X hX F U' s ⊆ Set.range i.base}) :
    F.obj.map φ.op (extendSupportedSection B X hX F U U' φ Z' i s').val = s'.val := by
  have h : Set.preimage ((SmallEtale.toScheme B X hX).map (𝟙 U' ≫ φ)).base
      (Set.range (i ≫ (SmallEtale.toScheme B X hX).map φ).base) =
        Set.preimage ((SmallEtale.toScheme B X hX).map (𝟙 U')).base (Set.range i.base) := by
    change Set.preimage ((SmallEtale.toScheme B X hX).map φ).base
        (Set.range (((SmallEtale.toScheme B X hX).map φ).base ∘ i.base)) =
      Set.range i.base
    rw [Set.range_comp]
    exact Set.preimage_image_eq _ ((SmallEtale.toScheme B X hX).map φ).isOpenEmbedding.injective
  let t := extendSupportedSection B X hX F U U' φ Z' i s'
  have ht := SmallEtale.supportedSectionsEquiv_restrict B X hX F U U' φ Z' i
    U' (𝟙 U') h t
  dsimp [t, extendSupportedSection] at ht
  have hE := Equiv.apply_symm_apply
    (SmallEtale.supportedSectionsEquiv B X hX F U U' φ Z' i) s'
  have hEval := congrArg Subtype.val hE
  have hres :
      ((SmallEtale.supportedSectionsEquiv B X hX F U U' φ Z' i)
        ((SmallEtale.supportedSectionsEquiv B X hX F U U' φ Z' i).symm s')).val =
        F.obj.map φ.op
          ((SmallEtale.supportedSectionsEquiv B X hX F U U' φ Z' i).symm s').val := by
    simpa using ht
  calc
    F.obj.map φ.op (extendSupportedSection B X hX F U U' φ Z' i s').val =
        F.obj.map φ.op
          ((SmallEtale.supportedSectionsEquiv B X hX F U U' φ Z' i).symm s').val := rfl
    _ = ((SmallEtale.supportedSectionsEquiv B X hX F U U' φ Z' i)
        ((SmallEtale.supportedSectionsEquiv B X hX F U U' φ Z' i).symm s')).val := hres.symm
    _ = s'.val := hEval

private theorem supportSection_extendSupportedSection_eq
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{v})
    (U U' : SmallEtale B X hX) (φ : U' ⟶ U) [IsOpenImmersion
      ((SmallEtale.toScheme B X hX).map φ)] (Z' : Scheme.{u})
    (i : Z' ⟶ (SmallEtale.toScheme B X hX).obj U')
    [IsClosedImmersion i]
    [IsClosedImmersion (i ≫ (SmallEtale.toScheme B X hX).map φ)]
    (s' : {s : F.obj.obj (op U') //
      SmallEtale.supportSection B X hX F U' s ⊆ Set.range i.base}) :
    SmallEtale.supportSection B X hX F U
        (extendSupportedSection B X hX F U U' φ Z' i s').val =
      Set.image ((SmallEtale.toScheme B X hX).map φ).base
        (SmallEtale.supportSection B X hX F U' s'.val) := by
  let φs := (SmallEtale.toScheme B X hX).map φ
  let t := extendSupportedSection B X hX F U U' φ Z' i s'
  have hres := supportSection_restrict_eq B X hX F U U' φ t.val
  have hrestrict := extendSupportedSection_restrict B X hX F U U' φ Z' i s'
  have hsubset := t.property
  have hrange : SmallEtale.supportSection B X hX F U
      (extendSupportedSection B X hX F U U' φ Z' i s').val ⊆ Set.range φs.base := by
    intro y hy
    obtain ⟨z, hz⟩ := hsubset hy
    exact ⟨i.base z, hz⟩
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨x, hxy⟩ := hrange hy
    have hx : x ∈ SmallEtale.supportSection B X hX F U'
        (F.obj.map φ.op t.val) := by
      rw [hres]
      change φs.base x ∈ SmallEtale.supportSection B X hX F U t.val
      rw [← hxy] at hy
      exact hy
    rw [hrestrict] at hx
    exact ⟨x, hx, hxy⟩
  · rintro y ⟨x, hx, hxy⟩
    have hx' : x ∈ SmallEtale.supportSection B X hX F U'
        (F.obj.map φ.op t.val) := by rwa [hrestrict]
    have hxpre : x ∈ Set.preimage φs.base
        (SmallEtale.supportSection B X hX F U t.val) := by
      rwa [← hres]
    rw [← hxy]
    exact hxpre

end AlgebraicGeometry.SmallEtale

end
