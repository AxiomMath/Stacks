module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerre.FiniteTypeLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover

/-!
# Stratified étale sheaves and restriction to an open subscheme

The two constructibility predicates of Tag 03RW have the same shape: on every affine open of the
ambient scheme there is a finite partition by constructible locally closed subschemes on each of
which the inverse image of the sheaf satisfies a condition — finite local constancy for sheaves of
sets and of abelian groups, finite-type local constancy for sheaves of modules. This file isolates
that shape as `AlgebraicGeometry.IsStratifiedSheaf`, a predicate parametrised by the condition on
the strata, and proves the one statement that holds for every condition closed under isomorphism:
being a stratified sheaf is inherited by the inverse image along an open immersion.

The point of the abstraction is that the condition on a stratum is tested on the stratum's own
small étale site, so restricting the ambient scheme changes nothing about it; the work is entirely
in moving a partition of `f ''ᵁ V` down to a partition of `V`, which is independent of the
coefficient category. That gives the "restriction" half of Tag 095F for sets, abelian groups and
modules at once.

## Main definitions

* `AlgebraicGeometry.IsStratifiedSheaf` — on every affine open there is a constructible
  stratification on each stratum of which the inverse image satisfies a given condition.

## Main results

* `AlgebraicGeometry.isStratifiedSheaf_pullback_of_isOpenImmersion` — a stratified sheaf stays
  stratified after inverse image along an open immersion.
* `AlgebraicGeometry.isConstructibleFiniteSheaf_pullback_of_isOpenImmersion` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_pullback_of_isOpenImmersion` — the restriction of
  a constructible sheaf to an open subscheme is constructible.

## Implementation notes

The strata of the transported partition are the *same* objects of the big étale site as those of
the original; only their structure morphism changes, from the composite with the open immersion to
the lift along it supplied by `AlgebraicGeometry.IsOpenImmersion.lift`. This keeps the condition on
the strata literally unchanged up to the composition comparison
`AlgebraicGeometry.smallEtaleSheafPullbackCompIso` for inverse image, which is where the hypothesis
that the condition is closed under isomorphism is used.

**No `@[stacks 095F]` attribute appears in this file.** Tag 095F is an equivalence, and only its
easy direction — restriction along an open immersion — is proved here; the converse is Zariski
descent of constructibility, which rests on Tag 095E. Tagging this half would report the whole tag
as formalized.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 095F](https://stacks.math.columbia.edu/tag/095F)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w v t r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- The morphism of the big étale site corresponding to the inclusion of an open subscheme is an
open immersion. -/
private theorem isOpenImmersion_map_preimage_ι {X : B.Scheme} (V : X.obj.Opens)
    (hV : B.Contains V.toScheme) :
    IsOpenImmersion (B.inclusion.map (B.inclusion.preimage V.ι : B.obj V.toScheme hV ⟶ X)) := by
  rw [B.inclusion.map_preimage]
  infer_instance

namespace ConstructibleStratification

section OpenImmersion

variable {B} {X Y : B.Scheme} (f : Y ⟶ X) [IsOpenImmersion (B.inclusion.map f)]
  {V : Y.obj.Opens} (s : ConstructibleStratification B X (B.inclusion.map f ''ᵁ V))

/-- The lift through the open immersion `f` of the inclusion of the `i`-th stratum of a
stratification of `f ''ᵁ V`. -/
private def liftInclusion (i : Fin s.n) : s.piece i ⟶ Y :=
  B.inclusion.preimage (IsOpenImmersion.lift (B.inclusion.map f)
    (B.inclusion.map (s.inclusion i)) ((s.contained i).trans
      (show SetLike.coe (B.inclusion.map f ''ᵁ V) ⊆
        Set.range (B.inclusion.map f).base from Set.image_subset_range _ _)))

private theorem map_liftInclusion_comp (i : Fin s.n) :
    B.inclusion.map (s.liftInclusion f i) ≫ B.inclusion.map f =
      B.inclusion.map (s.inclusion i) := by
  rw [liftInclusion, Functor.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

private theorem liftInclusion_comp (i : Fin s.n) : s.liftInclusion f i ≫ f = s.inclusion i :=
  B.inclusion.map_injective (s.map_liftInclusion_comp f i)

private theorem liftInclusion_apply (i : Fin s.n) (z : (s.piece i).obj) :
    (B.inclusion.map f).base ((B.inclusion.map (s.liftInclusion f i)).base z) =
      (B.inclusion.map (s.inclusion i)).base z := by
  simpa only [Scheme.Hom.comp_apply] using
    congrArg (fun q => q z) (s.map_liftInclusion_comp f i)

private theorem range_liftInclusion_subset (i : Fin s.n) :
    Set.range (B.inclusion.map (s.liftInclusion f i)).base ⊆ (V : Set Y.obj) := by
  rintro y ⟨z, rfl⟩
  obtain ⟨y, hy, heq⟩ : (B.inclusion.map (s.inclusion i)).base z ∈
      SetLike.coe (B.inclusion.map f ''ᵁ V) := s.contained i ⟨z, rfl⟩
  have hzy : (B.inclusion.map (s.liftInclusion f i)).base z = y :=
    (B.inclusion.map f).isOpenEmbedding.injective ((s.liftInclusion_apply f i z).trans heq.symm)
  exact hzy ▸ hy

/-- A stratification of the image `f ''ᵁ V` of an open under an open immersion `f`, lifted
stratum by stratum to a stratification of `V`. -/
private def ofOpenImmersion : ConstructibleStratification B Y V where
  n := s.n
  piece := s.piece
  inclusion := s.liftInclusion f
  isImmersion i :=
    (IsImmersion.comp_iff (B.inclusion.map (s.liftInclusion f i)) (B.inclusion.map f)).mp (by
      rw [s.map_liftInclusion_comp f i]
      exact s.isImmersion i)
  contained := s.range_liftInclusion_subset f
  constructible i := by
    let e : V ≃ₜ (B.inclusion.map f).base '' (V : Set Y.obj) :=
      (B.inclusion.map f).isOpenEmbedding.isEmbedding.homeomorphImage (V : Set Y.obj)
    have heq : V.ι.base ⁻¹' Set.range (B.inclusion.map (s.liftInclusion f i)).base =
        e ⁻¹' ((B.inclusion.map f ''ᵁ V).ι.base ⁻¹'
          Set.range (B.inclusion.map (s.inclusion i)).base) := by
      ext y
      change V.ι.base y ∈ Set.range (B.inclusion.map (s.liftInclusion f i)).base ↔
        (B.inclusion.map f ''ᵁ V).ι.base (e y) ∈
          Set.range (B.inclusion.map (s.inclusion i)).base
      exact ⟨fun ⟨z, hz⟩ => ⟨z, ((s.liftInclusion_apply f i z).symm.trans
          (congrArg (B.inclusion.map f).base hz.symm).symm).trans rfl⟩,
        fun ⟨z, hz⟩ => ⟨z, (B.inclusion.map f).isOpenEmbedding.injective
          (((s.liftInclusion_apply f i z).trans hz).trans rfl)⟩⟩
    rw [heq]
    exact (s.constructible i).preimage_of_isOpenEmbedding e.isOpenEmbedding
  pairwise_disjoint i j hij := by
    refine Set.disjoint_left.mpr fun y hyi hyj => ?_
    obtain ⟨x, hx⟩ := hyi
    obtain ⟨x', hx'⟩ := hyj
    exact Set.disjoint_left.mp (s.pairwise_disjoint i j hij)
      ⟨x, hx ▸ (s.liftInclusion_apply f i x).symm⟩ ⟨x', hx' ▸ (s.liftInclusion_apply f j x').symm⟩
  covers := by
    refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
    · have hyW : (B.inclusion.map f).base y ∈
          SetLike.coe (B.inclusion.map f ''ᵁ V) := ⟨y, hy, rfl⟩
      rw [s.covers] at hyW
      obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp hyW
      exact Set.mem_iUnion.mpr
        ⟨i, z, (B.inclusion.map f).isOpenEmbedding.injective
          ((s.liftInclusion_apply f i z).trans hz)⟩
    · obtain ⟨i, z, rfl⟩ := Set.mem_iUnion.mp hy
      exact s.range_liftInclusion_subset f i ⟨z, rfl⟩

end OpenImmersion

section Opens

variable {B} {X : B.Scheme} (V : X.obj.Opens) (hV : B.Contains V.toScheme)
  (s : ConstructibleStratification B (B.obj V.toScheme hV) ⊤)

/-- A stratification of the whole of an open subscheme `V` of `X`, regarded as a stratification
of `V` as an open of `X`. -/
private def ofOpens : ConstructibleStratification B X V :=
  let Z : B.Scheme := B.obj V.toScheme hV
  let v : Z ⟶ X := B.inclusion.preimage V.ι
  have hvmap : B.inclusion.map v = V.ι := B.inclusion.map_preimage _
  have hv := isOpenImmersion_map_preimage_ι B V hV
  have hven : Topology.IsOpenEmbedding (B.inclusion.map v).base := by
    rw [hvmap]
    exact V.isOpenEmbedding
  have hrangev : Set.range (B.inclusion.map v).base = (V : Set X.obj) := by
    rw [hvmap]
    exact V.range_ι
  have hincl (i : Fin s.n) (y : (s.piece i).obj) :
      (B.inclusion.map (s.inclusion i ≫ v)).base y =
        (B.inclusion.map v).base ((B.inclusion.map (s.inclusion i)).base y) := rfl
  have hpre (i : Fin s.n) :
      (V.ι.base ⁻¹' Set.range (B.inclusion.map (s.inclusion i ≫ v)).base) =
        Set.range (B.inclusion.map (s.inclusion i)).base := by
    ext z
    refine ⟨fun ⟨y, hy⟩ => ⟨y, hven.injective ?_⟩, fun ⟨y, hy⟩ => ⟨y, ?_⟩⟩
    · rw [← hincl i y, hvmap]
      exact hy
    · rw [hincl i y, hy, hvmap]
  let eTop : (⊤ : Z.obj.Opens).toScheme ≃ₜ Z.obj :=
    (Homeomorph.setCongr (show ((⊤ : Z.obj.Opens) : Set Z.obj) = Set.univ by ext z; simp)).trans
      (Homeomorph.Set.univ Z.obj)
  have htop (i : Fin s.n) :
      eTop.symm ⁻¹' ((⊤ : Z.obj.Opens).ι.base ⁻¹'
          Set.range (B.inclusion.map (s.inclusion i)).base) =
        Set.range (B.inclusion.map (s.inclusion i)).base := rfl
  { n := s.n
    piece := s.piece
    inclusion := fun i => s.inclusion i ≫ v
    isImmersion := fun i => by
      have h₁ : IsImmersion (B.inclusion.map (s.inclusion i)) := s.isImmersion i
      have h₂ : IsImmersion (B.inclusion.map v) := by have := hv; infer_instance
      simpa only [Functor.map_comp] using
        (inferInstance : IsImmersion (B.inclusion.map (s.inclusion i) ≫ B.inclusion.map v))
    contained := by
      rintro i x ⟨y, rfl⟩
      rw [← hrangev, hincl i y]
      exact ⟨_, rfl⟩
    constructible := by
      intro i
      rw [hpre i, ← htop i]
      exact (s.constructible i).preimage_of_isOpenEmbedding eTop.symm.isOpenEmbedding
    pairwise_disjoint := by
      intro i i' hii'
      refine Set.disjoint_left.mpr fun x hxi hxi' => ?_
      obtain ⟨zi, hzi⟩ := hxi
      obtain ⟨zi', hzi'⟩ := hxi'
      have := hven.injective
        (((hincl i zi).symm.trans hzi).trans (hzi'.symm.trans (hincl i' zi')))
      exact Set.disjoint_left.mp (s.pairwise_disjoint i i' hii') ⟨zi, rfl⟩ ⟨zi', this.symm⟩
    covers := by
      refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨z, hz⟩ : x ∈ Set.range (B.inclusion.map v).base := by
          rw [hrangev]
          exact hx
        have hzU : z ∈ ⋃ i, Set.range (B.inclusion.map (s.inclusion i)).base := by
          rw [← s.covers]
          exact Set.mem_univ z
        obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hzU
        exact Set.mem_iUnion.mpr ⟨i, y, (hincl i y).trans (by rw [hy]; exact hz)⟩
      · obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
        rw [← hrangev, hincl i y]
        exact ⟨_, rfl⟩ }

end Opens

end ConstructibleStratification

section General

variable {D : Type w} [Category.{v} D]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- `IsStratifiedSheaf B X P F` says that on every affine open of `X` there is a finite partition
by constructible locally closed subschemes on each stratum of which the inverse image of `F`
satisfies `P`.

Both parts of Tag 03RW are instances of this: `AlgebraicGeometry.IsConstructibleFiniteSheaf` takes
`P` to be finite local constancy, and `AlgebraicGeometry.IsConstructibleModuleSheaf` takes it to be
finite-type local constancy. -/
public def IsStratifiedSheaf (X : B.Scheme)
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D) : Prop :=
  ∀ V : X.obj.affineOpens, ∃ s : ConstructibleStratification B X V.1,
    ∀ i, P (s.piece i)
      (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback D
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj F)

/-- **Stacks 095F, the easy direction.** Being a stratified sheaf passes to the inverse image
along an open immersion, for any condition on the strata that is closed under isomorphism.

An affine open `V` of the source is carried by the open immersion to an affine open `f ''ᵁ V` of
the target; a partition of the latter has all its strata inside the image, so each stratum lifts
uniquely through the open immersion and the lifts partition `V`. -/
public theorem isStratifiedSheaf_pullback_of_isOpenImmersion {X Y : B.Scheme} (f : Y ⟶ X)
    (hf : IsOpenImmersion (B.inclusion.map f))
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D)
    (hF : IsStratifiedSheaf B X P F) :
    IsStratifiedSheaf B Y P
      (((smallEtaleBaseChange B f).sheafPullback D
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Y.obj Y.property)).obj F) := by
  intro V
  have : IsOpenImmersion (B.inclusion.map f) := hf
  obtain ⟨s, hs⟩ := hF ⟨B.inclusion.map f ''ᵁ V.1, V.2.image_of_isOpenImmersion _⟩
  refine ⟨s.ofOpenImmersion f (V := V.1), fun i => hPIso (s.piece i)
    ((smallEtaleSheafPullbackCompIso B (s.piece i) Y X
      (s.liftInclusion f i) f D).app F).symm ?_⟩
  exact s.liftInclusion_comp f i ▸ hs i

/-- Being a stratified sheaf transfers along an isomorphism of sheaves, provided the condition on
the strata does. -/
public theorem isStratifiedSheaf_congr (X : B.Scheme)
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) D} (e : F ≅ G)
    (hF : IsStratifiedSheaf B X P F) : IsStratifiedSheaf B X P G :=
  fun V => (hF V).imp fun s hs i => hPIso (s.piece i)
    (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback D
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).mapIso e) (hs i)

/-- Inverse image along a composite, applied to a sheaf: the comparison supplied by
`AlgebraicGeometry.smallEtaleSheafPullbackCompIso`, in the direction used below. -/
private def pullbackCompObjIso {S T W : B.Scheme} (f : T ⟶ S) (g : W ⟶ T)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) D) :
    ((smallEtaleBaseChange B (g ≫ f)).sheafPullback D
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B W.obj W.property)).obj F ≅
      ((smallEtaleBaseChange B g).sheafPullback D
        (SmallEtale.topology B T.obj T.property)
        (SmallEtale.topology B W.obj W.property)).obj
        (((smallEtaleBaseChange B f).sheafPullback D
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).obj F) :=
  ((smallEtaleSheafPullbackCompIso B W T S g f D).app F).symm

/-- If the composite of open immersions `g ≫ v` lands inside the open immersion `j`, a sheaf whose
inverse image along `j` is stratified has stratified inverse image along `g ≫ v`. -/
private theorem isStratifiedSheaf_pullback_of_range_subset {X Y Z U : B.Scheme}
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D) (v : Z ⟶ X) (g : Y ⟶ Z) (j : U ⟶ X)
    [IsOpenImmersion (B.inclusion.map v)] [IsOpenImmersion (B.inclusion.map g)]
    [IsOpenImmersion (B.inclusion.map j)]
    (hsub : Set.range (B.inclusion.map (g ≫ v)).base ⊆ Set.range (B.inclusion.map j).base)
    (hF : IsStratifiedSheaf B U P
      (((smallEtaleBaseChange B j).sheafPullback D
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B U.obj U.property)).obj F)) :
    IsStratifiedSheaf B Y P
      (((smallEtaleBaseChange B g).sheafPullback D
        (SmallEtale.topology B Z.obj Z.property)
        (SmallEtale.topology B Y.obj Y.property)).obj
        (((smallEtaleBaseChange B v).sheafPullback D
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B Z.obj Z.property)).obj F)) := by
  let q : Y ⟶ U :=
    B.inclusion.preimage (IsOpenImmersion.lift (B.inclusion.map j) (B.inclusion.map (g ≫ v)) hsub)
  have hqcomp : B.inclusion.map q ≫ B.inclusion.map j = B.inclusion.map (g ≫ v) := by
    rw [B.inclusion.map_preimage]
    exact IsOpenImmersion.lift_fac _ _ hsub
  have hqopen : IsOpenImmersion (B.inclusion.map q) := by
    have : IsOpenImmersion (B.inclusion.map q ≫ B.inclusion.map j) := by
      rw [hqcomp, Functor.map_comp]
      infer_instance
    exact IsOpenImmersion.of_comp _ (B.inclusion.map j)
  have hqj : q ≫ j = g ≫ v := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, hqcomp]
  refine isStratifiedSheaf_congr B Y P hPIso ?_
    (isStratifiedSheaf_pullback_of_isOpenImmersion B q hqopen P hPIso _ hF)
  refine (pullbackCompObjIso B j q F).symm ≪≫ eqToIso ?_ ≪≫ pullbackCompObjIso B v g F
  let pullObj : (Y ⟶ X) → Sheaf (SmallEtale.topology B Y.obj Y.property) D :=
    fun h => by
      have := smallEtaleBaseChange_isContinuous B h
      exact ((smallEtaleBaseChange B h).sheafPullback D
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Y.obj Y.property)).obj F
  simpa only [pullObj] using congrArg pullObj hqj

/-- Over an open immersion `v : Z ⟶ X`, the affine opens of `Z` lying over a member of an open
cover of `X` cover `Z`, and the inverse image of a sheaf that is stratified on each member of the
cover is stratified on each of them. -/
private theorem exists_affine_cover_isStratifiedSheaf_pullback {X Z : B.Scheme}
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D) (v : Z ⟶ X)
    [IsOpenImmersion (B.inclusion.map v)]
    {I : Type*} (U : I → B.Scheme) (j : ∀ k, U k ⟶ X)
    (hj : ∀ k, IsOpenImmersion (B.inclusion.map (j k)))
    (hcover : Set.univ = ⋃ k, Set.range (B.inclusion.map (j k)).base)
    (hlocal : ∀ k, IsStratifiedSheaf B (U k) P
      (((smallEtaleBaseChange B (j k)).sheafPullback D
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (U k).obj (U k).property)).obj F)) :
    ∃ (J : Type (u + 1)) (Y : J → B.Scheme) (g : ∀ a, Y a ⟶ Z),
      (∀ a, IsOpenImmersion (B.inclusion.map (g a))) ∧
      (Set.univ = ⋃ a, Set.range (B.inclusion.map (g a)).base) ∧
      ∀ a, IsStratifiedSheaf B (Y a) P
        (((smallEtaleBaseChange B (g a)).sheafPullback D
          (SmallEtale.topology B Z.obj Z.property)
          (SmallEtale.topology B (Y a).obj (Y a).property)).obj
          (((smallEtaleBaseChange B v).sheafPullback D
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B Z.obj Z.property)).obj F)) := by
  let O (k : I) : Z.obj.Opens := (B.inclusion.map v) ⁻¹ᵁ (B.inclusion.map (j k)).opensRange
  let Jdom := ULift.{u + 1} {W : Z.obj.affineOpens // ∃ k : I, (W : Z.obj.Opens) ≤ O k}
  let W (a : Jdom) : Z.obj.affineOpens := a.down.1
  let Y (a : Jdom) : B.Scheme :=
    ⟨(W a).1.toScheme, lt_of_le_of_lt (Scheme.size_coe_opens_le Z.obj (W a).1) Z.property⟩
  let g (a : Jdom) : Y a ⟶ Z := B.inclusion.preimage (W a).1.ι
  have hgmap (a : Jdom) : B.inclusion.map (g a) = (W a).1.ι := B.inclusion.map_preimage _
  have hg (a : Jdom) : IsOpenImmersion (B.inclusion.map (g a)) := by
    rw [hgmap]
    infer_instance
  refine ⟨Jdom, Y, g, hg, Set.Subset.antisymm (fun z _ => ?_) (fun z _ => Set.mem_univ z),
    fun a => ?_⟩
  · have hx : (B.inclusion.map v).base z ∈ ⋃ k, Set.range (B.inclusion.map (j k)).base := by
      rw [← hcover]
      exact Set.mem_univ _
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    obtain ⟨S, ⟨Wz, hWz, hEq⟩, hzw, hWsub⟩ :=
      Z.obj.isBasis_affineOpens.exists_subset_of_mem_open (a := z) hk (O k).2
    rw [← hEq] at hzw hWsub
    exact Set.mem_iUnion.mpr
      ⟨ULift.up ⟨⟨Wz, hWz⟩, ⟨k, hWsub⟩⟩, ⟨⟨z, hzw⟩, by rw [hgmap]; rfl⟩⟩
  · obtain ⟨k, hWsub⟩ := a.down.2
    have := hj k
    have := hg a
    refine isStratifiedSheaf_pullback_of_range_subset B P hPIso F v (g a) (j k) ?_ (hlocal k)
    rintro x ⟨y, rfl⟩
    have hyW : (B.inclusion.map (g a)).base y ∈ ((W a).1 : Set Z.obj) := by
      rw [hgmap]
      exact y.2
    have hyO : (B.inclusion.map v).base ((B.inclusion.map (g a)).base y) ∈
        Set.range (B.inclusion.map (j k)).base := hWsub hyW
    exact hyO

/-- **Zariski descent for stratified sheaves, modulo Tag 095E.** If a sheaf on `X` restricts to a
stratified sheaf on each member of an open cover of `X`, then it is a stratified sheaf, *provided*
the condition `P` on the strata is closed under isomorphism and satisfies the two assertions of
Tag 095E on quasi-compact quasi-separated schemes: being a stratified sheaf is Zariski local
(`hLocalCriterion`), and on such a scheme a stratified sheaf admits a single stratification of the
whole scheme (`hStratification`).

The affine opens of `X` are quasi-compact and quasi-separated, so the two inputs apply to them;
the proof covers such an affine open by the affine opens it has inside the members of the given
cover, transports the local hypothesis there by
`AlgebraicGeometry.isStratifiedSheaf_pullback_of_isOpenImmersion`, and then pushes the resulting
global stratification of the affine open back up to `X`.

This is the whole of Tag 095F except its two inputs, and it is also the Zariski-descent step in the
proof of Tag 09YR. -/
public theorem isStratifiedSheaf_of_openCover (X : B.Scheme)
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (hLocalCriterion : ∀ (Z : B.Scheme) [CompactSpace Z.obj] [QuasiSeparatedSpace Z.obj]
      (G : Sheaf (SmallEtale.topology B Z.obj Z.property) D),
      IsStratifiedSheaf B Z P G ↔
        ∃ (J : Type (u + 1)) (Y : J → B.Scheme) (g : ∀ j, Y j ⟶ Z),
          (∀ j, IsOpenImmersion (B.inclusion.map (g j))) ∧
          (Set.univ = ⋃ j, Set.range (B.inclusion.map (g j)).base) ∧
          ∀ j, IsStratifiedSheaf B (Y j) P
            (((smallEtaleBaseChange B (g j)).sheafPullback D
              (SmallEtale.topology B Z.obj Z.property)
              (SmallEtale.topology B (Y j).obj (Y j).property)).obj G))
    (hStratification : ∀ (Z : B.Scheme) [CompactSpace Z.obj] [QuasiSeparatedSpace Z.obj]
      (G : Sheaf (SmallEtale.topology B Z.obj Z.property) D),
      IsStratifiedSheaf B Z P G →
        ∃ s : ConstructibleStratification B Z ⊤,
          ∀ i, P (s.piece i)
            (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback D
              (SmallEtale.topology B Z.obj Z.property)
              (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj G))
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D)
    {I : Type*} (U : I → B.Scheme) (j : ∀ k, U k ⟶ X)
    (hj : ∀ k, IsOpenImmersion (B.inclusion.map (j k)))
    (hcover : Set.univ = ⋃ k, Set.range (B.inclusion.map (j k)).base)
    (hlocal : ∀ k, IsStratifiedSheaf B (U k) P
      (((smallEtaleBaseChange B (j k)).sheafPullback D
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (U k).obj (U k).property)).obj F)) :
    IsStratifiedSheaf B X P F := by
  intro V
  have hV : B.Contains V.1.toScheme :=
    lt_of_le_of_lt (Scheme.size_coe_opens_le X.obj V.1) X.property
  let Z : B.Scheme := B.obj V.1.toScheme hV
  let v : Z ⟶ X := B.inclusion.preimage V.1.ι
  have hv := isOpenImmersion_map_preimage_ι B V.1 hV
  obtain ⟨s, hs⟩ := hStratification Z _ ((hLocalCriterion Z _).mpr
    (exists_affine_cover_isStratifiedSheaf_pullback B P hPIso F v U j hj hcover hlocal))
  exact ⟨s.ofOpens V.1 hV, fun i =>
    hPIso (s.piece i) (pullbackCompObjIso B v (s.inclusion i) F).symm (hs i)⟩

end General

section Finite

variable {D : Type w} [Category.{v} D] {FD : D → D → Type*} {CD : D → Type t}
  [∀ A A', FunLike (FD A A') (CD A) (CD A')] [ConcreteCategory.{t} D FD]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) D]

/-- Constructibility of a sheaf of sets or of abelian groups is `IsStratifiedSheaf` for the
condition of being finite locally constant. -/
public theorem isConstructibleFiniteSheaf_iff_isStratifiedSheaf (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D) :
    IsConstructibleFiniteSheaf B X F ↔
      IsStratifiedSheaf B X
        (fun T G => Stacks.ConstantSheaf.IsFiniteLocallyConstant
          (SmallEtale.topology B T.obj T.property) G) F :=
  Iff.rfl

/-- **Stacks 095F, the easy direction, for sets and abelian groups.** The restriction of a
constructible sheaf of sets, or of abelian groups, to an open subscheme is constructible. -/
public theorem isConstructibleFiniteSheaf_pullback_of_isOpenImmersion {X Y : B.Scheme} (f : Y ⟶ X)
    (hf : IsOpenImmersion (B.inclusion.map f))
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D)
    (hF : IsConstructibleFiniteSheaf B X F) :
    IsConstructibleFiniteSheaf B Y
      (((smallEtaleBaseChange B f).sheafPullback D
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Y.obj Y.property)).obj F) := by
  refine isStratifiedSheaf_pullback_of_isOpenImmersion B f hf
    (fun T G => Stacks.ConstantSheaf.IsFiniteLocallyConstant
      (SmallEtale.topology B T.obj T.property) G) ?_ F hF
  intro T G H e h
  exact Stacks.ConstantSheaf.isFiniteLocallyConstant_congr
    (SmallEtale.topology B T.obj T.property) e (hF := h)

end Finite

section Modules

variable (R : Type r) [CommRing R] [IsNoetherianRing R]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} R)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} R)]

omit [IsNoetherianRing R] in
/-- Constructibility of a sheaf of modules is `IsStratifiedSheaf` for the condition of being
locally constant of finite type. -/
public theorem isConstructibleModuleSheaf_iff_isStratifiedSheaf (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R)) :
    IsConstructibleModuleSheaf B X R F ↔
      IsStratifiedSheaf B X
        (fun T G => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
          (SmallEtale.topology B T.obj T.property) G) F :=
  Iff.rfl

omit [IsNoetherianRing R] in
/-- **Stacks 095F, the easy direction, for modules.** The restriction of a constructible sheaf of
modules over a Noetherian ring to an open subscheme is constructible. -/
public theorem isConstructibleModuleSheaf_pullback_of_isOpenImmersion {X Y : B.Scheme} (f : Y ⟶ X)
    (hf : IsOpenImmersion (B.inclusion.map f))
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R))
    (hF : IsConstructibleModuleSheaf B X R F) :
    IsConstructibleModuleSheaf B Y R
      (((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{w} R)
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Y.obj Y.property)).obj F) := by
  refine isStratifiedSheaf_pullback_of_isOpenImmersion B f hf
    (fun T G => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
      (SmallEtale.topology B T.obj T.property) G) ?_ F hF
  intro T G H e h
  exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr
    (SmallEtale.topology B T.obj T.property) R e h

end Modules

end AlgebraicGeometry

end
