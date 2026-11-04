module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Slices
public import StacksCore.Tactic.StacksAttribute

/-!
# Fibre products and final objects in pro-étale sites

The big pro-étale category, its slice over a scheme, and the small and affine
pro-étale subcategories have the fibre products indicated by schemes. The first
three also have equalizers computed in schemes. The slice and small category
have the identity of the base as final object, while the big category has
`Spec ℤ` as final object.

## Main definitions

* `AlgebraicGeometry.ProEtale.smallIdentity` is the identity of the base in the small site.
* `AlgebraicGeometry.ProEtale.specZObject` is the terminal affine scheme in the big site.

## Main results

The creation and existence instances below express fibre products and equalizers
and their agreement with schemes. The terminal-object declarations identify the
final objects.

## Implementation notes

For part (1), the big site's pullback construction is supplied by
`AlgebraicGeometry.ProEtale.BigProetaleSite.hasPullbacks` and the slice construction by the
general theory of over categories. The affine and
small subcategories require closure under pullback. Part (2) is expressed by
equalizer existence and creation for the big and small categories; the slice
uses the general over-category construction. Part (3) uses the canonical
identity object of the slice and its restriction to the small category. Part
(4) first places `Spec ℤ` in the chosen big category and then identifies it as
terminal. In arbitrary universes `ℤ` is lifted to that universe.

## References

* [Stacks Project, Tag 098M](https://stacks.math.columbia.edu/tag/098M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

/-!
### Limits supplied by general constructions

Fibre products in the big category, and connected limits and the identity object in an
arbitrary slice, are instances of constructions that exist independently of the pro-étale
situation: the size-bounded category of schemes is closed under fibre products, and the
forgetful functor of a slice creates connected limits.
-/

add_to_stacks 098M "part (1), big category: fibre products exist"
  AlgebraicGeometry.ProEtale.BigProetaleSite.hasPullbacks
add_to_stacks 098M "part (1), big category: fibre products agree with schemes"
  AlgebraicGeometry.ProEtale.BigProetaleSite.createsPullbacks
add_to_stacks 098M "parts (1) and (2), slices: limits agree with the underlying category"
  CategoryTheory.Over.createsLimitsOfShapeForgetOfIsConnected
add_to_stacks 098M "parts (1) and (2), slices: connected limits exist"
  CategoryTheory.Over.hasLimitsOfShape_of_isConnected
add_to_stacks 098M "part (3), final object of a slice"
  CategoryTheory.Over.mkIdTerminal
add_to_sga "3 I 1.3" CategoryTheory.Over.mkIdTerminal
add_to_sga "4 IV 5.11.1" "terminal object (X" CategoryTheory.Over.mkIdTerminal
add_to_ega "0 8.1.10" "more general" CategoryTheory.Over.mkIdTerminal

variable (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion of the affine objects of a category over schemes creates fibre products,
the fibre product of two affine schemes over an affine base being affine. -/
noncomputable abbrev affineCreatesPullbacks {C : Type (u + 1)} [Category.{u} C]
    [HasPullbacks C] (G : C ⥤ Scheme.{u})
    [PreservesLimitsOfShape WalkingCospan G] :
    CreatesLimitsOfShape WalkingCospan
      (ObjectProperty.ι (fun X : C ↦ IsAffine (G.obj X))) where
  CreatesLimit := fun {F} => by
    let D := F ⋙ ObjectProperty.ι (fun X : C ↦ IsAffine (G.obj X))
    let t := pullback.cone (D.map WalkingCospan.Hom.inl) (D.map WalkingCospan.Hom.inr)
    exact createsLimitFullSubcategoryInclusion' F
      ((IsLimit.postcomposeInvEquiv (diagramIsoCospan D) t).symm (limit.isLimit _)) (by
        let e := PreservesPullback.iso G (D.map WalkingCospan.Hom.inl)
          (D.map WalkingCospan.Hom.inr)
        let : IsAffine (G.obj (D.obj .left)) := (F.obj .left).property
        let : IsAffine (G.obj (D.obj .right)) := (F.obj .right).property
        let : IsAffine (G.obj (D.obj .one)) := (F.obj .one).property
        exact @IsAffine.of_isIso _ _ e.hom e.isIso_hom inferInstance)

/-- Being weakly étale after inclusion into schemes, as a property of the morphisms of the
underlying category of a big pro-étale site. -/
abbrev WeaklyEtaleInBigSite : MorphismProperty B.Scheme :=
  MorphismProperty.inverseImage @WeaklyEtale B.inclusion

/-- Weakly étale morphisms of the big category are closed under composition. -/
instance weaklyEtaleInBigSite_isStableUnderComposition :
    (WeaklyEtaleInBigSite B).IsStableUnderComposition where
  comp_mem f g hf hg := by
    let : WeaklyEtale (B.inclusion.map f) := hf
    let : WeaklyEtale (B.inclusion.map g) := hg
    change WeaklyEtale (B.inclusion.map (f ≫ g))
    rw [Functor.map_comp]
    exact inferInstance

/-- Weakly étale morphisms of the big category are stable under base change. -/
instance weaklyEtaleInBigSite_isStableUnderBaseChange :
    (WeaklyEtaleInBigSite B).IsStableUnderBaseChange where
  of_isPullback h hg := by
    change WeaklyEtale (B.inclusion.map _) at hg ⊢
    exact MorphismProperty.of_isPullback (P := @WeaklyEtale) (h.map B.inclusion) hg

/-- If a composite and its second factor are weakly étale in the big category, so is the
first factor. -/
instance weaklyEtaleInBigSite_hasOfPostcompProperty :
    (WeaklyEtaleInBigSite B).HasOfPostcompProperty (WeaklyEtaleInBigSite B) where
  of_postcomp f g hg hfg := by
    let : WeaklyEtale (B.inclusion.map g) := hg
    let : WeaklyEtale (B.inclusion.map (f ≫ g)) := hfg
    change WeaklyEtale (B.inclusion.map f ≫ B.inclusion.map g) at hfg
    exact WeaklyEtale.of_comp (B.inclusion.map f) (B.inclusion.map g)

/-- Objects of the slice over `S` with weakly étale structure morphism are closed under
fibre products. -/
theorem weaklyEtaleOver_closedUnderPullbacks :
    (WeaklyEtaleInBigSite B).overObj
      (X := (⟨S, hS⟩ : B.Scheme)).IsClosedUnderLimitsOfShape WalkingCospan :=
  CategoryTheory.Over.closedUnderLimitsOfShape_pullback
    (P := WeaklyEtaleInBigSite B) (X := (⟨S, hS⟩ : B.Scheme))

/-- The inclusion of the small pro-étale category into the big category over `S` creates
fibre products. -/
@[instance_reducible]
noncomputable def smallProetaleInclusion_createsPullbacks :
    CreatesLimitsOfShape WalkingCospan (SmallProetale.inclusion B S hS) := by
  let P := (WeaklyEtaleInBigSite B).overObj (X := (⟨S, hS⟩ : B.Scheme))
  letI : P.IsClosedUnderLimitsOfShape WalkingCospan :=
    weaklyEtaleOver_closedUnderPullbacks B S hS
  change CreatesLimitsOfShape WalkingCospan P.ι
  exact ⟨fun {F} => createsLimitFullSubcategoryInclusionOfClosed WalkingCospan P F⟩

/-- `Spec ℤ` belongs to every big pro-étale site. -/
@[stacks 098M "part (4), containment of Spec ℤ"]
theorem specZ_mem : B.Contains (Spec (.of (ULift.{u} ℤ))) := by
  show (Spec (.of (ULift.{u} ℤ))).size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff (Cardinal.mk_le_aleph0.trans_lt B.aleph0_lt_cutoff)

/-- The scheme `Spec ℤ`, regarded as an object of the big pro-étale category. -/
@[stacks 098M "part (4), final object"]
noncomputable def specZObject : B.Scheme :=
  ⟨Spec (.of (ULift.{u} ℤ)), specZ_mem B⟩

/-- `Spec ℤ` is final in the big pro-étale category. -/
@[stacks 098M "part (4), finality and agreement with schemes"]
noncomputable def specZObject_isTerminal :
    IsTerminal (specZObject B) :=
  IsTerminal.ofUniqueHom
    (fun _ => B.inclusion.preimage (AlgebraicGeometry.specULiftZIsTerminal.from _))
    fun _ _ => B.inclusion.map_injective (AlgebraicGeometry.specULiftZIsTerminal.hom_ext _ _)

/-- The identity of `S`, as an object of the small pro-étale category. -/
@[stacks 098M "part (3), small final object"]
def smallIdentity : SmallProetale B S hS :=
  ⟨Over.mk (𝟙 (⟨S, hS⟩ : B.Scheme)), by
    change WeaklyEtale (𝟙 S)
    infer_instance⟩

/-- The identity of `S` is final in the small pro-étale category. -/
@[stacks 098M "part (3), small finality"]
noncomputable def smallIdentity_isTerminal :
    IsTerminal (smallIdentity B S hS) :=
  IsTerminal.ofUniqueHom
    (fun _ => (SmallProetale.inclusion B S hS).preimage (CategoryTheory.Over.mkIdTerminal.from _))
    fun _ _ => (SmallProetale.inclusion B S hS).map_injective
      (CategoryTheory.Over.mkIdTerminal.hom_ext _ _)

/-- The small pro-étale category has fibre products computed in schemes. -/
@[stacks 098M "part (1), small category: fibre products exist"]
instance smallProetale_hasPullbacks :
    HasPullbacks (SmallProetale B S hS) := by
  change HasPullbacks (((WeaklyEtaleInBigSite B).overObj
    (X := (⟨S, hS⟩ : B.Scheme))).FullSubcategory)
  exact hasLimitsOfShape_of_closedUnderLimits WalkingCospan
    ((WeaklyEtaleInBigSite B).overObj (X := (⟨S, hS⟩ : B.Scheme)))

/-- The inclusion of the small pro-étale category creates fibre products. -/
@[stacks 098M "part (1), small category: agreement with schemes"]
noncomputable instance smallProetale_createsPullbacks :
    CreatesLimitsOfShape WalkingCospan
      (SmallProetale.toScheme B S hS) := by
  letI : CreatesLimitsOfShape WalkingCospan
      (SmallProetale.inclusion B S hS) :=
    smallProetaleInclusion_createsPullbacks B S hS
  letI : CreatesLimitsOfShape WalkingCospan
      (BigProetaleOver.toScheme B S hS) := by
    change CreatesLimitsOfShape WalkingCospan
      (Over.forget (⟨S, hS⟩ : B.Scheme) ⋙ B.inclusion)
    letI : CreatesLimitsOfShape WalkingCospan
        (Over.forget (⟨S, hS⟩ : B.Scheme)) :=
      CategoryTheory.Over.createsLimitsOfShapeForgetOfIsConnected
    infer_instance
  infer_instance

/-- The affine pro-étale category has fibre products computed in schemes. -/
@[stacks 098M "part (1), affine category: fibre products exist"]
instance bigAffineProetale_hasPullbacks :
    HasPullbacks (BigAffineProetale B S hS) := by
  let G := BigProetaleOver.toScheme B S hS
  let : CreatesLimitsOfShape WalkingCospan
      (BigAffineProetale.inclusion B S hS) := affineCreatesPullbacks G
  let : HasPullbacks (BigProetaleOver B S hS) := by infer_instance
  exact hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (BigAffineProetale.inclusion B S hS)

/-- The inclusion of the affine pro-étale category creates fibre products. -/
@[stacks 098M "part (1), affine category: agreement with schemes"]
noncomputable instance bigAffineProetale_createsPullbacks :
    CreatesLimitsOfShape WalkingCospan
      (BigAffineProetale.toScheme B S hS) := by
  let G := BigProetaleOver.toScheme B S hS
  letI : CreatesLimitsOfShape WalkingCospan
      (BigAffineProetale.inclusion B S hS) := affineCreatesPullbacks G
  letI : CreatesLimitsOfShape WalkingCospan G := by
    change CreatesLimitsOfShape WalkingCospan
      (Over.forget (⟨S, hS⟩ : B.Scheme) ⋙ B.inclusion)
    letI : CreatesLimitsOfShape WalkingCospan
        (Over.forget (⟨S, hS⟩ : B.Scheme)) :=
      CategoryTheory.Over.createsLimitsOfShapeForgetOfIsConnected
    infer_instance
  infer_instance

/-- The big pro-étale category has equalizers. -/
@[stacks 098M "part (2), big category: equalizers exist"]
instance bigProetale_hasEqualizers : HasEqualizers B.Scheme := by
  let : HasTerminal B.Scheme := (specZObject_isTerminal B).hasTerminal
  let : HasBinaryProducts B.Scheme := hasBinaryProducts_of_hasTerminal_and_pullbacks _
  exact hasEqualizers_of_hasPullbacks_and_binary_products (C := B.Scheme)

/-- The inclusion of the big pro-étale category creates equalizers. -/
@[stacks 098M "part (2), big category: agreement with schemes"]
noncomputable instance bigProetale_createsEqualizers :
    CreatesLimitsOfShape WalkingParallelPair B.inclusion := by
  letI : HasTerminal B.Scheme := (specZObject_isTerminal B).hasTerminal
  letI : PreservesLimitsOfShape (Discrete PEmpty) B.inclusion := by
    let : PreservesLimit (Functor.empty B.Scheme) B.inclusion :=
      preservesTerminal_of_iso B.inclusion
        (B.inclusion.mapIso ((specZObject_isTerminal B).uniqueUpToIso
          (terminalIsTerminal (C := B.Scheme))).symm ≪≫
          AlgebraicGeometry.specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal)
    exact preservesLimitsOfShape_pempty_of_preservesTerminal B.inclusion
  letI : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  letI : PreservesLimitsOfShape (Discrete WalkingPair) B.inclusion :=
    preservesBinaryProducts_of_preservesTerminal_and_pullbacks B.inclusion
  letI : HasBinaryProducts B.Scheme := hasBinaryProducts_of_hasTerminal_and_pullbacks B.Scheme
  letI : PreservesLimitsOfShape WalkingParallelPair B.inclusion :=
    preservesEqualizers_of_preservesPullbacks_and_binaryProducts B.inclusion
  exact ⟨fun {F} => createsLimitOfFullyFaithfulOfPreserves⟩

/-- The small pro-étale category has equalizers. -/
@[stacks 098M "part (2), small category: equalizers exist"]
instance smallProetale_hasEqualizers :
    HasEqualizers (SmallProetale B S hS) := by
  let : HasTerminal (SmallProetale B S hS) :=
    (smallIdentity_isTerminal B S hS).hasTerminal
  let : HasBinaryProducts (SmallProetale B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  exact hasEqualizers_of_hasPullbacks_and_binary_products
    (C := SmallProetale B S hS)

/-- The inclusion of the small pro-étale category creates equalizers. -/
@[stacks 098M "part (2), small category: agreement with schemes"]
noncomputable instance smallProetale_createsEqualizers :
    CreatesLimitsOfShape WalkingParallelPair
      (SmallProetale.toScheme B S hS) := by
  letI : HasTerminal (SmallProetale B S hS) :=
    (smallIdentity_isTerminal B S hS).hasTerminal
  letI : HasPullbacks (SmallProetale B S hS) := inferInstance
  letI : HasBinaryProducts (SmallProetale B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  letI : PreservesLimitsOfShape (Discrete PEmpty)
      (SmallProetale.inclusion B S hS) := by
    let X : B.Scheme := ⟨S, hS⟩
    let i := SmallProetale.inclusion B S hS
    let e₁ : i.obj (⊤_ (SmallProetale B S hS)) ≅ Over.mk (𝟙 X) :=
      i.mapIso
      ((smallIdentity_isTerminal B S hS).uniqueUpToIso terminalIsTerminal).symm
    let e₂ : Over.mk (𝟙 X) ≅ ⊤_ (Over X) :=
      (CategoryTheory.Over.mkIdTerminal).uniqueUpToIso terminalIsTerminal
    let : PreservesLimit
        (Functor.empty (SmallProetale B S hS))
        i := preservesTerminal_of_iso i (e₁ ≪≫ e₂)
    exact preservesLimitsOfShape_pempty_of_preservesTerminal i
  letI : PreservesLimitsOfShape WalkingCospan
      (SmallProetale.inclusion B S hS) := by
    let : CreatesLimitsOfShape WalkingCospan
        (SmallProetale.inclusion B S hS) :=
      smallProetaleInclusion_createsPullbacks B S hS
    infer_instance
  letI : PreservesLimitsOfShape (Discrete WalkingPair)
      (SmallProetale.inclusion B S hS) :=
    preservesBinaryProducts_of_preservesTerminal_and_pullbacks _
  letI : PreservesLimitsOfShape WalkingParallelPair
      (SmallProetale.inclusion B S hS) :=
    preservesEqualizers_of_preservesPullbacks_and_binaryProducts _
  letI : CreatesLimitsOfShape WalkingParallelPair
      (SmallProetale.inclusion B S hS) :=
    ⟨fun {F} => createsLimitOfFullyFaithfulOfPreserves⟩
  letI : CreatesLimitsOfShape WalkingParallelPair
      (BigProetaleOver.toScheme B S hS) := by
    change CreatesLimitsOfShape WalkingParallelPair
      (Over.forget (⟨S, hS⟩ : B.Scheme) ⋙ B.inclusion)
    letI : CreatesLimitsOfShape WalkingParallelPair
        (Over.forget (⟨S, hS⟩ : B.Scheme)) :=
      CategoryTheory.Over.createsLimitsOfShapeForgetOfIsConnected
    infer_instance
  infer_instance

/-- The small pro-étale category has a final object. -/
instance smallProetale_hasTerminal :
    HasTerminal (SmallProetale B S hS) :=
  (smallIdentity_isTerminal B S hS).hasTerminal

/-- The big pro-étale category has a final object. -/
instance bigProetale_hasTerminal : HasTerminal B.Scheme :=
  (specZObject_isTerminal B).hasTerminal

/-!
### Base change of covering families

A covering family pulls back along any morphism, both in the big category and in a slice of it.
-/

/-- Pulling back the pushforward of a sieve along the image of a morphism is at most the
pushforward of its pullback, for a functor preserving fibre products. -/
theorem pullback_functorPushforward_le {C D : Type*} [Category C] [Category D]
    [HasPullbacks C] (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F]
    {X Y : C} (f : Y ⟶ X) (R : Sieve X) :
    (R.functorPushforward F).pullback (F.map f) ≤ (R.pullback f).functorPushforward F := by
  intro Z t ht
  obtain ⟨V, g, k, hg, e⟩ := ht
  let h := (IsPullback.of_hasPullback g f).map F
  refine ⟨pullback g f, pullback.snd g f, h.lift k t (by simpa using e.symm), ?_, ?_⟩
  · show R (pullback.snd g f ≫ f)
    rw [← pullback.condition]
    exact R.downward_closed hg (pullback.fst g f)
  · exact (h.lift_snd _ _ _).symm

/-- A functor preserving fibre products is cover-preserving for the topology generated by a
precoverage as soon as it takes each generating covering family to a covering sieve. -/
theorem coverPreserving_of_generators {C D : Type*} [Category C] [Category D]
    [HasPullbacks C] (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F]
    (P : Precoverage C) (K : GrothendieckTopology D)
    (hgen : ∀ {X : C} {R : Presieve X}, R ∈ P X →
      (Sieve.generate R).functorPushforward F ∈ K (F.obj X)) :
    CoverPreserving P.toGrothendieck K F := by
  refine ⟨fun {X S} hS => ?_⟩
  induction hS with
  | of X R hR => exact hgen hR
  | top X => simp
  | pullback X S hS Y f ih =>
      exact K.superset_covering (pullback_functorPushforward_le F f S)
        (K.pullback_stable (F.map f) ih)
  | transitive X S R hS hR ihS ihR =>
      apply K.transitive ihS
      intro Y t ht
      obtain ⟨Z, g, k, hg, e⟩ := ht
      refine K.superset_covering ?_ (K.pullback_stable k (ihR hg))
      intro W q hq
      have hq' := (Sieve.functorPushforward_pullback_le F g R) (q ≫ k) hq
      change (R.functorPushforward F) ((q ≫ k) ≫ F.map g) at hq'
      show (R.functorPushforward F) (q ≫ t)
      rw [e]
      simpa only [Category.assoc] using hq'


/-- The square comparing the fibre product of `b : X ⟶ S` with `f : T ⟶ S` and the fibre product
of a factorization `a ≫ b : A ⟶ S` with `f` is itself a fibre product. -/
theorem baseChange_square {C : Type*} [Category C] [HasPullbacks C]
    {A X S T : C} (a : A ⟶ X) (b : X ⟶ S) (bA : A ⟶ S) (f : T ⟶ S)
    (h : a ≫ b = bA) :
    IsPullback
      (pullback.lift (pullback.fst bA f ≫ a) (pullback.snd bA f)
        (by rw [Category.assoc, h]; exact pullback.condition))
      (pullback.fst bA f) (pullback.fst b f) a := by
  refine ⟨⟨pullback.lift_fst _ _ _⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    refine pullback.lift c.snd (c.fst ≫ pullback.snd b f) ?_
    calc
      c.snd ≫ bA = c.snd ≫ a ≫ b := by rw [← h]
      _ = c.fst ≫ pullback.fst b f ≫ b := by
        simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ b) c.condition.symm
      _ = c.fst ≫ pullback.snd b f ≫ f := by rw [pullback.condition]
    all_goals simp only [Category.assoc]
  · intro c
    refine pullback.hom_ext ?_ ?_
    · simpa only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst] using
        c.condition.symm
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  · intro c
    exact pullback.lift_fst _ _ _
  · intro c m hm₁ hm₂
    refine pullback.hom_ext ?_ ?_
    · simpa only [Category.assoc, pullback.lift_fst] using hm₂
    · simpa only [Category.assoc, pullback.lift_snd] using
        congrArg (fun k ↦ k ≫ pullback.snd b f) hm₁

/-- A family of fibre products of a chosen pro-étale covering family is again one. -/
theorem isProetaleCovering_of_isPullback
    {X Y : B.Scheme} (E : PreZeroHypercover.{u + 1} X)
    (hE : B.IsProetaleCovering ⟨X, E⟩) (g : Y ⟶ X)
    (P : E.I₀ → B.Scheme) (p₁ : ∀ i, P i ⟶ Y) (p₂ : ∀ i, P i ⟶ E.X i)
    (h : ∀ i, IsPullback (p₁ i) (p₂ i) g (E.f i)) :
    B.IsProetaleCovering ⟨Y, ⟨E.I₀, P, p₁⟩⟩ := by
  rw [B.isProetaleCovering_iff] at hE ⊢
  exact Precoverage.mem_coverings_of_isPullback
    (f := fun i ↦ B.inclusion.map (E.f i)) (hR := hE) (g := B.inclusion.map g)
    (p₁ := fun i ↦ B.inclusion.map (p₁ i)) (p₂ := fun i ↦ B.inclusion.map (p₂ i))
    (fun i ↦ (h i).map B.inclusion)

/-- A chosen pro-étale covering family of an object of a slice stays one after base change along
a morphism of the base. -/
theorem isProetaleCovering_overPullback {S T : B.Scheme} (f : T ⟶ S) {X : Over S}
    (E : PreZeroHypercover.{u + 1} X)
    (hE : B.IsProetaleCovering ⟨(Over.forget S).obj X, E.map (Over.forget S)⟩) :
    B.IsProetaleCovering ⟨(Over.forget T).obj ((Over.pullback f).obj X),
      (E.map (Over.pullback f)).map (Over.forget T)⟩ := by
  refine isProetaleCovering_of_isPullback B (E.map (Over.forget S)) hE
    (pullback.fst X.hom f) (fun i ↦ ((Over.pullback f).obj (E.X i)).left)
    (fun i ↦ ((Over.pullback f).map (E.f i)).left)
    (fun i ↦ pullback.fst (E.X i).hom f) (fun i ↦ ?_)
  show IsPullback
    (pullback.lift (pullback.fst (E.X i).hom f ≫ (E.f i).left)
      (pullback.snd (E.X i).hom f) _)
    (pullback.fst (E.X i).hom f) (pullback.fst X.hom f) (E.f i).left
  exact baseChange_square (E.f i).left X.hom (E.X i).hom f (Over.w (E.f i))

end AlgebraicGeometry.ProEtale
