module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZariskiLocal
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Inverse image of a constructible étale sheaf

Let `f : X ⟶ Y` be a morphism of schemes. The inverse image `f⁻¹F` of a constructible sheaf `F` on
the small étale site of `Y` is constructible on the small étale site of `X`, for sheaves of sets,
of abelian groups, and of modules over a Noetherian ring. This is Tag 095G.

The argument is the one of the source, carried out for an arbitrary condition `P` on the strata
which is closed under isomorphism of sheaves and stable under inverse image. The target is covered
by its affine opens, so the source is covered by the fibre products of those affine opens with it,
and being a stratified sheaf is Zariski local; this reduces the statement to an affine target. An
affine scheme is quasi-compact and quasi-separated, so Tag 095E supplies **one** constructible
stratification of the whole target on each stratum of which `F` satisfies `P`. That stratification
is then pulled back: the stratum of `X` over the `i`-th stratum `Z i` of `Y` is the fibre product
`Z i ×_Y X`, which is immersed in `X` with image the preimage of the image of `Z i`, hence
constructible, and the inverse image of `f⁻¹F` to it agrees with the inverse image to `Z i ×_Y X`
of the restriction of `F` to `Z i`, so `P` follows from stability under inverse image.

## Main results

* `AlgebraicGeometry.isStratifiedSheaf_pullback` — Tag 095G for an arbitrary condition on the
  strata.
* `AlgebraicGeometry.isConstructibleFiniteSheaf_pullback` — **Tag 095G for sheaves of sets and of
  abelian groups.**
* `AlgebraicGeometry.isConstructibleModuleSheaf_pullback` — **Tag 095G for sheaves of modules over
  a Noetherian ring.**

## Implementation notes

The strata of the pulled back partition are fibre products *over the target*, not reduced induced
subschemes of the source on the preimages of the strata. This is what makes the condition on the
strata reach them: it is a condition on sheaves over a stratum, and it is carried to the fibre
product by inverse image along the first projection.

A stratification of a *single* open subscheme of the source is produced directly for every affine
open, rather than one of the whole source, since the source is not assumed quasi-compact.

## References

* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
* [Stacks Project, Tag 095E](https://stacks.math.columbia.edu/tag/095E)
* [Stacks Project, Tag 095F](https://stacks.math.columbia.edu/tag/095F)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u w v t r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-! ### Open subschemes and fibre products in the big étale site -/

/-- An open subscheme of an object of the big étale site, again an object of that site. -/
private abbrev openObj (X : B.Scheme) (U : X.obj.Opens) : B.Scheme :=
  B.obj U.toScheme (lt_of_le_of_lt (Scheme.size_coe_opens_le X.obj U) X.property)

/-- The open immersion of an open subscheme of an object of the big étale site. -/
private abbrev openHom (X : B.Scheme) (U : X.obj.Opens) : openObj B X U ⟶ X :=
  ObjectProperty.homMk U.ι

private theorem map_openHom (X : B.Scheme) (U : X.obj.Opens) :
    B.inclusion.map (openHom B X U) = U.ι := rfl

private instance isOpenImmersion_map_openHom (X : B.Scheme) (U : X.obj.Opens) :
    IsOpenImmersion (B.inclusion.map (openHom B X U)) :=
  inferInstanceAs (IsOpenImmersion U.ι)

private theorem range_map_openHom (X : B.Scheme) (U : X.obj.Opens) :
    Set.range (B.inclusion.map (openHom B X U)).base = (U : Set X.obj) :=
  U.range_ι

/-- The affine opens of an object of the big étale site cover it. -/
private theorem iUnion_range_map_openHom (X : B.Scheme) :
    (⋃ U : X.obj.affineOpens, Set.range (B.inclusion.map (openHom B X U.1)).base) = Set.univ := by
  simp only [range_map_openHom]
  simpa only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top] using
    congrArg (fun U : X.obj.Opens => (U : Set X.obj)) (iSup_affineOpens_eq_top X.obj)

/-- The image of the second projection of a fibre product in the big étale site is the preimage of
the image of the first morphism. -/
@[ega "IV 9.2.2" "(iv), special case"]
private theorem range_map_pullback_snd {X Y S : B.Scheme} (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (B.inclusion.map (pullback.snd f g)).base =
      (B.inclusion.map g).base ⁻¹' Set.range (B.inclusion.map f).base := by
  simpa only [Set.preimage_univ, Set.image_univ] using
    Scheme.image_preimage_eq_of_isPullback
      ((IsPullback.of_hasPullback f g).map B.inclusion) Set.univ

/-- A property of morphisms of schemes stable under base change passes to the second projection of a
fibre product in the big étale site. -/
private theorem property_map_pullback_snd (Q : MorphismProperty Scheme)
    [Q.IsStableUnderBaseChange] {X Y S : B.Scheme} (f : X ⟶ S) (g : Y ⟶ S)
    (hf : Q (B.inclusion.map f)) : Q (B.inclusion.map (pullback.snd f g)) :=
  MorphismProperty.of_isPullback ((IsPullback.of_hasPullback f g).map B.inclusion) hf

section General

variable {D : Type w} [Category.{v} D]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- Inverse image around a commuting square: restricting a sheaf from the bottom right corner to
the top left corner along either side of the square gives the same sheaf, by the composition law
for inverse image. -/
private def pullObjSquareIso {T X S Y : B.Scheme} (j : T ⟶ X) (f : X ⟶ Y) (p : T ⟶ S) (i : S ⟶ Y)
    (h : j ≫ f = p ≫ i) (F : Sheaf (SmallEtale.topology B Y.obj Y.property) D) :
    smallEtalePullObj B j (smallEtalePullObj B f F) ≅
      smallEtalePullObj B p (smallEtalePullObj B i F) :=
  (smallEtaleSheafPullbackCompIso B T X Y j f D).app F ≪≫ eqToIso (by rw [h]) ≪≫
    ((smallEtaleSheafPullbackCompIso B T S Y p i D).app F).symm

/-- The image in the source of the stratum of a pulled back partition: the image of the preimage of
the image of the original stratum. -/
private theorem range_map_pullbackStratum {X Y : B.Scheme} (f : X ⟶ Y) (U : X.obj.Opens)
    {Z : B.Scheme} (ι : Z ⟶ Y) :
    Set.range (B.inclusion.map
        (pullback.snd ι (openHom B X U ≫ f) ≫ openHom B X U)).base =
      U.ι.base '' ((B.inclusion.map (openHom B X U ≫ f)).base ⁻¹'
        Set.range (B.inclusion.map ι).base) := by
  rw [ConstructibleStratification.range_map_comp, range_map_pullback_snd, map_openHom]

/-- **A partition of the target pulled back to an open subscheme of the source.** The `i`-th
stratum is the fibre product of the `i`-th stratum of the target with the open subscheme. -/
private def pullbackStratification {X Y : B.Scheme} (f : X ⟶ Y)
    (s : ConstructibleStratification B Y ⊤) (U : X.obj.Opens) :
    ConstructibleStratification B X U where
  n := s.n
  piece i := pullback (s.inclusion i) (openHom B X U ≫ f)
  inclusion i := pullback.snd (s.inclusion i) (openHom B X U ≫ f) ≫ openHom B X U
  isImmersion i := by
    have h₁ : IsImmersion (B.inclusion.map (pullback.snd (s.inclusion i)
        (openHom B X U ≫ f))) :=
      property_map_pullback_snd B (@IsImmersion) _ _ (s.isImmersion i)
    simpa only [Functor.map_comp] using
      (inferInstance : IsImmersion
        (B.inclusion.map (pullback.snd (s.inclusion i) (openHom B X U ≫ f)) ≫
          B.inclusion.map (openHom B X U)))
  contained i := by
    rw [range_map_pullbackStratum]
    exact (Set.image_subset_range _ _).trans U.range_ι.subset
  constructible i := by
    rw [range_map_pullbackStratum, Set.preimage_image_eq _ U.ι.isOpenEmbedding.injective]
    exact (B.inclusion.map (openHom B X U ≫ f)).isConstructible_preimage
      (isConstructible_range_of_isConstructible_top B Y (s.inclusion i) (s.constructible i))
  pairwise_disjoint i j hij := by
    rw [range_map_pullbackStratum, range_map_pullbackStratum]
    exact ((s.pairwise_disjoint i j hij).preimage
      (B.inclusion.map (openHom B X U ≫ f)).base).image
        U.isOpenEmbedding.injective.injOn (Set.subset_univ _) (Set.subset_univ _)
  covers := by
    have hcov : (⋃ i, (B.inclusion.map (openHom B X U ≫ f)).base ⁻¹'
        Set.range (B.inclusion.map (s.inclusion i)).base) = Set.univ := by
      rw [← Set.preimage_iUnion, ← s.covers]
      simp
    simp_rw [range_map_pullbackStratum]
    rw [← Set.image_iUnion, hcov, Set.image_univ, U.range_ι]

/-- **Inverse image along a morphism whose target carries one global partition.** If a sheaf on the
target satisfies the condition on the strata of a single constructible stratification of the whole
target, its inverse image along any morphism is a stratified sheaf: that one stratification is
pulled back to every affine open of the source. -/
private theorem isStratifiedSheaf_pullback_of_stratification_top {X Y : B.Scheme} (f : X ⟶ Y)
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (hPPull : ∀ (T' T : B.Scheme) (q : T' ⟶ T)
      (G : Sheaf (SmallEtale.topology B T.obj T.property) D),
      P T G → P T' (smallEtalePullObj B q G))
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) D)
    (s : ConstructibleStratification B Y ⊤)
    (hs : ∀ i, P (s.piece i) (smallEtalePullObj B (s.inclusion i) F)) :
    IsStratifiedSheaf B X P (smallEtalePullObj B f F) := by
  intro W
  refine ⟨pullbackStratification B f s W.1, fun i => ?_⟩
  exact hPIso _ (pullObjSquareIso B
      (pullback.snd (s.inclusion i) (openHom B X W.1 ≫ f) ≫ openHom B X W.1) f
      (pullback.fst (s.inclusion i) (openHom B X W.1 ≫ f)) (s.inclusion i)
      (by rw [Category.assoc]; exact pullback.condition.symm) F).symm
    (hPPull _ _ (pullback.fst (s.inclusion i) (openHom B X W.1 ≫ f)) _ (hs i))

/-- **Stacks 095G for an arbitrary condition on the strata.** The inverse image of a stratified
sheaf along any morphism of the big étale site is stratified, for a condition `P` on the strata
which is closed under isomorphism of sheaves and stable under inverse image.

The source is covered by the fibre products with it of the affine opens of the target, and being a
stratified sheaf is Zariski local. Over such a fibre product the sheaf is the inverse image of the
restriction of `F` to an affine open, and that affine open, being quasi-compact and
quasi-separated, carries a single stratification adapted to the restriction by Tag 095E; it is
that stratification which is pulled back. -/
@[sga "4 IX 2.4" "more general"]
public theorem isStratifiedSheaf_pullback {X Y : B.Scheme} (f : X ⟶ Y)
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (hPPull : ∀ (T' T : B.Scheme) (q : T' ⟶ T)
      (G : Sheaf (SmallEtale.topology B T.obj T.property) D),
      P T G → P T' (smallEtalePullObj B q G))
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) D)
    (hF : IsStratifiedSheaf B Y P F) :
    IsStratifiedSheaf B X P (smallEtalePullObj B f F) := by
  have hPImmersion : ∀ (T T' : B.Scheme) (g : T' ⟶ T), IsImmersion (B.inclusion.map g) →
      ∀ G : Sheaf (SmallEtale.topology B T.obj T.property) D, P T G →
        P T' (smallEtalePullObj B g G) := fun T T' g _ G h => hPPull T' T g G h
  refine isStratifiedSheaf_of_openCover B X P hPIso
    (fun Z _ _ G => (isStratifiedSheaf_tfae B P hPIso hPImmersion Z G).out 1 2)
    (fun Z _ _ G hG => ((isStratifiedSheaf_tfae B P hPIso hPImmersion Z G).out 1 3).mp hG)
    (smallEtalePullObj B f F) (I := Y.obj.affineOpens)
    (fun U => pullback (openHom B Y U.1) f)
    (fun U => pullback.snd (openHom B Y U.1) f) (fun U => ?_) ?_ (fun U => ?_)
  · exact property_map_pullback_snd B (@IsOpenImmersion) _ _ inferInstance
  · simp_rw [range_map_pullback_snd]
    rw [← Set.preimage_iUnion, iUnion_range_map_openHom, Set.preimage_univ]
  · have hUaff : IsAffine (openObj B Y U.1).obj := U.2
    have hUcpt : CompactSpace (openObj B Y U.1).obj := Scheme.compactSpace_of_isAffine _
    have hUqs : QuasiSeparatedSpace (openObj B Y U.1).obj := inferInstance
    have hrestrict : IsStratifiedSheaf B (openObj B Y U.1) P
        (smallEtalePullObj B (openHom B Y U.1) F) :=
      isStratifiedSheaf_pullback_of_isOpenImmersion B (openHom B Y U.1) inferInstance P hPIso F hF
    obtain ⟨s, hs⟩ := ((isStratifiedSheaf_tfae B P hPIso hPImmersion (openObj B Y U.1)
      (smallEtalePullObj B (openHom B Y U.1) F)).out 1 3).mp hrestrict
    exact isStratifiedSheaf_congr B _ P hPIso
      (pullObjSquareIso B (pullback.snd (openHom B Y U.1) f) f
        (pullback.fst (openHom B Y U.1) f) (openHom B Y U.1) pullback.condition.symm F).symm
      (isStratifiedSheaf_pullback_of_stratification_top B
        (pullback.fst (openHom B Y U.1) f) P hPIso hPPull _ s hs)

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

/-- **Stacks 095G for sheaves of sets and of abelian groups.** The inverse image of a constructible
sheaf with values in a concrete category along an arbitrary morphism of schemes is
constructible. -/
@[stacks 095G "sets and abelian groups"]
public theorem isConstructibleFiniteSheaf_pullback {X Y : B.Scheme} (f : X ⟶ Y)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) D)
    (hF : IsConstructibleFiniteSheaf B Y F) :
    IsConstructibleFiniteSheaf B X
      (((smallEtaleBaseChange B f).sheafPullback D
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).obj F) := by
  have hPIso : ∀ (T : B.Scheme)
      {F G : Sheaf (SmallEtale.topology B T.obj T.property) D}, (F ≅ G) →
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD)
        (SmallEtale.topology B T.obj T.property) F →
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD)
        (SmallEtale.topology B T.obj T.property) G := by
    intro T F G e h
    exact Stacks.ConstantSheaf.isFiniteLocallyConstant_congr
      (SmallEtale.topology B T.obj T.property) e (hF := h)
  have hPPull : ∀ (T' T : B.Scheme) (q : T' ⟶ T)
      (G : Sheaf (SmallEtale.topology B T.obj T.property) D),
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD)
        (SmallEtale.topology B T.obj T.property) G →
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD)
        (SmallEtale.topology B T'.obj T'.property) (smallEtalePullObj B q G) := by
    intro T' T q G h
    exact isFiniteLocallyConstant_smallEtaleSheafPullback' B D q G (hH := h)
  exact isStratifiedSheaf_pullback B f _ hPIso hPPull F hF

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
/-- **Stacks 095G for sheaves of modules over a Noetherian ring.** The inverse image of a
constructible sheaf of modules over a Noetherian ring along an arbitrary morphism of schemes is
constructible. -/
@[stacks 095G "modules over a Noetherian ring"]
public theorem isConstructibleModuleSheaf_pullback {X Y : B.Scheme} (f : X ⟶ Y)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{w} R))
    (hF : IsConstructibleModuleSheaf B Y R F) :
    IsConstructibleModuleSheaf B X R
      (((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{w} R)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).obj F) := by
  have hPIso : ∀ (T : B.Scheme)
      {F G : Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{w} R)}, (F ≅ G) →
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
        (SmallEtale.topology B T.obj T.property) F →
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
        (SmallEtale.topology B T.obj T.property) G := by
    intro T F G e h
    exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr
      (SmallEtale.topology B T.obj T.property) R e h
  have hPPull : ∀ (T' T : B.Scheme) (q : T' ⟶ T)
      (G : Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{w} R)),
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
        (SmallEtale.topology B T.obj T.property) G →
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
        (SmallEtale.topology B T'.obj T'.property) (smallEtalePullObj B q G) := by
    intro T' T q G h
    exact isFiniteTypeLocallyConstant_smallEtaleSheafPullback B R q G h
  exact isStratifiedSheaf_pullback B f _ hPIso hPPull F hF

end Modules

end AlgebraicGeometry

end
