module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ImmersionCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IrreducibleTrivializingObject
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SmallEtaleInverseImageModuleExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleSitePointSupport
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.ReducedInducedIrreducible
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves
public import StacksFrontier.Topology.Noetherian.IrreduciblePieceGenericPoint
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A subsheaf of a locally constant sheaf of finite type is constructible

Let `Z` be a scheme with Noetherian underlying space in a big étale site, let `Λ` be a Noetherian
ring, let `F` be a sheaf of `Λ`-modules on the small étale site of `Z` which is locally constant
of finite type, and let `G ⟶ F` be a monomorphism. Then `G` is constructible.

This is the geometric step of Stacks 09BH (3): the case of that statement in which the ambient
sheaf needs no stratification at all.

## Outline

The argument is a Noetherian induction whose single step is supplied on an irreducible stratum,
and it has two halves.

*The open-image step.* On an irreducible locally Noetherian `Z'` the ambient sheaf becomes
constant on an irreducible object `V₀` of the small étale site
(`AlgebraicGeometry.exists_irreducible_trivializing_object`), and the subsheaf then becomes
constant on an object `U₀` of the small étale site of the scheme of `V₀`
(`AlgebraicGeometry.exists_constantSheafIso_overPullback_of_mono`). The composite of the two
structure morphisms makes `U₀` an object of the small étale site of `Z'`, and its image `Ω` is an
*open subscheme* of `Z'`, over which `U₀` is étale and surjective. One nonempty object covering
the final object of the small étale site of `Ω` is all local constancy asks for, so the subsheaf
is locally constant of finite type on `Ω`.

*The Noetherian induction.* Every nonempty relatively open piece of a closed subset of `Z` can be
shrunk to an irreducible one (`Topology.exists_isOpen_isIrreducible_genericPoint`), whose reduced
induced subscheme is an irreducible scheme
(`Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.irreducibleSpace_reducedInducedScheme`);
the open-image step applies to it, and the open subscheme `Ω` obtained there is cut out of the
piece by an open subset of `Z`. That is exactly the hypothesis of
`AlgebraicGeometry.exists_locallyClosed_partition_of_noetherianSpace`, which therefore partitions
`Z` into finitely many locally closed pieces on each of which the subsheaf is constructible; Tag
09YR assembles them.

## Main definitions

* `AlgebraicGeometry.siteEtaleImageObj` — an object of the small étale site of `Z`, read as an
  object of the small étale site of its own open image.
* `AlgebraicGeometry.IsConstructibleOnImmersedPiece` — the property of a subset of `Z` that the
  Noetherian induction establishes.

## Main results

* `AlgebraicGeometry.surjective_siteEtaleImageFactor` and
  `AlgebraicGeometry.ofArrows_siteEtaleImageObj_mem_topology` — an object of the small étale site
  covers its own open image.
* `AlgebraicGeometry.exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_mono` — the
  open-image step.
* `AlgebraicGeometry.exists_isOpen_isConstructibleOnImmersedPiece_inter` — the inductive step.
* `AlgebraicGeometry.isConstructibleModuleSheaf_of_mono_of_isFiniteTypeLocallyConstant` — the
  conclusion.

## Implementation notes

No `@[stacks]` attribute appears in this file. What is proved is one step of the proof of Stacks
09BH (3), and the tag is attributed where that statement is proved, in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/StrongSerreModules.lean`.

The surjectivity of `U₀` over its open image is the only point-set input: the structure morphism
of an object of the small étale site has the open image as its set-theoretic image, and the open
immersion of that image is injective, so the canonical lift along it is surjective.

## References

* [Stacks Project, Tag 09BG](https://stacks.math.columbia.edu/tag/09BG)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 09YR](https://stacks.math.columbia.edu/tag/09YR)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology TopologicalSpace
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u

namespace AlgebraicGeometry

/-! ### An object of the small étale site over its open image -/

section Image

variable (B : BigEtaleSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

/-- The open image of an object of the small étale site lies below the size cutoff: it is an open
subscheme of a scheme that does. -/
theorem contains_siteEtaleImageOpen (X : SmallEtale B S hS) :
    B.Contains (siteEtaleImageOpen B S hS X).toScheme :=
  Scheme.size_lt_of_isOpenImmersion (siteEtaleImageOpen B S hS X).ι hS

/-- An object of the small étale site of `S`, read as an object of the small étale site of its
own open image: the factorisation through the image is a morphism of the site over `S`, hence
étale. -/
def siteEtaleImageObj (X : SmallEtale B S hS) :
    SmallEtale B (siteEtaleImageOpen B S hS X).toScheme (contains_siteEtaleImageOpen B hS X) :=
  ⟨Over.mk (siteEtaleImageFactor B S hS X).hom.left,
    Stacks.EtaleCohomology.etale_toScheme_map B hS (siteEtaleImageFactor B S hS X)⟩

/-- **The factorisation of an object of the small étale site through its open image is
surjective.** The image of the structure morphism is exactly that open subscheme, and the open
immersion of an open subscheme is injective, so the canonical lift along it misses nothing. -/
theorem surjective_siteEtaleImageFactor (X : SmallEtale B S hS) :
    Function.Surjective (B.inclusion.map (siteEtaleImageFactor B S hS X).hom.left) := by
  intro y
  have hfr : Set.range (B.inclusion.map X.obj.hom) ⊆
      Set.range (siteEtaleImageOpen B S hS X).ι := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨B.inclusion.map X.obj.hom z, ⟨z, rfl⟩⟩, rfl⟩
  have hy : (siteEtaleImageOpen B S hS X).ι y ∈ Set.range (B.inclusion.map X.obj.hom) := by
    have h : (siteEtaleImageOpen B S hS X).ι y ∈ ((siteEtaleImageOpen B S hS X) : Set S) :=
      (Scheme.Opens.range_ι (siteEtaleImageOpen B S hS X)) ▸ Set.mem_range_self y
    exact h
  obtain ⟨z, hz⟩ := hy
  refine ⟨z, (siteEtaleImageOpen B S hS X).isOpenEmbedding.injective ?_⟩
  rw [siteEtaleImageFactor_map]
  calc (siteEtaleImageOpen B S hS X).ι
        ((IsOpenImmersion.lift (siteEtaleImageOpen B S hS X).ι
          (B.inclusion.map X.obj.hom) hfr) z)
      = (IsOpenImmersion.lift (siteEtaleImageOpen B S hS X).ι
          (B.inclusion.map X.obj.hom) hfr ≫ (siteEtaleImageOpen B S hS X).ι) z := rfl
    _ = (B.inclusion.map X.obj.hom) z := by rw [IsOpenImmersion.lift_fac]
    _ = (siteEtaleImageOpen B S hS X).ι y := hz

/-- **An object of the small étale site covers its own open image.** The one-element family given
by the factorisation through the image is a covering family of the final object of the small
étale site of that image. -/
theorem ofArrows_siteEtaleImageObj_mem_topology (X : SmallEtale B S hS) :
    Sieve.ofArrows (fun _ : PUnit.{1} => siteEtaleImageObj B hS X)
        (fun _ => (SmallEtale.finalIsTerminal B (siteEtaleImageOpen B S hS X).toScheme
          (contains_siteEtaleImageOpen B hS X)).from (siteEtaleImageObj B hS X)) ∈
      SmallEtale.topology B (siteEtaleImageOpen B S hS X).toScheme
        (contains_siteEtaleImageOpen B hS X)
        (SmallEtale.final B (siteEtaleImageOpen B S hS X).toScheme
          (contains_siteEtaleImageOpen B hS X)) := by
  refine Stacks.EtaleCohomology.ofArrows_mem_topology B
    (contains_siteEtaleImageOpen B hS X) _ _ fun x => ⟨PUnit.unit, ?_⟩
  exact surjective_siteEtaleImageFactor B hS X x

end Image

/-- The sheaf pullback along a morphism of `B.Scheme`s preserves monomorphisms. -/
private theorem mono_sheafPullback_map (B : BigEtaleSite.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    {S T : B.Scheme} (f : T ⟶ S)
    {G F : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{u + 1} Λ)} (i : G ⟶ F)
    [Mono i] :
    Mono (((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).map i) := by
  have := preservesFiniteLimits_smallEtaleSheafPullback_moduleCat.{u + 1, u, u + 1} B f Λ
  exact preserves_mono_of_preservesLimit _ i

/-! ### The open-image step -/

section Step

variable (B : BigEtaleSite.{u}) (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ)]

/-- **The open-image step of Stacks 09BH (3).** On an irreducible locally Noetherian scheme, a
subsheaf of a sheaf of `Λ`-modules which is locally constant of finite type is itself locally
constant of finite type on a nonempty open subscheme.

The ambient sheaf becomes constant on an irreducible object `V₀` of the small étale site, and the
subsheaf then becomes constant on an object `U₀` of the small étale site of the scheme of `V₀`.
Composing structure morphisms makes `U₀` an object of the small étale site of `Z`, étale and
surjective over its own open image `Ω`; that single object covers the final object of the small
étale site of `Ω`, which is all that local constancy asks for there. -/
theorem exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_mono (Z : B.Scheme)
    [IrreducibleSpace Z.obj] [IsLocallyNoetherian Z.obj]
    {G F : Sheaf (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{u + 1} Λ)} (i : G ⟶ F)
    [Mono i]
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (SmallEtale.topology B Z.obj Z.property) F) :
    ∃ (W : B.Scheme) (q : W ⟶ Z), IsOpenImmersion (B.inclusion.map q) ∧ Nonempty W.obj ∧
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
        (SmallEtale.topology B W.obj W.property) (smallEtalePullObj B q G) := by
  classical
  obtain ⟨V₀, E, hV₀irr, hE, hcF⟩ := exists_irreducible_trivializing_object B Λ Z F hF
  have : IrreducibleSpace (V₀.obj.left).obj := hV₀irr
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj Z.obj Z.property)) :=
    inferInstanceAs (IsLocallyNoetherian Z.obj)
  have : IsLocallyNoetherian (V₀.obj.left).obj :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map V₀.obj.hom)
  rw [nonempty_constantSheafIso_over_iff B Z.obj Z.property V₀ (ModuleCat.{u + 1} Λ) F E] at hcF
  obtain ⟨cF⟩ := hcF
  have := mono_sheafPullback_map B Λ V₀.obj.hom i
  obtain ⟨U₀, N, hU₀ne, hN, hcG⟩ :=
    exists_constantSheafIso_overPullback_of_mono B (V₀.obj.left) Λ E
      (((smallEtaleBaseChange B V₀.obj.hom).sheafPullback (ModuleCat.{u + 1} Λ)
        (SmallEtale.topology B Z.obj Z.property)
        (SmallEtale.topology B (V₀.obj.left).obj (V₀.obj.left).property)).map i ≫ cF.inv) hE
  rw [nonempty_constantSheafIso_over_iff B (V₀.obj.left).obj (V₀.obj.left).property U₀
    (ModuleCat.{u + 1} Λ) _ N] at hcG
  obtain ⟨cG⟩ := hcG
  have hUqe : Etale (B.inclusion.map (U₀.obj.hom ≫ V₀.obj.hom)) := by
    rw [Functor.map_comp]
    infer_instance
  let Uq : SmallEtale B Z.obj Z.property := ⟨Over.mk (U₀.obj.hom ≫ V₀.obj.hom), hUqe⟩
  let Ω := siteEtaleImageOpen B Z.obj Z.property Uq
  let W : B.Scheme := ((opensToBoundedEtale B Z.obj Z.property).obj Ω).obj.left
  let q : W ⟶ Z := ((opensToBoundedEtale B Z.obj Z.property).obj Ω).obj.hom
  have hq : IsOpenImmersion (B.inclusion.map q) := (inferInstance : IsOpenImmersion Ω.ι)
  refine ⟨W, q, hq, hU₀ne.map (B.inclusion.map
    (siteEtaleImageFactor B Z.obj Z.property Uq).hom.left), ?_⟩
  refine Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_cover
    (SmallEtale.topology B W.obj W.property) Λ
    (SmallEtale.finalIsTerminal B W.obj W.property) _
    (ofArrows_siteEtaleImageObj_mem_topology B Z.property Uq) fun _ => ⟨N, hN, ?_⟩
  rw [nonempty_constantSheafIso_over_iff B W.obj W.property
    (siteEtaleImageObj B Z.property Uq) (ModuleCat.{u + 1} Λ) (smallEtalePullObj B q G) N]
  have heq : (siteEtaleImageObj B Z.property Uq).obj.hom ≫ q = U₀.obj.hom ≫ V₀.obj.hom :=
    Over.w (siteEtaleImageFactor B Z.obj Z.property Uq).hom
  have hpull := congrArg (fun m : Uq.obj.left ⟶ Z =>
    ((smallEtaleBaseChange B m).sheafPullback (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B (Uq.obj.left).obj (Uq.obj.left).property)).obj G) heq.symm
  exact ⟨cG ≪≫ (smallEtaleSheafPullbackCompIso B (U₀.obj.left) (V₀.obj.left) Z
      U₀.obj.hom V₀.obj.hom (ModuleCat.{u + 1} Λ)).app G ≪≫ eqToIso hpull ≪≫
    ((smallEtaleSheafPullbackCompIso B (Uq.obj.left) W Z
      (siteEtaleImageObj B Z.property Uq).obj.hom q (ModuleCat.{u + 1} Λ)).app G).symm⟩


/-! ### The Noetherian induction -/

/-- The reduced induced scheme on a locally closed subset of a locally Noetherian scheme is
locally Noetherian: its canonical morphism is an immersion, hence locally of finite type. -/
@[ega "II 6.5.1" "partial"]
theorem isLocallyNoetherian_reducedInducedScheme {X : Scheme.{u}} (T : Set X)
    (hT : IsLocallyClosed T) [IsLocallyNoetherian X] :
    IsLocallyNoetherian (reducedInducedScheme T hT) :=
  LocallyOfFiniteType.isLocallyNoetherian (reducedInducedInclusion T hT)

/-- The property of a subset of `Z` which the Noetherian induction of Stacks 09BH (3)
establishes: some subscheme immersed in `Z` with that subset as its image carries a constructible
inverse image of `G`. -/
def IsConstructibleOnImmersedPiece (Z : B.Scheme)
    (G : Sheaf (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{u + 1} Λ))
    (T : Set Z.obj) : Prop :=
  ∃ (Z' : B.Scheme) (g : Z' ⟶ Z), IsImmersion (B.inclusion.map g) ∧
    Set.range (B.inclusion.map g) = T ∧
    IsConstructibleModuleSheaf B Z' Λ (smallEtalePullObj B g G)

/-- **The geometric step on an irreducible piece.** On an irreducible locally closed subset `T₀`
of `Z`, some open subset of `Z` cuts out a nonempty part of `T₀` on which the subsheaf is
constructible.

The reduced induced subscheme of `T₀` is an irreducible locally Noetherian scheme, so the
open-image step applies to the restricted subsheaf there; the open subscheme obtained is cut out
of `T₀` by an open subset of `Z`, the inclusion of `T₀` being a topological embedding. -/
theorem exists_isOpen_isConstructibleOnImmersedPiece_inter (Z : B.Scheme)
    [IsLocallyNoetherian Z.obj]
    {G F : Sheaf (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{u + 1} Λ)} (i : G ⟶ F)
    [Mono i]
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (SmallEtale.topology B Z.obj Z.property) F)
    (T₀ : Set Z.obj) (hlc : IsLocallyClosed T₀) (hirr : IsIrreducible T₀) :
    ∃ V : Set Z.obj, IsOpen V ∧ (V ∩ T₀).Nonempty ∧
      IsConstructibleOnImmersedPiece B Λ Z G (V ∩ T₀) := by
  classical
  have hirrZ : IrreducibleSpace (ConstructibleStratification.partitionPiece B Z T₀ hlc).obj :=
    irreducibleSpace_reducedInducedScheme T₀ hlc hirr
  have hlnZ : IsLocallyNoetherian
      (ConstructibleStratification.partitionPiece B Z T₀ hlc).obj :=
    isLocallyNoetherian_reducedInducedScheme T₀ hlc
  have hmapp := ConstructibleStratification.map_partitionInclusion B Z T₀ hlc
  have himmp : IsImmersion
      (B.inclusion.map (ConstructibleStratification.partitionInclusion B Z T₀ hlc)) :=
    hmapp ▸ isImmersion_reducedInducedInclusion T₀ hlc
  have hemb : IsEmbedding
      (B.inclusion.map (ConstructibleStratification.partitionInclusion B Z T₀ hlc)) :=
    hmapp ▸ isEmbedding_reducedInducedInclusion T₀ hlc
  have hrng : Set.range
      (B.inclusion.map (ConstructibleStratification.partitionInclusion B Z T₀ hlc)) = T₀ :=
    hmapp ▸ range_inclusion T₀ hlc
  have := mono_sheafPullback_map B Λ (ConstructibleStratification.partitionInclusion B Z T₀ hlc) i
  obtain ⟨W, q, hqoi, hWne, hlcW⟩ :=
    exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_mono B Λ
      (ConstructibleStratification.partitionPiece B Z T₀ hlc)
      (((smallEtaleBaseChange B
        (ConstructibleStratification.partitionInclusion B Z T₀ hlc)).sheafPullback
          (ModuleCat.{u + 1} Λ) (SmallEtale.topology B Z.obj Z.property)
          (SmallEtale.topology B (ConstructibleStratification.partitionPiece B Z T₀ hlc).obj
            (ConstructibleStratification.partitionPiece B Z T₀ hlc).property)).map i)
      (isFiniteTypeLocallyConstant_smallEtaleSheafPullback B Λ
        (ConstructibleStratification.partitionInclusion B Z T₀ hlc) F hF)
  have hqoi' : IsOpenImmersion (B.inclusion.map q) := hqoi
  obtain ⟨V, hV, hVpre⟩ :=
    hemb.isInducing.isOpen_iff.mp (IsOpenImmersion.isOpen_range (B.inclusion.map q))
  have himg := Set.image_preimage_eq_inter_range
    (f := ⇑(B.inclusion.map (ConstructibleStratification.partitionInclusion B Z T₀ hlc)))
    (t := V)
  rw [hVpre, hrng] at himg
  have hrange : Set.range (B.inclusion.map
      (q ≫ ConstructibleStratification.partitionInclusion B Z T₀ hlc)) = V ∩ T₀ := by
    refine Eq.trans ?_ himg
    rw [← Set.range_comp]
    rfl
  have hWne' : Nonempty (B.inclusion.obj W) := hWne
  refine ⟨V, hV, hrange ▸ Set.range_nonempty _, W,
    q ≫ ConstructibleStratification.partitionInclusion B Z T₀ hlc, ?_, hrange, ?_⟩
  · rw [Functor.map_comp]
    infer_instance
  · refine isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant B W Λ _
      (Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr
        (SmallEtale.topology B W.obj W.property) Λ ?_ hlcW)
    exact (smallEtaleSheafPullbackCompIso B W
      (ConstructibleStratification.partitionPiece B Z T₀ hlc) Z q
      (ConstructibleStratification.partitionInclusion B Z T₀ hlc) (ModuleCat.{u + 1} Λ)).app G

/-- **A subsheaf of a locally constant sheaf of finite type is constructible**, which is the
geometric step of Stacks 09BH (3): the case of that statement in which the ambient sheaf needs no
stratification.

The Noetherian induction of
`AlgebraicGeometry.exists_locallyClosed_partition_of_noetherianSpace` is fed with
`AlgebraicGeometry.exists_isOpen_isConstructibleOnImmersedPiece_inter`, applied to the irreducible
piece supplied by `Topology.exists_isOpen_isIrreducible_genericPoint`; the resulting finite family
of immersed subschemes covers `Z` with constructible images, so Tag 09YR assembles the
restrictions into constructibility on `Z`. -/
theorem isConstructibleModuleSheaf_of_mono_of_isFiniteTypeLocallyConstant (Z : B.Scheme)
    [IsLocallyNoetherian Z.obj] [NoetherianSpace Z.obj]
    {G F : Sheaf (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{u + 1} Λ)} (i : G ⟶ F)
    [Mono i]
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (SmallEtale.topology B Z.obj Z.property) F) :
    IsConstructibleModuleSheaf B Z Λ G := by
  classical
  have hns : NoetherianSpace (B.inclusion.obj Z) := inferInstanceAs (NoetherianSpace Z.obj)
  have hqs : QuasiSeparatedSpace Z.obj := IsLocallyNoetherian.quasiSeparatedSpace
  have hcs : CompactSpace Z.obj := NoetherianSpace.compactSpace _
  have hP : ∀ C : Set Z.obj, IsClosed C → ((Set.univ : Set Z.obj) ∩ C).Nonempty →
      ∃ V : Set Z.obj, IsOpen V ∧ (V ∩ Set.univ ∩ C).Nonempty ∧
        IsConstructibleOnImmersedPiece B Λ Z G (V ∩ Set.univ ∩ C) := by
    intro C hC hne
    obtain ⟨V₁, hV₁, -, hirr, -⟩ :=
      Topology.exists_isOpen_isIrreducible_genericPoint (W := (Set.univ : Set Z.obj))
        isOpen_univ C hC hne
    obtain ⟨V₂, hV₂, hne₂, hcon₂⟩ :=
      exists_isOpen_isConstructibleOnImmersedPiece_inter B Λ Z i hF (V₁ ∩ Set.univ ∩ C)
        ((hV₁.inter isOpen_univ).isLocallyClosed.inter hC.isLocallyClosed) hirr
    have hset : V₁ ∩ V₂ ∩ Set.univ ∩ C = V₂ ∩ (V₁ ∩ Set.univ ∩ C) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_univ, and_true]
      tauto
    exact ⟨V₁ ∩ V₂, hV₁.inter hV₂, hset ▸ hne₂, hset ▸ hcon₂⟩
  obtain ⟨n, A, hlcA, -, hPA, -, hcov⟩ :=
    exists_locallyClosed_partition_of_noetherianSpace (Set.univ : Set Z.obj) isOpen_univ
      (IsConstructibleOnImmersedPiece B Λ Z G) hP
  have hPA' : ∀ k, ∃ (Z' : B.Scheme) (g : Z' ⟶ Z), IsImmersion (B.inclusion.map g) ∧
      Set.range (B.inclusion.map g) = A k ∧
      IsConstructibleModuleSheaf B Z' Λ (smallEtalePullObj B g G) := hPA
  choose Zp gp himm hrangep hconp using hPA'
  refine isConstructibleModuleSheaf_of_constructible_immersion_cover B Z Λ G Zp gp himm
    (fun k => ?_) ?_ hconp
  · have h : Set.range (B.inclusion.map (gp k)).base = A k := hrangep k
    rw [h]
    exact isConstructible_of_isLocallyClosed (hlcA k)
  · rw [hcov]
    exact Set.iUnion_congr fun k => (hrangep k).symm

end Step

end AlgebraicGeometry

end
