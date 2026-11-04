module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.GlobalStratification
public import StacksFrontier.Topology.Constructible.InConstructible
public import StacksFrontier.Topology.Spectral.BijectionHomeomorph
public import StacksFrontier.Topology.Spectral.ConstructiblyClosed
public import StacksFrontier.Topology.Stratification.RefineConstructible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructibility from a cover by constructible locally closed subschemes

On a quasi-compact quasi-separated scheme `X`, an étale sheaf is constructible as soon as its
inverse images along a family of immersions with constructible images covering `X` are
constructible. The index set of the family is arbitrary; quasi-compactness of the constructible
topology cuts it down to a finite subfamily.

The route is the one of the source. The underlying space of `X` is spectral, so each member of the
cover is a constructibly closed subspace of a spectral space and therefore spectral in its own
right; in particular it is quasi-compact and quasi-separated, which is what lets the global form of
constructibility be applied to it. Each member thus carries **one** finite partition by
constructible locally closed subschemes on which the condition on the strata holds, and the images
of those strata in `X` are constructible there, by constructibility of a constructible subset of a
constructible subspace. The resulting finite constructible cover of `X` is refined by a finite
stratification with constructible strata, and each stratum is cut out of the stratum containing it.

## Main results

* `Topology.IsEmbedding.spectralSpace_of_isConstructible_range` — the source of an embedding with
  constructible image into a spectral space is spectral.
* `Topology.IsEmbedding.isConstructible_image_of_isConstructible_range` — such an embedding carries
  constructible subsets to constructible subsets.
* `AlgebraicGeometry.spectralSpace_of_isImmersion_of_isConstructible_range` — an immersed
  subscheme with constructible image in a quasi-compact quasi-separated scheme has spectral space.
* `AlgebraicGeometry.exists_stratification_top_of_constructible_immersion_cover` — the conclusion
  for an arbitrary condition on the strata, as one stratification of the whole scheme.
* `AlgebraicGeometry.isConstructibleFiniteSheaf_of_constructible_immersion_cover` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_of_constructible_immersion_cover` — Tag 09YR for
  sheaves of sets and of abelian groups, and for sheaves of modules over a Noetherian ring.

## Implementation notes

The strata of the output are built with `AlgebraicGeometry.BigEtaleSite.strataCutObj`, i.e. **inside
the stratum scheme** they are cut from, as the reduced induced subscheme on the preimage there of
the refining stratum. They are never taken as subschemes of the ambient scheme with the same image:
the condition on a stratum is a condition on sheaves over that stratum, so it reaches the cut part
by inverse image along `AlgebraicGeometry.BigEtaleSite.strataCutHom`, which exists only because the
cut part lives over the original stratum. For an arbitrary immersion there is no factorization of a
subscheme of the ambient through it, which is why
`AlgebraicGeometry.ConstructibleStratification.ofPartition` is not usable here.

The two statements are stated with the coefficient universe of
`AlgebraicGeometry.IsConstructibleFiniteSheaf`, which is independent of the scheme universe; taking
it to be the successor of the scheme universe recovers the statement of the source.

The strata of the refinement that are empty are discarded, by indexing the output by the subtype of
nonempty strata. This is what makes the construction uniform in the empty scheme, where the
refining family is itself empty and no stratum of it could be chosen.

No Stacks attribute for Tag 09YR is placed in this file.

## References

* [Stacks Project, Tag 09YR](https://stacks.math.columbia.edu/tag/09YR)
* [Stacks Project, Tag 095E](https://stacks.math.columbia.edu/tag/095E)
* [Stacks Project, Tag 09YJ](https://stacks.math.columbia.edu/tag/09YJ)
* [Stacks Project, Tag 09Y4](https://stacks.math.columbia.edu/tag/09Y4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe v w t r u

namespace Topology.IsEmbedding

/-- An embedding with constructible image into a spectral space has spectral source: the image is
closed for the constructible topology, hence spectral in the subspace topology, and the embedding
is a homeomorphism onto it. -/
public theorem spectralSpace_of_isConstructible_range {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [SpectralSpace Y] {f : X → Y}
    (hf : IsEmbedding f) (hr : IsConstructible (Set.range f)) : SpectralSpace X := by
  have hS : SpectralSpace (Set.range f) :=
    spectralSpace_of_isClosed_constructibleTopology _ hr.isClosed_constructibleTopology
  have : CompactSpace X := Homeomorph.compactSpace hf.toHomeomorph.symm
  exact hf.toHomeomorph.isOpenEmbedding.spectralSpace

/-- **Stacks 09YJ, in the form used here.** An embedding with constructible image into a space with
a basis of quasi-compact opens carries constructible subsets to constructible subsets: the source is
homeomorphic to the image, and a constructible subset of a constructible subspace is constructible
in the ambient space. -/
public theorem isConstructible_image_of_isConstructible_range {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [PrespectralSpace Y] {f : X → Y}
    (hf : IsEmbedding f) (hr : IsConstructible (Set.range f))
    {Z : Set X} (hZ : IsConstructible Z) : IsConstructible (f '' Z) := by
  have hF : IsConstructible (hf.toHomeomorph.symm ⁻¹' Z) :=
    hZ.preimage_of_isOpenEmbedding hf.toHomeomorph.symm.isOpenEmbedding
  have himg : (Subtype.val : Set.range f → Y) '' (hf.toHomeomorph.symm ⁻¹' Z) = f '' Z := by
    rw [← Homeomorph.image_eq_preimage_symm, Set.image_image]
    simp
  rw [← himg]
  exact isConstructibleSet_iff_isConstructible.mp
    (isConstructibleSet_of_isConstructibleSet_in_constructible ‹PrespectralSpace Y›
      (isConstructibleSet_iff_isConstructible.mpr hr)
      (isConstructibleSet_iff_isConstructible.mpr hF))

end Topology.IsEmbedding

namespace AlgebraicGeometry

/-- A subscheme immersed in a quasi-compact quasi-separated scheme with constructible image has
spectral underlying space. In particular it is quasi-compact and quasi-separated, which is the
"details omitted" step of the source. -/
public theorem spectralSpace_of_isImmersion_of_isConstructible_range {X Y : Scheme.{u}}
    [SpectralSpace Y] (f : X ⟶ Y) [IsImmersion f]
    (hr : IsConstructible (Set.range ⇑f.base)) : SpectralSpace X :=
  f.isEmbedding.spectralSpace_of_isConstructible_range hr

/-- The underlying space of a quasi-compact quasi-separated scheme is spectral: it is sober, T0 and
has a basis of quasi-compact opens for any scheme. -/
@[sga "4 IV 4.2.1" "special case"]
public theorem Scheme.spectralSpace_of_compactSpace_quasiSeparatedSpace (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] : SpectralSpace X := {}

variable (B : BigEtaleSite.{u}) {D : Type w} [Category.{v} D]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  (X : B.Scheme)

/-- **Tag 09YR, for an arbitrary condition on the strata.** On a quasi-compact quasi-separated
scheme, if the inverse image of a sheaf along each member of a family of immersions with
constructible images covering the scheme has, on every affine open of that member, a finite
partition by constructible locally closed subschemes satisfying a condition stable under
isomorphism and inverse image, then the scheme itself carries one such partition.

Quasi-compactness of the constructible topology makes the cover finite; each member is then spectral
in its own right, so the global form of Tag 095E applies to it; the images in the ambient scheme of
the strata so obtained are constructible by Tag 09YJ, and Tag 09Y4 refines that finite constructible
cover by a stratification whose strata are cut out of the strata containing them. -/
@[sga "4 IX 2.4" "Clause (i)"]
public theorem exists_stratification_top_of_constructible_immersion_cover
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (hPPull : ∀ (T' T : B.Scheme) (q : T' ⟶ T)
      (G : Sheaf (SmallEtale.topology B T.obj T.property) D),
      P T G → P T' (smallEtalePullObj B q G))
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D)
    {I : Type*} (T : I → B.Scheme) (j : ∀ i, T i ⟶ X)
    (hj : ∀ i, IsImmersion (B.inclusion.map (j i)))
    (hc : ∀ i, IsConstructible (Set.range (B.inclusion.map (j i)).base))
    (hcover : (Set.univ : Set X.obj) = ⋃ i, Set.range (B.inclusion.map (j i)).base)
    (hF : ∀ i, IsStratifiedSheaf B (T i) P (smallEtalePullObj B (j i) F)) :
    ∃ t : ConstructibleStratification B X ⊤,
      ∀ i, P (t.piece i) (smallEtalePullObj B (t.inclusion i) F) := by
  classical
  have hXspec : SpectralSpace X.obj := Scheme.spectralSpace_of_compactSpace_quasiSeparatedSpace _
  have hXspec' : SpectralSpace ↥(B.inclusion.obj X) := hXspec
  -- The cover is finite: a constructible set is open for the constructible topology, which is
  -- quasi-compact on a spectral space.
  obtain ⟨tf, htf⟩ := @IsCompact.elim_finite_subcover X.obj (constructibleTopology X.obj)
    Set.univ I (@CompactSpace.isCompact_univ X.obj (constructibleTopology X.obj)
      (compactSpace_constructibleTopology X.obj))
    (fun i => Set.range (B.inclusion.map (j i)).base)
    (fun i => (hc i).isOpen_constructibleTopology) (by rw [← hcover])
  set σ : Fin tf.card → I := fun k => (tf.equivFin.symm k).1 with hσ
  -- Each chosen member of the cover carries one stratification of itself.
  have hex : ∀ k : Fin tf.card, ∃ s : ConstructibleStratification B (T (σ k)) ⊤,
      ∀ l, P (s.piece l)
        (smallEtalePullObj B (s.inclusion l) (smallEtalePullObj B (j (σ k)) F)) := by
    intro k
    have : SpectralSpace (T (σ k)).obj :=
      spectralSpace_of_isImmersion_of_isConstructible_range
        (Y := B.inclusion.obj X) (B.inclusion.map (j (σ k))) (hc (σ k))
    exact exists_stratification_top_of_isStratifiedSheaf B (T (σ k)) P hPIso hPPull _ (hF (σ k))
  choose s hs using hex
  -- The strata of all the chosen members, as immersed subschemes of the ambient scheme.
  set Sig := Σ k : Fin tf.card, Fin ((s k).n) with hSig
  set inc : ∀ q : Sig, (s q.1).piece q.2 ⟶ X :=
    fun q => (s q.1).inclusion q.2 ≫ j (σ q.1) with hinc
  have himm : ∀ q : Sig, IsImmersion (B.inclusion.map (inc q)) := by
    intro q
    have := (s q.1).isImmersion q.2
    rw [hinc, Functor.map_comp]
    infer_instance
  have hPcomp : ∀ q : Sig, P ((s q.1).piece q.2) (smallEtalePullObj B (inc q) F) := fun q =>
    hPIso _ ((smallEtaleSheafPullbackCompIso B ((s q.1).piece q.2) (T (σ q.1)) X
      ((s q.1).inclusion q.2) (j (σ q.1)) D).app F) (hs q.1 q.2)
  set L : Sig → Set X.obj := fun q => Set.range (B.inclusion.map (inc q)).base with hL
  have hLrange : ∀ q : Sig, L q = ⇑(B.inclusion.map (j (σ q.1))).base ''
      Set.range ⇑(B.inclusion.map ((s q.1).inclusion q.2)).base := by
    intro q
    simp only [hL, hinc, Functor.map_comp]
    simp [Set.range_comp]
  have hLcon : ∀ q : Sig, IsConstructible (L q) := by
    intro q
    rw [hLrange q]
    exact (B.inclusion.map (j (σ q.1))).isEmbedding.isConstructible_image_of_isConstructible_range
      (hc (σ q.1))
      (isConstructible_range_of_isConstructible_top B (T (σ q.1)) ((s q.1).inclusion q.2)
        ((s q.1).constructible q.2))
  have hLcover : (⋃ q : Sig, L q) = Set.univ := by
    refine Set.Subset.antisymm (Set.subset_univ _) (fun x _ => ?_)
    obtain ⟨i, hitf, hxi⟩ := Set.mem_iUnion₂.mp (htf (Set.mem_univ x))
    set k := tf.equivFin ⟨i, hitf⟩
    have hk : σ k = i := by
      rw [hσ]
      simp [k]
    obtain ⟨y, hy⟩ : x ∈ Set.range ⇑(B.inclusion.map (j (σ k))).base := by
      rw [hk]; exact hxi
    have hycov : y ∈ ⋃ l, Set.range ⇑(B.inclusion.map ((s k).inclusion l)).base := by
      have := (s k).covers
      simp only [TopologicalSpace.Opens.coe_top] at this
      rw [← this]
      trivial
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hycov
    refine Set.mem_iUnion.mpr ⟨⟨k, l⟩, ?_⟩
    rw [hLrange]
    exact ⟨y, hl, hy⟩
  -- Refine the finite constructible cover by a stratification (Tag 09Y4).
  let eSig : Sig ≃ Fin (∑ k, (s k).n) := finSigmaFinEquiv
  obtain ⟨𝒮, h𝒮con, h𝒮union⟩ := exists_finiteStratification_refining_constructible
    (fun a : Fin (∑ k, (s k).n) => L (eSig.symm a)) (fun a => hLcon _)
    (by rw [eSig.symm.surjective.iUnion_comp L]; exact hLcover)
  have h𝒮lc : ∀ i, IsLocallyClosed (𝒮.S i) := fun i =>
    isLocallyClosed_of_closure_subset_biUnion_le 𝒮.S (fun _ _ h => 𝒮.disjoint h)
      𝒮.closure_subset i
  -- Every nonempty stratum of the refinement lies inside one of the strata it refines.
  set J := {i : 𝒮.ι // (𝒮.S i).Nonempty} with hJ
  have : Fintype J := Fintype.ofFinite J
  have hchoose : ∀ i : J, ∃ q : Sig, 𝒮.S i.1 ⊆ L q := by
    intro i
    obtain ⟨x, hx⟩ := i.2
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp (hLcover ▸ Set.mem_univ x :
      x ∈ ⋃ q : Sig, L q)
    obtain ⟨Ip, hIp⟩ := h𝒮union (eSig q)
    rw [Equiv.symm_apply_apply] at hIp
    refine ⟨q, ?_⟩
    rw [hIp] at hq ⊢
    obtain ⟨i', hi', hxi'⟩ := Set.mem_iUnion₂.mp hq
    have : i.1 = i' := by
      by_contra hne
      exact Set.disjoint_left.mp (𝒮.disjoint hne) hx hxi'
    subst this
    exact Set.subset_biUnion_of_mem (u := 𝒮.S) hi'
  choose q hq using hchoose
  let eJ := Fintype.equivFin J
  have hrange : ∀ i : J, Set.range (B.inclusion.map
      (B.strataCutHom X (inc (q i)) (h𝒮lc i.1) ≫ inc (q i))).base = 𝒮.S i.1 := by
    intro i
    rw [B.range_strataCutHom_comp X (inc (q i)) (h𝒮lc i.1)]
    exact Set.inter_eq_right.mpr (hq i)
  refine ⟨{ n := Fintype.card J
            piece := fun m => B.strataCutObj X (inc (q (eJ.symm m))) (h𝒮lc (eJ.symm m).1)
            inclusion := fun m =>
              B.strataCutHom X (inc (q (eJ.symm m))) (h𝒮lc (eJ.symm m).1) ≫ inc (q (eJ.symm m))
            isImmersion := fun m =>
              B.isImmersion_strataCutHom_comp X _ (himm _) _
            contained := fun m => by
              rw [hrange]
              simp
            constructible := fun m => by
              rw [hrange]
              exact (h𝒮con _).preimage_of_isOpenEmbedding
                (⊤ : X.obj.Opens).isOpenEmbedding
            pairwise_disjoint := fun m m' hmm' => by
              rw [hrange, hrange]
              exact 𝒮.disjoint fun h => hmm' (eJ.symm.injective (Subtype.ext h))
            covers := ?_ }, ?_⟩
  · have h1 : (⋃ m : Fin (Fintype.card J), Set.range (B.inclusion.map
        (B.strataCutHom X (inc (q (eJ.symm m))) (h𝒮lc (eJ.symm m).1)
          ≫ inc (q (eJ.symm m)))).base) = ⋃ i : J, 𝒮.S i.1 := by
      rw [← eJ.symm.surjective.iUnion_comp fun i : J => 𝒮.S i.1]
      exact Set.iUnion_congr fun m => hrange _
    have h2 : (⋃ i : J, 𝒮.S i.1) = Set.univ := by
      refine Set.Subset.antisymm (Set.subset_univ _) (fun x _ => ?_)
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (𝒮.iUnion_eq_univ ▸ Set.mem_univ x :
        x ∈ ⋃ i, 𝒮.S i)
      exact Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, hi⟩
    rw [h1, h2]
    simp
  · exact fun m => strataCondition_strataCutHom B X P hPIso hPPull
      (inc (q (eJ.symm m))) (h𝒮lc (eJ.symm m).1) F (hPcomp _)

end AlgebraicGeometry

namespace AlgebraicGeometry

section Finite

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
  {D : Type w} [Category.{v} D] {FD : D → D → Type*} {CD : D → Type t}
  [∀ A A', FunLike (FD A A') (CD A) (CD A')] [ConcreteCategory.{t} D FD]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) D]

/-- **Stacks 09YR, for sheaves of sets and of abelian groups.** On a quasi-compact quasi-separated
scheme, a sheaf with values in a concrete category is constructible as soon as there are
constructible locally closed subschemes covering the scheme on each of which its inverse image is
constructible. -/
@[stacks 09YR "sets and abelian groups"]
public theorem isConstructibleFiniteSheaf_of_constructible_immersion_cover
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D)
    {I : Type*} (T : I → B.Scheme) (j : ∀ i, T i ⟶ X)
    (hj : ∀ i, IsImmersion (B.inclusion.map (j i)))
    (hc : ∀ i, Topology.IsConstructible (Set.range (B.inclusion.map (j i)).base))
    (hcover : (Set.univ : Set X.obj) = ⋃ i, Set.range (B.inclusion.map (j i)).base)
    (hF : ∀ i, IsConstructibleFiniteSheaf B (T i)
      (((smallEtaleBaseChange B (j i)).sheafPullback D
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (T i).obj (T i).property)).obj F)) :
    IsConstructibleFiniteSheaf B X F := by
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
  exact isStratifiedSheaf_of_exists_stratification_top B X _ hPIso hPPull F
    (exists_stratification_top_of_constructible_immersion_cover B X _ hPIso hPPull F T j hj hc
      hcover hF)

end Finite

section Modules

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
  (R : Type r) [CommRing R] [IsNoetherianRing R]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} R)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} R)]

omit [IsNoetherianRing R] in
/-- **Stacks 09YR, for sheaves of modules over a Noetherian ring.** On a quasi-compact
quasi-separated scheme, a sheaf of modules over a Noetherian ring is constructible as soon as there
are constructible locally closed subschemes covering the scheme on each of which its inverse image
is constructible. -/
@[stacks 09YR "modules over a Noetherian ring"]
public theorem isConstructibleModuleSheaf_of_constructible_immersion_cover
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R))
    {I : Type*} (T : I → B.Scheme) (j : ∀ i, T i ⟶ X)
    (hj : ∀ i, IsImmersion (B.inclusion.map (j i)))
    (hc : ∀ i, Topology.IsConstructible (Set.range (B.inclusion.map (j i)).base))
    (hcover : (Set.univ : Set X.obj) = ⋃ i, Set.range (B.inclusion.map (j i)).base)
    (hF : ∀ i, IsConstructibleModuleSheaf B (T i) R
      (((smallEtaleBaseChange B (j i)).sheafPullback (ModuleCat.{w} R)
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (T i).obj (T i).property)).obj F)) :
    IsConstructibleModuleSheaf B X R F := by
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
  exact isStratifiedSheaf_of_exists_stratification_top B X _ hPIso hPPull F
    (exists_stratification_top_of_constructible_immersion_cover B X _ hPIso hPPull F T j hj hc
      hcover hF)

end Modules

end AlgebraicGeometry

end
