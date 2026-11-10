module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.OpenRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StratificationGlue
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StratificationSurgery
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageFiniteTypeLocallyConstant
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructibility is Zariski local, and is a single stratification

Stacks 095E says three things are the same for a sheaf on the small étale site of a quasi-compact
quasi-separated scheme `Z`: it is constructible; it is constructible after restriction to each
member of some open cover of `Z`; and there is *one* finite partition of `Z` into constructible
locally closed subschemes on each of which the sheaf becomes finite locally constant.

The definition of constructibility quantifies over the affine opens of `Z` separately, so neither
of the other two conditions is formal. Passing from the affine opens to a single partition of `Z`
is this file's work, and it is done for an arbitrary condition `P` on the strata, exactly as
`AlgebraicGeometry.IsStratifiedSheaf` is parametrised by one: the argument is the same for sheaves
of sets, of abelian groups and of modules.

## Main results

* `AlgebraicGeometry.exists_constructibleStratification_top_of_locally`: the heart. On a
  quasi-compact quasi-separated scheme, a sheaf which admits a stratification by `P` on a
  quasi-compact open neighbourhood of every point admits one on the whole scheme.
* `AlgebraicGeometry.isStratifiedSheaf_of_constructibleStratification_top`: conversely, a single
  stratification of the whole scheme makes the sheaf stratified, by cutting each stratum down to an
  affine open.
* `AlgebraicGeometry.exists_openCover_isStratifiedSheaf` and
  `AlgebraicGeometry.isStratifiedSheaf_of_openCover_of_quasiSeparated`: the two implications
  between the first two conditions of Tag 095E on their own, with the hypotheses each of them
  really needs — the first none at all, the second quasi-separatedness alone, the compactness used
  being that of the affine open being stratified rather than of the scheme.
* `AlgebraicGeometry.isStratifiedSheaf_tfae`: **Tag 095E for an arbitrary stratum condition** — the
  three conditions are equivalent for any `P` closed under isomorphism and stable under inverse
  image along an immersion.
* `AlgebraicGeometry.isConstructibleFiniteSheaf_tfae` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_tfae`: **Tag 095E** for sheaves of sets and of
  abelian groups, and for sheaves of modules over a Noetherian ring. Together these are the whole
  tag, including its assertion that the analogue holds for abelian sheaves and for `Λ`-modules, so
  the attribute is carried by both.

## Implementation notes

The three operations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StratificationSurgery` are what make
the heart work. Finitely many quasi-compact opens suffice to cover `Z`; the stratification on each
is extended to the whole of `Z` by adjoining the complement of that open, which puts all of them
over the same open subscheme and so lets
`AlgebraicGeometry.ConstructibleStratification.exists_refines_forall` take a common refinement;
the empty strata of that refinement are discarded, so that each remaining stratum contains a point
and that point lies in one of the covering opens, which identifies the stratum of the original
stratification it refines. The complementary strata are exactly what this last step has to rule
out, and a stratum with no points could not be ruled out, which is why the pruning is needed.

The converse direction cuts a stratum down to an affine open `W` by taking the open subscheme of
the stratum lying over `W`; the condition `P` survives because it is stable under inverse image
along the open immersion of that open subscheme.

## References

* [Stacks Project, Tag 095E](https://stacks.math.columbia.edu/tag/095E)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u w v t r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

section General

variable {D : Type w} [Category.{v} D]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)

/-- A condition closed under isomorphism holds for the inverse image along a composite as soon as
it holds for the iterated inverse image. -/
private theorem pred_pullback_comp_of_pred_pullback_pullback
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (G : Sheaf (SmallEtale.topology B Z.obj Z.property) D)
    (h : P X (((smallEtaleBaseChange B f).sheafPullback D
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)).obj
        (((smallEtaleBaseChange B g).sheafPullback D
          (SmallEtale.topology B Z.obj Z.property)
          (SmallEtale.topology B Y.obj Y.property)).obj G))) :
    P X (((smallEtaleBaseChange B (f ≫ g)).sheafPullback D
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B X.obj X.property)).obj G) :=
  hPIso _ ((smallEtaleSheafPullbackCompIso B X Y Z f g D).app G) h

/-- **The global stratification of Stacks 095E.** On a quasi-compact quasi-separated scheme, a
sheaf which is stratified by `P` on some quasi-compact open neighbourhood of every point is
stratified by `P` on a single constructible stratification of the whole scheme.

Finitely many of the given opens cover the scheme; each of their stratifications is enlarged to a
stratification of the whole scheme by adjoining the complement of the open it partitions, so that
all of them partition the same open subscheme and have a common refinement; the empty strata of
that refinement are discarded, so every remaining stratum has a point, that point lies in one of
the covering opens, and the stratum therefore refines a genuine stratum of that open's
stratification rather than its complementary one. -/
@[sga "4 IX 2.4" "Clause (i)"]
public theorem exists_constructibleStratification_top_of_locally
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (hPImmersion : ∀ (T T' : B.Scheme) (g : T' ⟶ T), IsImmersion (B.inclusion.map g) →
      ∀ G : Sheaf (SmallEtale.topology B T.obj T.property) D, P T G →
        P T' (((smallEtaleBaseChange B g).sheafPullback D
          (SmallEtale.topology B T.obj T.property)
          (SmallEtale.topology B T'.obj T'.property)).obj G))
    (Z : B.Scheme) [CompactSpace Z.obj] [QuasiSeparatedSpace Z.obj]
    (G : Sheaf (SmallEtale.topology B Z.obj Z.property) D)
    (hloc : ∀ z : Z.obj, ∃ (V : Z.obj.Opens) (_ : z ∈ V) (_ : IsCompact (V : Set Z.obj))
      (s : ConstructibleStratification B Z V), ∀ i,
        P (s.piece i) (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback D
          (SmallEtale.topology B Z.obj Z.property)
          (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj G)) :
    ∃ s : ConstructibleStratification B Z ⊤, ∀ i,
      P (s.piece i) (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback D
        (SmallEtale.topology B Z.obj Z.property)
        (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj G) := by
  classical
  choose V hmem hcpt s hs using hloc
  -- finitely many of the opens `V z` already cover `Z`
  obtain ⟨c, hc⟩ := isCompact_univ.elim_finite_subcover (fun z : Z.obj => (V z : Set Z.obj))
    (fun z => (V z).2) fun x _ => Set.mem_iUnion.mpr ⟨x, hmem x⟩
  let et : Fin c.card ≃ c := c.equivFin.symm
  let tt (j : Fin c.card) : ConstructibleStratification B Z ⊤ :=
    ConstructibleStratification.addComplement (V (et j)) (s (et j)) (hcpt (et j))
  -- each stratum of `tt j` either is the adjoined complement of `V (et j)` or carries `P`
  have hcases : ∀ (j : Fin c.card) (i : Fin (tt j).n),
      Set.range (B.inclusion.map ((tt j).inclusion i)).base ⊆ ((V (et j) : Set Z.obj)ᶜ) ∨
        P ((tt j).piece i) (((smallEtaleBaseChange B ((tt j).inclusion i)).sheafPullback D
          (SmallEtale.topology B Z.obj Z.property)
          (SmallEtale.topology B ((tt j).piece i).obj ((tt j).piece i).property)).obj G) :=
    fun j => Fin.cases (Or.inl (ConstructibleStratification.range_complementInclusion _).subset)
      fun i' => Or.inr (hs (et j) i')
  obtain ⟨r₀, hr₀⟩ := ConstructibleStratification.exists_refines_forall tt
  obtain ⟨r, hrr₀, hrne⟩ := ConstructibleStratification.exists_refines_nonempty r₀
  refine ⟨r, fun k => ?_⟩
  -- a point of the `k`-th stratum, and a covering open containing it
  obtain ⟨z, hz⟩ := hrne k
  obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp (hc (Set.mem_univ z))
  have hetj : ((et (c.equivFin ⟨y, hy⟩) : c) : Z.obj) = y :=
    congrArg Subtype.val (c.equivFin.symm_apply_apply ⟨y, hy⟩)
  obtain ⟨i, a, hai, hfac⟩ := (hrr₀.trans (hr₀ (c.equivFin ⟨y, hy⟩))) k
  have hsub : Set.range (B.inclusion.map (r.inclusion k)).base ⊆
      Set.range (B.inclusion.map ((tt (c.equivFin ⟨y, hy⟩)).inclusion i)).base := by
    rw [← hfac, ConstructibleStratification.range_map_comp]
    exact Set.image_subset_range _ _
  rcases hcases (c.equivFin ⟨y, hy⟩) i with hcompl | hP
  · exact (hcompl (hsub hz) (by rwa [hetj])).elim
  · rw [← hfac]
    exact pred_pullback_comp_of_pred_pullback_pullback B P hPIso a _ G
      (hPImmersion _ _ a hai _ hP)

/-- **A single stratification of the whole scheme makes a sheaf stratified.** This is the
implication (3) ⇒ (1) of Stacks 095E: the restriction of a global partition to an affine open is a
partition of that affine open, obtained by replacing each stratum by the open subscheme of it lying
over the affine open.

`P` survives that replacement because it is stable under inverse image along an immersion, an open
immersion being one. -/
public theorem isStratifiedSheaf_of_constructibleStratification_top
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (hPImmersion : ∀ (T T' : B.Scheme) (g : T' ⟶ T), IsImmersion (B.inclusion.map g) →
      ∀ G : Sheaf (SmallEtale.topology B T.obj T.property) D, P T G →
        P T' (((smallEtaleBaseChange B g).sheafPullback D
          (SmallEtale.topology B T.obj T.property)
          (SmallEtale.topology B T'.obj T'.property)).obj G))
    (Z : B.Scheme) [CompactSpace Z.obj] [QuasiSeparatedSpace Z.obj]
    (G : Sheaf (SmallEtale.topology B Z.obj Z.property) D)
    (s : ConstructibleStratification B Z ⊤)
    (hs : ∀ i, P (s.piece i) (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback D
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj G)) :
    IsStratifiedSheaf B Z P G := by
  intro W
  -- the part of the `i`-th stratum lying over `W`
  let O (i : Fin s.n) : (s.piece i).obj.Opens := B.inclusion.map (s.inclusion i) ⁻¹ᵁ W.1
  let Y (i : Fin s.n) : B.Scheme :=
    ⟨(O i).toScheme, lt_of_le_of_lt (Scheme.size_coe_opens_le (s.piece i).obj (O i))
      (s.piece i).property⟩
  let o (i : Fin s.n) : Y i ⟶ s.piece i := B.inclusion.preimage (O i).ι
  have homap (i : Fin s.n) : B.inclusion.map (o i) = (O i).ι := B.inclusion.map_preimage _
  have hoopen (i : Fin s.n) : IsOpenImmersion (B.inclusion.map (o i)) := by
    rw [homap]
    infer_instance
  have hoimm (i : Fin s.n) : IsImmersion (B.inclusion.map (o i)) := by
    have := hoopen i
    infer_instance
  have hrange (i : Fin s.n) :
      Set.range (B.inclusion.map (o i ≫ s.inclusion i)).base =
        Set.range (B.inclusion.map (s.inclusion i)).base ∩ (W.1 : Set Z.obj) := by
    rw [ConstructibleStratification.range_map_comp, homap, (O i).range_ι]
    exact Set.image_preimage_eq_inter_range.trans (Set.inter_comm _ _)
  have hconZ (i : Fin s.n) :
      Topology.IsConstructible (Set.range (B.inclusion.map (s.inclusion i)).base) :=
    (isConstructible_top_ι_preimage_iff (Y := Z.obj) _).mp (s.constructible i)
  refine ⟨{ n := s.n
            piece := Y
            inclusion := fun i => o i ≫ s.inclusion i
            isImmersion := fun i => by
              have h₁ := hoopen i
              have h₂ : IsImmersion (B.inclusion.map (s.inclusion i)) := s.isImmersion i
              simpa only [Functor.map_comp] using
                (inferInstance : IsImmersion
                  (B.inclusion.map (o i) ≫ B.inclusion.map (s.inclusion i)))
            contained := fun i => by rw [hrange]; exact Set.inter_subset_right
            constructible := fun i => by
              rw [hrange, Set.preimage_inter,
                show (W.1.ι.base ⁻¹' (W.1 : Set Z.obj)) = Set.univ from
                  Set.eq_univ_of_forall fun x => x.2, Set.inter_univ]
              exact (hconZ i).preimage_of_isOpenEmbedding W.1.isOpenEmbedding
            pairwise_disjoint := fun i i' hii' => by
              rw [hrange, hrange]
              exact (s.pairwise_disjoint i i' hii').mono Set.inter_subset_left
                Set.inter_subset_left
            covers := by
              have hu : ⋃ i, Set.range (B.inclusion.map (o i ≫ s.inclusion i)).base =
                  (⋃ i, Set.range (B.inclusion.map (s.inclusion i)).base) ∩
                    (W.1 : Set Z.obj) := by
                rw [Set.iUnion_inter]
                exact Set.iUnion_congr fun i => hrange i
              rw [hu, ← s.covers, TopologicalSpace.Opens.coe_top, Set.univ_inter] },
    fun i => ?_⟩
  exact pred_pullback_comp_of_pred_pullback_pullback B P hPIso (o i) _ G
    (hPImmersion _ _ (o i) (hoimm i) _ (hs i))

/-- **Tag 095E, (1) implies (2), for an arbitrary condition on the strata.** A stratified sheaf is
stratified on the one-member covering of the scheme by its identity.

Neither compactness nor quasi-separatedness of the scheme is needed for this direction, so it is
stated without them rather than read off `AlgebraicGeometry.isStratifiedSheaf_tfae`. -/
public theorem exists_openCover_isStratifiedSheaf
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (Z : B.Scheme) (F : Sheaf (SmallEtale.topology B Z.obj Z.property) D)
    (hF : IsStratifiedSheaf B Z P F) :
    ∃ (I : Type (u + 1)) (U : I → B.Scheme) (f : ∀ i, U i ⟶ Z),
      (∀ i, IsOpenImmersion (B.inclusion.map (f i))) ∧
      ((Set.univ : Set Z.obj) = ⋃ i, Set.range (B.inclusion.map (f i)).base) ∧
      ∀ i, IsStratifiedSheaf B (U i) P (smallEtalePullObj B (f i) F) := by
  refine ⟨PUnit.{u + 2}, fun _ => Z, fun _ => 𝟙 Z, fun _ => ?_, ?_, fun _ => ?_⟩
  · rw [CategoryTheory.Functor.map_id]
    infer_instance
  · refine Set.Subset.antisymm (fun x _ => Set.mem_iUnion.mpr ⟨PUnit.unit, ?_⟩)
      (Set.subset_univ _)
    simp
  · exact isStratifiedSheaf_congr B Z P hPIso
      ((smallEtaleSheafPullbackIdIso B Z D).app F).symm hF

/-- **Tag 095E, (2) implies (1), for an arbitrary condition on the strata.** If a sheaf on a
quasi-separated scheme restricts to a stratified sheaf on each member of a Zariski open covering,
it is a stratified sheaf.

An affine open of the scheme is covered by the images of affine opens of the members of the
covering; being quasi-compact it is covered by finitely many of them, each carrying a
stratification pushed forward from the member, and those glue.

Compactness of the scheme is not needed — only that of the affine open being stratified — and the
index type of the covering is arbitrary, so this direction is stated on its own rather than read
off `AlgebraicGeometry.isStratifiedSheaf_tfae`. -/
@[sga "4 IX 2.4" "Clause (ii)"]
public theorem isStratifiedSheaf_of_openCover_of_quasiSeparated
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (hPPull : ∀ (T' T : B.Scheme) (q : T' ⟶ T)
      (G : Sheaf (SmallEtale.topology B T.obj T.property) D),
      P T G → P T' (smallEtalePullObj B q G))
    (Z : B.Scheme) [QuasiSeparatedSpace Z.obj]
    (F : Sheaf (SmallEtale.topology B Z.obj Z.property) D)
    {I : Type*} (U : I → B.Scheme) (jm : ∀ k, U k ⟶ Z)
    (hj : ∀ k, IsOpenImmersion (B.inclusion.map (jm k)))
    (hcover : (Set.univ : Set Z.obj) = ⋃ k, Set.range (B.inclusion.map (jm k)).base)
    (hlocal : ∀ k, IsStratifiedSheaf B (U k) P (smallEtalePullObj B (jm k) F)) :
    IsStratifiedSheaf B Z P F := by
  classical
  have hjinst : ∀ k, IsOpenImmersion (B.inclusion.map (jm k)) := hj
  intro V
  let J := Σ k : I, {W : (U k).obj.affineOpens //
    ⇑(B.inclusion.map (jm k)).base '' ((W.1 : (U k).obj.Opens) : Set (U k).obj) ⊆
      ((V.1 : Z.obj.Opens) : Set Z.obj)}
  let O : J → Z.obj.Opens := fun a => (B.inclusion.map (jm a.1)) ''ᵁ a.2.1.1
  have hOcoe : ∀ a : J, ((O a : Z.obj.Opens) : Set Z.obj) =
      ⇑(B.inclusion.map (jm a.1)).base ''
        ((a.2.1.1 : (U a.1).obj.Opens) : Set (U a.1).obj) := fun a => by simp [O]
  have hOsub : ∀ a : J, ((O a : Z.obj.Opens) : Set Z.obj) ⊆
      ((V.1 : Z.obj.Opens) : Set Z.obj) := fun a => (hOcoe a) ▸ a.2.2
  have hOcomp : ∀ a : J, IsCompact ((O a : Z.obj.Opens) : Set Z.obj) := fun a =>
    (a.2.1.2.image_of_isOpenImmersion (B.inclusion.map (jm a.1))).isCompact
  have hcovV : ((V.1 : Z.obj.Opens) : Set Z.obj) ⊆
      ⋃ a : J, ((O a : Z.obj.Opens) : Set Z.obj) := by
    intro x hxV
    obtain ⟨k, z, hz⟩ := Set.mem_iUnion.mp (hcover ▸ Set.mem_univ x)
    have hzpre : z ∈ ((B.inclusion.map (jm k)) ⁻¹ᵁ V.1 : (U k).obj.Opens) := by
      change (B.inclusion.map (jm k)).base z ∈ ((V.1 : Z.obj.Opens) : Set Z.obj)
      rw [hz]
      exact hxV
    obtain ⟨S, hS, hzw, hWsub⟩ :=
      (U k).obj.isBasis_affineOpens.exists_subset_of_mem_open (a := z) hzpre
        ((B.inclusion.map (jm k)) ⁻¹ᵁ V.1).2
    obtain ⟨Wz, hWz, rfl⟩ := hS
    refine Set.mem_iUnion.mpr ⟨⟨k, ⟨⟨Wz, hWz⟩, ?_⟩⟩, ?_⟩
    · rintro w ⟨b, hb, rfl⟩
      exact hWsub hb
    · rw [hOcoe]
      exact ⟨z, hzw, hz⟩
  have hstrat : ∀ a : J, ∃ s : ConstructibleStratification B Z (O a),
      ∀ i, P (s.piece i) (smallEtalePullObj B (s.inclusion i) F) := by
    intro a
    obtain ⟨s0, hs0⟩ := hlocal a.1 a.2.1
    exact exists_constructibleStratification_image B Z P hPIso (jm a.1) (hj a.1) F
      a.2.1.1 (O a) (hOcoe a) s0 hs0
  obtain ⟨tf, htf⟩ := V.2.isCompact.elim_finite_subcover
    (fun a : J => ((O a : Z.obj.Opens) : Set Z.obj)) (fun a => (O a).2) hcovV
  refine exists_constructibleStratification_of_cover B Z P hPIso hPPull F V.1
    (O := fun b : Fin tf.card => O (tf.equivFin.symm b).1)
    (fun b => hOcomp _) (fun b => hOsub _) ?_
    (fun b => (hstrat (tf.equivFin.symm b).1).choose)
    (fun b => (hstrat (tf.equivFin.symm b).1).choose_spec)
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨a, hatf, hxa⟩ := Set.mem_iUnion₂.mp (htf hx)
    refine Set.mem_iUnion.mpr ⟨tf.equivFin ⟨a, hatf⟩, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact hxa
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
    exact hOsub _ hb

/-- **Stacks 095E for an arbitrary stratum condition.** On a quasi-compact quasi-separated scheme
the three conditions of Tag 095E are equivalent for any condition `P` on the strata which is closed
under isomorphism of sheaves and stable under inverse image along an immersion: being stratified by
`P`; being stratified by `P` after restriction to each member of some open cover; and admitting one
constructible stratification of the whole scheme with `P` on every stratum.

(1) ⇒ (2) is `AlgebraicGeometry.exists_openCover_isStratifiedSheaf`. (2) ⇒ (3) is
`AlgebraicGeometry.exists_constructibleStratification_top_of_locally`, whose local input is
supplied on the image of an affine open of a member of the cover, carried over by
`AlgebraicGeometry.ConstructibleStratification.pushOpenImmersion`. (3) ⇒ (1) is
`AlgebraicGeometry.isStratifiedSheaf_of_constructibleStratification_top`. -/
@[sga "4 IX 2.4" "more general"]
public theorem isStratifiedSheaf_tfae
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (hPImmersion : ∀ (T T' : B.Scheme) (g : T' ⟶ T), IsImmersion (B.inclusion.map g) →
      ∀ G : Sheaf (SmallEtale.topology B T.obj T.property) D, P T G →
        P T' (((smallEtaleBaseChange B g).sheafPullback D
          (SmallEtale.topology B T.obj T.property)
          (SmallEtale.topology B T'.obj T'.property)).obj G))
    (Z : B.Scheme) [CompactSpace Z.obj] [QuasiSeparatedSpace Z.obj]
    (G : Sheaf (SmallEtale.topology B Z.obj Z.property) D) :
    List.TFAE
      [ IsStratifiedSheaf B Z P G,
        ∃ (J : Type (u + 1)) (Y : J → B.Scheme) (g : ∀ j, Y j ⟶ Z),
          (∀ j, IsOpenImmersion (B.inclusion.map (g j))) ∧
          (Set.univ = ⋃ j, Set.range (B.inclusion.map (g j)).base) ∧
          ∀ j, IsStratifiedSheaf B (Y j) P
            (((smallEtaleBaseChange B (g j)).sheafPullback D
              (SmallEtale.topology B Z.obj Z.property)
              (SmallEtale.topology B (Y j).obj (Y j).property)).obj G),
        ∃ s : ConstructibleStratification B Z ⊤, ∀ i,
          P (s.piece i) (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback D
            (SmallEtale.topology B Z.obj Z.property)
            (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj G) ] := by
  classical
  tfae_have 1 → 2 := exists_openCover_isStratifiedSheaf B P hPIso Z G
  tfae_have 2 → 3 := by
    rintro ⟨J, Y, g, hg, hcover, hloc⟩
    refine exists_constructibleStratification_top_of_locally B P hPIso hPImmersion Z G
      fun z => ?_
    -- the point lies on a member of the cover; take an affine open of it around a preimage
    obtain ⟨j, w, hw⟩ := Set.mem_iUnion.mp (hcover ▸ Set.mem_univ z)
    have hgj : IsOpenImmersion (B.inclusion.map (g j)) := hg j
    obtain ⟨S, hS, hwS, -⟩ := (Y j).obj.isBasis_affineOpens.exists_subset_of_mem_open
      (a := w) (Set.mem_univ w) isOpen_univ
    obtain ⟨W', hW', rfl⟩ := hS
    obtain ⟨s', hs'⟩ := hloc j ⟨W', hW'⟩
    have hWaff : IsAffineOpen (B.inclusion.map (g j) ''ᵁ W') :=
      hW'.image_of_isOpenImmersion (B.inclusion.map (g j))
    exact ⟨B.inclusion.map (g j) ''ᵁ W', ⟨w, hwS, hw⟩, hWaff.isCompact,
      ConstructibleStratification.pushOpenImmersion (g j) hgj s' _ rfl hWaff.isCompact,
      fun i => pred_pullback_comp_of_pred_pullback_pullback B P hPIso _ _ G (hs' i)⟩
  tfae_have 3 → 1 := by
    rintro ⟨s, hs⟩
    exact isStratifiedSheaf_of_constructibleStratification_top B P hPIso hPImmersion Z G s hs
  tfae_finish

end General

section Finite

variable {A : Type w} [Category.{v} A] {FA : A → A → Type*} {CA : A → Type t}
  [∀ Q Q', FunLike (FA Q Q') (CA Q) (CA Q')] [ConcreteCategory.{t} A FA]
  [∀ (S : B.Scheme) (U : SmallEtale B S.obj S.property),
    HasWeakSheafify ((SmallEtale.topology B S.obj S.property).over U) A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S T : B.Scheme) (f : T ⟶ S) (X : SmallEtale B S.obj S.property),
    ((Over.post (X := X) (smallEtaleBaseChange B f)).sheafPushforwardContinuous A
      ((SmallEtale.topology B S.obj S.property).over X)
      ((SmallEtale.topology B T.obj T.property).over
        ((smallEtaleBaseChange B f).obj X))).IsRightAdjoint]

/-- **Stacks 095E for sheaves of sets and of abelian groups.** For a sheaf on the small étale site
of a quasi-compact quasi-separated scheme the following are equivalent: it is constructible; it is
constructible after restriction to each member of some open cover; and there is one constructible
stratification of the whole scheme on each stratum of which its inverse image is finite locally
constant.

Finite local constancy is closed under isomorphism and stable under inverse image along an
arbitrary morphism of small étale sites, by
`AlgebraicGeometry.isFiniteLocallyConstant_smallEtaleSheafPullback_of_overPost`, which is
Tag 093R, so `AlgebraicGeometry.isStratifiedSheaf_tfae` applies to it. -/
@[stacks 095E, sga "4 IX 2.4" "(i), (ii)"]
public theorem isConstructibleFiniteSheaf_tfae (Z : B.Scheme)
    [CompactSpace Z.obj] [QuasiSeparatedSpace Z.obj]
    (G : Sheaf (SmallEtale.topology B Z.obj Z.property) A) :
    List.TFAE
      [ IsConstructibleFiniteSheaf B Z G,
        ∃ (J : Type (u + 1)) (Y : J → B.Scheme) (g : ∀ j, Y j ⟶ Z),
          (∀ j, IsOpenImmersion (B.inclusion.map (g j))) ∧
          (Set.univ = ⋃ j, Set.range (B.inclusion.map (g j)).base) ∧
          ∀ j, IsConstructibleFiniteSheaf B (Y j)
            (((smallEtaleBaseChange B (g j)).sheafPullback A
              (SmallEtale.topology B Z.obj Z.property)
              (SmallEtale.topology B (Y j).obj (Y j).property)).obj G),
        ∃ s : ConstructibleStratification B Z ⊤, ∀ i,
          Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FA) (CD := CA)
            (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
            (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback A
              (SmallEtale.topology B Z.obj Z.property)
              (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj G) ] := by
  refine isStratifiedSheaf_tfae B (isFiniteLocallyConstantSmallEtale B (FA := FA) (CA := CA))
    ?_ ?_ Z G
  · intro T F' G' e h
    have := h
    exact Stacks.ConstantSheaf.isFiniteLocallyConstant_congr
      (SmallEtale.topology B T.obj T.property) e
  · intro _ _ g _ G' h
    have := h
    exact isFiniteLocallyConstant_smallEtaleSheafPullback_of_overPost B g G'

end Finite

section Modules

variable (R : Type r) [CommRing R] [IsNoetherianRing R]
  [∀ (S : B.Scheme) (U : SmallEtale B S.obj S.property),
    HasWeakSheafify ((SmallEtale.topology B S.obj S.property).over U) (ModuleCat.{w} R)]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} R)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S T : B.Scheme) (f : T ⟶ S) (X : SmallEtale B S.obj S.property),
    ((Over.post (X := X) (smallEtaleBaseChange B f)).sheafPushforwardContinuous (ModuleCat.{w} R)
      ((SmallEtale.topology B S.obj S.property).over X)
      ((SmallEtale.topology B T.obj T.property).over
        ((smallEtaleBaseChange B f).obj X))).IsRightAdjoint]

omit [IsNoetherianRing R] in
/-- For a sheaf of modules over a Noetherian ring on the small étale site of a quasi-compact
quasi-separated scheme the following are equivalent: it is constructible; it is constructible
after restriction to each member of some open cover; and there is one constructible stratification
of the whole scheme on each stratum of which its inverse image is locally constant with finitely
generated values. -/
@[stacks 095E, sga "4 IX 2.4" "special case"]
public theorem isConstructibleModuleSheaf_tfae (Z : B.Scheme)
    [CompactSpace Z.obj] [QuasiSeparatedSpace Z.obj]
    (G : Sheaf (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{w} R)) :
    List.TFAE
      [ IsConstructibleModuleSheaf B Z R G,
        ∃ (J : Type (u + 1)) (Y : J → B.Scheme) (g : ∀ j, Y j ⟶ Z),
          (∀ j, IsOpenImmersion (B.inclusion.map (g j))) ∧
          (Set.univ = ⋃ j, Set.range (B.inclusion.map (g j)).base) ∧
          ∀ j, IsConstructibleModuleSheaf B (Y j) R
            (((smallEtaleBaseChange B (g j)).sheafPullback (ModuleCat.{w} R)
              (SmallEtale.topology B Z.obj Z.property)
              (SmallEtale.topology B (Y j).obj (Y j).property)).obj G),
        ∃ s : ConstructibleStratification B Z ⊤, ∀ i,
          Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
            (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
            (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback (ModuleCat.{w} R)
              (SmallEtale.topology B Z.obj Z.property)
              (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj G) ] := by
  refine isStratifiedSheaf_tfae B
    (fun T G => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
      (SmallEtale.topology B T.obj T.property) G) ?_ ?_ Z G
  · intro T F' G' e h
    exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr
      (SmallEtale.topology B T.obj T.property) R e h
  · intro _ _ g _ G' h
    exact isFiniteTypeLocallyConstant_smallEtaleSheafPullback_of_overPost B g R G' h

end Modules

end AlgebraicGeometry

end
