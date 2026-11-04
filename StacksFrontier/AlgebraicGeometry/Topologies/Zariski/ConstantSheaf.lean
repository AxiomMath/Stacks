module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.ConstantGroupSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Comparison
public import StacksFrontier.AlgebraicGeometry.Topologies.Zariski.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites

/-!
# Constant sheaves on the big and small Zariski sites of a scheme

Let `B` be a big Zariski site containing a scheme `S` and let `G` be an abstract group. On the
big Zariski site of `S`, and on its small Zariski site, the sheafification of the constant
presheaf with value `G` has the locally constant `G`-valued maps as its sections, and the
constant sheaf of groups is the group-valued functor of points of the constant group scheme
`G_S`.

## Main results

* `AlgebraicGeometry.bigZariskiOver_openCoverData` and
  `AlgebraicGeometry.smallZariski_openCoverData` realise an arbitrary open cover of the scheme
  underlying a site object by a covering family of the site.
* `AlgebraicGeometry.constantSheafIsoLocallyConstantMaps_bigZariski` and
  `constantSheafIsoLocallyConstantMaps_smallZariski` identify the constant sheaves, and the
  two `_unit` lemmas fix those identifications on constant sections.
* `AlgebraicGeometry.constantGroupSheafRepresentedByConstantGroupScheme_bigZariski` and
  `constantGroupSheafRepresentedByConstantGroupScheme_smallZariski` are the representations of
  the constant group sheaves by `G_S`.

## Implementation notes

The chosen sites only contain schemes below their size cutoff and only the covering families
they selected, so an arbitrary open cover has to be replaced by a tautologically equivalent
covering family of the site; that is the content of Stacks 03WV, from which the covering data
of the two sites is assembled here.

## References

* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- A covering family of the chosen big category gives a covering family of the big Zariski
category of `S`, with the same underlying schemes. -/
public theorem bigZariskiOver_cover_sieve (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (T : BigZariskiOver B S hS) (V : PreZeroHypercover.{u + 1} T.left)
    (hV : B.IsCovering ⟨T.left, V⟩) :
    ∃ (W : V.I₀ → BigZariskiOver B S hS) (a : ∀ i, W i ⟶ T)
      (hobj : ∀ i, (BigZariskiOver.toScheme B S hS).obj (W i) = B.inclusion.obj (V.X i)),
      Sieve.ofArrows W a ∈ BigZariskiOver.topology B S hS T ∧
      (∀ i, eqToHom (hobj i) ≫ B.inclusion.map (V.f i) =
        (BigZariskiOver.toScheme B S hS).map (a i)) := by
  let W : V.I₀ → BigZariskiOver B S hS := fun i => Over.mk (V.f i ≫ T.hom)
  let a : ∀ i, W i ⟶ T := fun i => Over.homMk (V.f i) (by simp [W])
  let E : PreZeroHypercover T := { I₀ := V.I₀, X := W, f := a }
  refine ⟨W, a, fun i => by simp [W, BigZariskiOver.toScheme, BigZariskiOver.inclusion], ?_,
    fun i => by simp [W, a, BigZariskiOver.toScheme, BigZariskiOver.inclusion]⟩
  show Sieve.generate E.presieve₀ ∈ (BigZariskiOver.precoverage B S hS).toGrothendieck T
  exact (BigZariskiOver.precoverage B S hS).generate_mem_toGrothendieck ⟨E, rfl, hV⟩

/-- A morphism that factors through a member of the open cover attached to `U` lands in `U`. -/
private theorem apply_mem_of_comp_openCoverOfIsOpenCover {X Y : Scheme.{u}}
    (U : X → X.Opens) (hU : TopologicalSpace.IsOpenCover U) {b : X}
    (e : Y ≅ (X.openCoverOfIsOpenCover U hU).X b) (g : Y ⟶ X)
    (h : e.hom ≫ (X.openCoverOfIsOpenCover U hU).f b = g) (y : Y) : g y ∈ U b := by
  rw [← h]
  exact (e.hom y).property

/-- Every open cover of the scheme underlying an object of the big Zariski site of `S` is
refined by a covering family of that site. -/
public theorem bigZariskiOver_openCoverData (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    ∀ {T : BigZariskiOver B S hS}
      (U : (BigZariskiOver.toScheme B S hS).obj T →
        ((BigZariskiOver.toScheme B S hS).obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → BigZariskiOver B S hS) (a : ∀ i, W i ⟶ T)
        (r : I → (BigZariskiOver.toScheme B S hS).obj T),
        Sieve.ofArrows W a ∈ BigZariskiOver.topology B S hS T ∧
          ∀ i y, (BigZariskiOver.toScheme B S hS).map (a i) y ∈ U (r i) := by
  intro T U hU
  let O : ((BigZariskiOver.toScheme B S hS).obj T).OpenCover :=
    ((BigZariskiOver.toScheme B S hS).obj T).openCoverOfIsOpenCover U hU
  obtain ⟨V, hV, hEq⟩ :=
    BigZariskiSite.exists_isCovering_tautologicallyEquivalent_openCover B T.left O
  rcases hEq.2 with ⟨β, hβ⟩
  choose e he using hβ
  obtain ⟨W, a, hobj, hcover, hmap⟩ := bigZariskiOver_cover_sieve B S hS T V hV
  refine ⟨V.I₀, W, a, β, hcover, ?_⟩
  intro i y
  let y' := (eqToHom (hobj i)) y
  have hmap' : B.inclusion.map (V.f i) y' =
      (BigZariskiOver.toScheme B S hS).map (a i) y := by
    simpa [y'] using congrArg (fun f => f y) (hmap i)
  rw [← hmap']
  exact apply_mem_of_comp_openCoverOfIsOpenCover U hU (e i) _ (he i) y'

/-- An object of the big Zariski site of `S` with empty underlying scheme is covered by the
empty family. -/
public theorem bigZariskiOver_bottom_cover (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    ∀ {T : BigZariskiOver B S hS},
      IsEmpty ((BigZariskiOver.toScheme B S hS).obj T) →
        (⊥ : Sieve T) ∈ BigZariskiOver.topology B S hS T := by
  intro T hEmpty
  let X := (BigZariskiOver.toScheme B S hS).obj T
  let U : X → X.Opens := fun _ => ⊥
  have hU : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover]
    exact le_antisymm le_top fun x _ => (hEmpty.false x).elim
  let O : X.OpenCover := X.openCoverOfIsOpenCover U hU
  obtain ⟨V, hV, hEq⟩ :=
    BigZariskiSite.exists_isCovering_tautologicallyEquivalent_openCover B T.left O
  have hVI : IsEmpty V.I₀ := by
    rcases hEq.2 with ⟨β, _⟩
    exact ⟨fun i => hEmpty.false (β i)⟩
  obtain ⟨W, a, _, hcover, _⟩ := bigZariskiOver_cover_sieve B S hS T V hV
  have hbot : Sieve.ofArrows W a = (⊥ : Sieve T) := by
    ext Y f
    simp only [Sieve.bot_apply]
    refine ⟨fun hf => ?_, False.elim⟩
    obtain ⟨i, -, -⟩ := (Sieve.mem_ofArrows_iff W a f).mp hf
    exact hVI.false i
  rwa [← hbot]

/-- A covering family of the chosen big category by open immersions into an object of the small
Zariski site of `S` gives a covering family of that site, with the same underlying schemes. -/
public theorem smallZariski_cover_sieve (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (T : SmallZariski B S hS)
    (V : PreZeroHypercover.{u + 1} ((SmallZariski.inclusion B S hS).obj T).left)
    (hV : B.IsCovering ⟨((SmallZariski.inclusion B S hS).obj T).left, V⟩)
    (hVopen : ∀ i, IsOpenImmersion (B.inclusion.map (V.f i))) :
    ∃ (W : V.I₀ → SmallZariski B S hS) (a : ∀ i, W i ⟶ T)
      (hobj : ∀ i, (SmallZariski.toScheme B S hS).obj (W i) = B.inclusion.obj (V.X i)),
      Sieve.ofArrows W a ∈ SmallZariski.topology B S hS T ∧
      ∀ i y, (SmallZariski.toScheme B S hS).map (a i) y =
        B.inclusion.map (V.f i) ((eqToHom (hobj i)) y) := by
  let T' := (SmallZariski.inclusion B S hS).obj T
  let W' : V.I₀ → BigZariskiOver B S hS := fun i => Over.mk (V.f i ≫ T'.hom)
  let a' : ∀ i, W' i ⟶ T' := fun i => Over.homMk (V.f i) (by simp [W'])
  have hobj : ∀ i,
      (BigZariskiOver.toScheme B S hS).obj (W' i) = B.inclusion.obj (V.X i) := by
    intro i
    simp [W', BigZariskiOver.toScheme, BigZariskiOver.inclusion]
  have hmap : ∀ i, eqToHom (hobj i) ≫ B.inclusion.map (V.f i) =
      (BigZariskiOver.toScheme B S hS).map (a' i) := by
    intro i
    simp [W', a', BigZariskiOver.toScheme, BigZariskiOver.inclusion]
  have hWopen : ∀ i, IsOpenOver B S hS (W' i) := by
    intro i
    show IsOpenImmersion (B.inclusion.map (V.f i ≫ T'.hom))
    rw [Functor.map_comp]
    have : IsOpenImmersion (B.inclusion.map (V.f i)) := hVopen i
    have : IsOpenImmersion (B.inclusion.map T'.hom) := T.property
    exact IsOpenImmersion.comp (B.inclusion.map (V.f i)) (B.inclusion.map T'.hom)
  let W : V.I₀ → SmallZariski B S hS := fun i => ⟨W' i, hWopen i⟩
  let a : ∀ i, W i ⟶ T := fun i => (SmallZariski.inclusion B S hS).preimage (a' i)
  let E : PreZeroHypercover T := { I₀ := V.I₀, X := W, f := a }
  have ha : ∀ i, (SmallZariski.inclusion B S hS).map (a i) = a' i := fun i =>
    Functor.map_preimage (SmallZariski.inclusion B S hS) (a' i) (X := W i) (Y := T)
  have hEF : (E.map (SmallZariski.inclusion B S hS)).map
      (BigZariskiOver.inclusion B S hS) = V := by
    refine PreZeroHypercover.ext (x :=
      (E.map (SmallZariski.inclusion B S hS)).map (BigZariskiOver.inclusion B S hS))
      (y := V) rfl HEq.rfl (heq_of_eq ?_)
    funext i
    show (BigZariskiOver.inclusion B S hS).map
      ((SmallZariski.inclusion B S hS).map (a i)) = V.f i
    rw [ha i]
    rfl
  have hfamily : SmallZariski.IsCovering B S hS ⟨T, E⟩ := by
    show B.IsCovering ⟨T'.left,
      (E.map (SmallZariski.inclusion B S hS)).map (BigZariskiOver.inclusion B S hS)⟩
    rwa [hEF]
  refine ⟨W, a, hobj, ?_, fun i y => ?_⟩
  · show Sieve.generate E.presieve₀ ∈ (SmallZariski.precoverage B S hS).toGrothendieck T
    exact (SmallZariski.precoverage B S hS).generate_mem_toGrothendieck ⟨E, rfl, hfamily⟩
  · show (BigZariskiOver.toScheme B S hS).map
      ((SmallZariski.inclusion B S hS).map (a i)) y = _
    rw [ha i]
    exact (congrArg (fun f => f y) (hmap i)).symm

/-- Every open cover of the scheme underlying an object of the small Zariski site of `S` is
refined by a covering family of that site. -/
public theorem smallZariski_openCoverData (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    ∀ {T : SmallZariski B S hS}
      (U : (SmallZariski.toScheme B S hS).obj T →
        ((SmallZariski.toScheme B S hS).obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → SmallZariski B S hS) (a : ∀ i, W i ⟶ T)
        (r : I → (SmallZariski.toScheme B S hS).obj T),
        Sieve.ofArrows W a ∈ SmallZariski.topology B S hS T ∧
          ∀ i y, (SmallZariski.toScheme B S hS).map (a i) y ∈ U (r i) := by
  intro T U hU
  let T' := (SmallZariski.inclusion B S hS).obj T
  let X := B.inclusion.obj T'.left
  change TopologicalSpace.IsOpenCover (X := X) U at hU
  let O : X.OpenCover := X.openCoverOfIsOpenCover U hU
  obtain ⟨V, hV, hEq⟩ :=
    BigZariskiSite.exists_isCovering_tautologicallyEquivalent_openCover B T'.left O
  rcases hEq.2 with ⟨β, hβ⟩
  choose e he using hβ
  have hVopen : ∀ i, IsOpenImmersion ((B.inclusion.map (V.f i))) := by
    intro i
    have h : IsOpenImmersion ((e i).hom ≫ O.f (β i)) := by infer_instance
    rwa [he i] at h
  obtain ⟨W, a, hobj, hcover, hpoint⟩ := smallZariski_cover_sieve B S hS T V hV hVopen
  refine ⟨V.I₀, W, a, β, hcover, fun i y => ?_⟩
  rw [hpoint]
  exact apply_mem_of_comp_openCoverOfIsOpenCover U hU (e i) _ (he i) _

/-- Locally constant `G`-valued maps form a sheaf on the big Zariski site of `S`. -/
public theorem locallyConstantMaps_isSheaf_bigZariski (B : BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Group G] :
    Presheaf.IsSheaf (BigZariskiOver.topology B S hS)
      ((BigZariskiOver.toScheme B S hS).op ⋙
        locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  isSheaf_bigZariski_of_isSheaf_fpqc B S hS (locallyConstantMapsOver G S ⋙ forget GrpCat)
    (locallyConstantMapsOver_isSheaf_fpqc S G)

/-- Locally constant `G`-valued maps form a sheaf on the small Zariski site of `S`. -/
public theorem locallyConstantMaps_isSheaf_smallZariski (B : BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Group G] :
    Presheaf.IsSheaf (SmallZariski.topology B S hS)
      ((SmallZariski.toScheme B S hS).op ⋙
        locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  isSheaf_smallZariski_of_isSheaf_fpqc B S hS (locallyConstantMapsOver G S ⋙ forget GrpCat)
    (locallyConstantMapsOver_isSheaf_fpqc S G)

/-- Constant sheaves on the chosen big Zariski site have locally constant sections. -/
@[stacks 03P5 "big Zariski site"]
public def constantSheafIsoLocallyConstantMaps_bigZariski (B : BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ((constantSheaf (BigZariskiOver.topology B S hS)
      (Type (max (u + 1) v))).obj G).obj ≅
    ((BigZariskiOver.toScheme B S hS).op ⋙
      locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  constantSheafIsoLocallyConstantMapsOn (BigZariskiOver.toScheme B S hS) G
    (BigZariskiOver.topology B S hS) (bigZariskiOver_openCoverData B S hS)
    (bigZariskiOver_bottom_cover B S hS) (locallyConstantMaps_isSheaf_bigZariski B S hS G)

/-- Constant sheaves on the chosen small Zariski site have locally constant sections. -/
@[stacks 03P5 "small Zariski site"]
public def constantSheafIsoLocallyConstantMaps_smallZariski (B : BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ((constantSheaf (SmallZariski.topology B S hS) (Type (max (u + 1) v))).obj G).obj ≅
    ((SmallZariski.toScheme B S hS).op ⋙
      locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  constantSheafIsoLocallyConstantMapsOn (SmallZariski.toScheme B S hS) G
    (SmallZariski.topology B S hS) (smallZariski_openCoverData B S hS)
    (openCoverData_bottom (SmallZariski.toScheme B S hS) (SmallZariski.topology B S hS)
      (smallZariski_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_smallZariski B S hS G)

/-- The big Zariski identification preserves constant sections. -/
@[stacks 03P5 "unit on the big Zariski site"]
public theorem constantSheafIsoLocallyConstantMaps_bigZariski_unit (B : BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ConstantSheafIso.UnitCompatible (BigZariskiOver.toScheme B S hS)
      (BigZariskiOver.topology B S hS) G
      (constantSheafIsoLocallyConstantMaps_bigZariski B S hS G) :=
  constantSheafIsoLocallyConstantMapsOn_unit (BigZariskiOver.toScheme B S hS) G
    (BigZariskiOver.topology B S hS) (bigZariskiOver_openCoverData B S hS)
    (bigZariskiOver_bottom_cover B S hS) (locallyConstantMaps_isSheaf_bigZariski B S hS G)

/-- The small Zariski identification preserves constant sections. -/
@[stacks 03P5 "unit on the small Zariski site"]
public theorem constantSheafIsoLocallyConstantMaps_smallZariski_unit (B : BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ConstantSheafIso.UnitCompatible (SmallZariski.toScheme B S hS)
      (SmallZariski.topology B S hS) G
      (constantSheafIsoLocallyConstantMaps_smallZariski B S hS G) :=
  constantSheafIsoLocallyConstantMapsOn_unit (SmallZariski.toScheme B S hS) G
    (SmallZariski.topology B S hS) (smallZariski_openCoverData B S hS)
    (openCoverData_bottom (SmallZariski.toScheme B S hS) (SmallZariski.topology B S hS)
      (smallZariski_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_smallZariski B S hS G)

/-- Representation of the constant group sheaf on the chosen big Zariski site. -/
@[stacks 03P5 "group-valued representation on the big Zariski site"]
public def constantGroupSheafRepresentedByConstantGroupScheme_bigZariski
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    GroupSheafRepresentation S (Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion)
      (BigZariskiOver.topology B S hS) G := by
  let H := Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion
  let J := BigZariskiOver.topology B S hS
  have hSet : Presheaf.IsSheaf J
      (H.op ⋙ locallyConstantMapsOver G S ⋙ forget GrpCat) :=
    isSheaf_bigZariski_of_isSheaf_fpqc B S hS (locallyConstantMapsOver G S ⋙ forget GrpCat)
      (locallyConstantMapsOver_isSheaf_fpqc S G)
  let : HasSheafify J GrpCat.{max (u + 1) v} := hasSheafify_grpCat J
  let : J.WEqualsLocallyBijective GrpCat.{max (u + 1) v} := wEqualsLocallyBijective_grpCat J
  have hOpen := @bigZariskiOver_openCoverData B S hS
  exact groupSheafRepresentationOfLocallyConstantMaps.{u, v} S H J G hOpen
    (openCoverData_bottom (H ⋙ Over.forget S) J hOpen) hSet

/-- Representation of the constant group sheaf on the chosen small Zariski site. -/
@[stacks 03P5 "group-valued representation on the small Zariski site"]
public def constantGroupSheafRepresentedByConstantGroupScheme_smallZariski
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    GroupSheafRepresentation S
      (SmallZariski.inclusion B S hS ⋙
        Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion)
      (SmallZariski.topology B S hS) G := by
  let H := SmallZariski.inclusion B S hS ⋙
    Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion
  let J := SmallZariski.topology B S hS
  have hSet : Presheaf.IsSheaf J
      (H.op ⋙ locallyConstantMapsOver G S ⋙ forget GrpCat) :=
    isSheaf_smallZariski_of_isSheaf_fpqc B S hS (locallyConstantMapsOver G S ⋙ forget GrpCat)
      (locallyConstantMapsOver_isSheaf_fpqc S G)
  let : HasSheafify J GrpCat.{max (u + 1) v} := hasSheafify_grpCat J
  let : J.WEqualsLocallyBijective GrpCat.{max (u + 1) v} := wEqualsLocallyBijective_grpCat J
  have hOpen := @smallZariski_openCoverData B S hS
  exact groupSheafRepresentationOfLocallyConstantMaps.{u, v} S H J G hOpen
    (openCoverData_bottom (H ⋙ Over.forget S) J hOpen) hSet

end AlgebraicGeometry

end
