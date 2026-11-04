module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.LimitPresentation
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Topologies.Vtopology.CoveringExistence
import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite

/-!
# Property (B) for integral morphisms

A morphism of schemes `f : X ⟶ Y` has *property (B)* when, for every étale `g : V ⟶ Y` and every
étale covering of `X ×ₗᵧ V`, there is an étale covering of `V` over each member of which the
corresponding fibre product breaks up as a disjoint union of pieces, one for each member of the
given covering, mapping to that member over `X ×ₗᵧ V`.

Property (B) for integral morphisms follows from property (B) for finite morphisms, given that an
integral morphism over an affine base is a directed limit of finite morphisms
([Stacks, Tag 04DR]).

## Main definitions

* `Stacks.EtaleCohomology.HasPropertyB` is property (B) for a morphism of schemes.

## Main results

* `Stacks.EtaleCohomology.exists_subordinate_decomposition_of_refinement` reindexes a
  decomposition built from a refinement of a covering by the covering's own index type.
* `Stacks.EtaleCohomology.hasPropertyB_of_etaleNeighborhood_decomposition` reduces property (B)
  to the production of one decomposition over an étale neighbourhood of each point of the base.
* `Stacks.EtaleCohomology.hasPropertyB_of_isIntegralHom_of_finite_case` is the dévissage: property
  (B) for finite morphisms implies property (B) for integral morphisms, given limit presentations
  of integral morphisms over affine bases.
* `Stacks.EtaleCohomology.hasPropertyB_of_isIntegralHom_of_finite`: property (B) for finite
  morphisms implies property (B) for integral morphisms.

## References

* [Stacks Project, Tag 04DP](https://stacks.math.columbia.edu/tag/04DP)
* [Stacks Project, Tag 04DR](https://stacks.math.columbia.edu/tag/04DR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- The part of a decomposition indexed by `J` that sits over one index `i` of the coarser index
type `I`. -/
noncomputable abbrev groupedPieces {I J : Type u} (h : J → I) (W : J → Scheme.{u}) (i : I) :=
  ∐ fun j : {j : J // h j = i} => W j.1

/-- **Regrouping a coproduct by an index map.** Summing the pieces over the fibres of `h` and then
over `I` gives back the coproduct over `J`. -/
noncomputable def groupedPiecesIso {I J : Type u} (h : J → I) (W : J → Scheme.{u}) :
    (∐ fun i : I => groupedPieces h W i) ≅ ∐ W := by
  refine ⟨Sigma.desc (fun i => Sigma.desc (fun j => Sigma.ι W j.1)),
    Sigma.desc (fun j => Sigma.ι (fun j' : {j' : J // h j' = h j} => W j'.1)
      ⟨j, rfl⟩ ≫ Sigma.ι (fun i : I => groupedPieces h W i) (h j)), ?_, ?_⟩
  · apply Sigma.hom_ext
    intro i
    apply Sigma.hom_ext
    intro j
    rcases j with ⟨j, rfl⟩
    simp [groupedPieces]
  · apply Sigma.hom_ext
    intro j
    simp [groupedPieces]

/-- The maps of a refinement, assembled on the regrouped coproducts. -/
noncomputable def groupedPiecesMap {I J : Type u} (h : J → I) (W : J → Scheme.{u})
    (B : I → Scheme.{u}) (a : ∀ j, W j ⟶ B (h j)) (i : I) : groupedPieces h W i ⟶ B i :=
  Sigma.desc fun j => a j.1 ≫ eqToHom (congrArg B j.2)

/-- Regrouping preserves a subordination equation on each individual piece. -/
theorem groupedPiecesMap_subordinate {I J : Type u} (h : J → I)
    (W : J → Scheme.{u}) (B : I → Scheme.{u}) (T Z : Scheme.{u})
    (e : (∐ W) ≅ T) (a : ∀ j, W j ⟶ B (h j)) (t : ∀ i, B i ⟶ Z) (q : T ⟶ Z)
    (ha : ∀ j, a j ≫ t (h j) = Sigma.ι W j ≫ e.hom ≫ q)
    (i : I) (j : {j : J // h j = i}) :
    Sigma.ι (fun j' : {j' : J // h j' = i} => W j'.1) j ≫ groupedPiecesMap h W B a i ≫ t i =
      Sigma.ι W j.1 ≫ e.hom ≫ q := by
  rcases j with ⟨j, rfl⟩
  simp [groupedPiecesMap, ha]

/-- **A decomposition refining a covering can be reindexed by the covering itself.** Given a
decomposition of `T` into pieces `W j` indexed by an arbitrary type `J`, each mapping to the member
`B (h j)` of a family indexed by `I` compatibly with maps `t i : B i ⟶ Z` and a comparison
`q : T ⟶ Z`, there is a decomposition of `T` indexed by `I` itself with the same compatibility. -/
theorem exists_subordinate_decomposition_of_refinement {I J : Type u} (h : J → I)
    (W : J → Scheme.{u}) (B : I → Scheme.{u}) (T Z : Scheme.{u})
    (e : (∐ W) ≅ T) (a : ∀ j, W j ⟶ B (h j)) (t : ∀ i, B i ⟶ Z) (q : T ⟶ Z)
    (ha : ∀ j, a j ≫ t (h j) = Sigma.ι W j ≫ e.hom ≫ q) :
    ∃ (A : I → Scheme.{u}) (e' : (∐ A) ≅ T) (b : ∀ i, A i ⟶ B i),
      ∀ i, b i ≫ t i = Sigma.ι A i ≫ e'.hom ≫ q := by
  refine ⟨fun i => groupedPieces h W i, (groupedPiecesIso h W).trans e, groupedPiecesMap h W B a,
    fun i => ?_⟩
  apply Sigma.hom_ext
  intro j
  rw [groupedPiecesMap_subordinate h W B T Z e a t q ha i j]
  simp [groupedPiecesIso]

/-- A precoverage of schemes cut out by a morphism property stable under base change is itself
stable under base change. -/
alias schemePrecoverageStableUnderBaseChange :=
  AlgebraicGeometry.schemePrecoverage_stableUnderBaseChange

/-- Finite disjoint unions of schemes remain disjoint unions after base change. -/
private noncomputable def baseChangeCoproductIso {J : Type u} [Finite J]
    {W : J → Scheme.{u}} {P T : Scheme.{u}} (e : (∐ W) ≅ P) (k : T ⟶ P) :
    (∐ fun j => pullback k (Sigma.ι W j ≫ e.hom)) ≅ T := by
  letI : Fintype J := Fintype.ofFinite J
  let eJ : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let W' : Fin (Fintype.card J) → Scheme.{u} := fun j => W (eJ.symm j)
  let w : ∀ j, W' (eJ j) ≅ W j := fun j => eqToIso (by simp [W'])
  let r : (∐ W) ≅ ∐ W' := Sigma.whiskerEquiv eJ w
  let e' : (∐ W') ≅ P := r.symm.trans e
  let π : ∀ j, W' j ⟶ P := fun j => Sigma.ι W' j ≫ e'.hom
  have hdesc : Sigma.desc π = e'.hom := by
    apply Sigma.hom_ext
    intro j
    simp [π]
  have hdescIso : IsIso (Sigma.desc π) := by
    rw [hdesc]
    infer_instance
  letI := hdescIso
  letI : IsIso (Sigma.desc fun j => pullback.fst k (π j)) :=
    FinitaryPreExtensive.isIso_sigmaDesc_fst π k hdescIso
  let A : J → Scheme.{u} := fun j => pullback k (Sigma.ι W j ≫ e.hom)
  let B : Fin (Fintype.card J) → Scheme.{u} := fun j => pullback k (π j)
  have hι (j : J) :
      Sigma.ι W' (eJ j) ≫ r.symm.hom = (w j).hom ≫ Sigma.ι W j := by
    dsimp [r, Sigma.whiskerEquiv, w, W']
    simp
  have hπ (j : J) : π (eJ j) = (w j).hom ≫ (Sigma.ι W j ≫ e.hom) := by
    change Sigma.ι W' (eJ j) ≫ r.symm.hom ≫ e.hom = _
    simpa [Category.assoc] using congrArg (fun x => x ≫ e.hom) (hι j)
  let wPB : ∀ j, B (eJ j) ≅ A j := fun j => by
    let v : W j ⟶ P := Sigma.ι W j ≫ e.hom
    let m := pullback.map k (π (eJ j)) k v (𝟙 T) (w j).hom (𝟙 P) (by simp) (hπ j)
    haveI : IsIso (w j).hom := by infer_instance
    haveI : IsIso m := by
      dsimp [m]
      apply pullback.map_isIso
    exact asIso m
  let hReindex : (∐ A) ≅ ∐ B := Sigma.whiskerEquiv eJ wPB
  exact hReindex.trans (asIso (Sigma.desc fun j => pullback.fst k (π j)))

private theorem baseChangeCoproductIso_ι {J : Type u} [Finite J]
    {W : J → Scheme.{u}} {P T : Scheme.{u}} (e : (∐ W) ≅ P) (k : T ⟶ P)
    (j : J) :
    Sigma.ι (fun j => pullback k (Sigma.ι W j ≫ e.hom)) j ≫
        (baseChangeCoproductIso e k).hom = pullback.fst k (Sigma.ι W j ≫ e.hom) := by
  classical
  simp [baseChangeCoproductIso, pullback.lift_fst]

/-- The étale precoverage of schemes is jointly surjective. -/
private theorem etalePrecoverage_jointlySurjective :
    Scheme.JointlySurjective Scheme.etalePrecoverage := by
  refine ⟨?_⟩
  intro X R hR x
  change R ∈ Scheme.precoverage @Etale X at hR
  rcases hR with ⟨hJ, _⟩
  change R ∈ Scheme.jointlySurjectivePrecoverage X at hJ
  rw [Scheme.jointlySurjectivePrecoverage,
    Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hJ
  exact hJ x

/-- **An étale covering of an affine scheme has a finite affine refinement**, whose members map
to members of the covering by open immersions. -/
theorem exists_finite_affine_etale_refinement {X : Scheme.{u}} [IsAffine X]
    (𝒰 : X.Cover.{u} Scheme.etalePrecoverage) :
    ∃ (𝒲 : X.AffineCover.{u} @Etale) (_hfin : Finite 𝒲.I₀)
      (r : 𝒲.cover ⟶ 𝒰), ∀ j, IsOpenImmersion (r.h₀ j) := by
  let : MorphismProperty.RespectsLeft (@Etale) @IsOpenImmersion := ⟨fun i hi f hf => by
    let : IsOpenImmersion i := hi
    let : Etale i := inferInstance
    let : Etale f := hf
    infer_instance⟩
  let : Scheme.JointlySurjective Scheme.etalePrecoverage := etalePrecoverage_jointlySurjective
  let : QuasiCompactCover 𝒰.toPreZeroHypercover := by
    apply AlgebraicGeometry.QuasiCompactCover.of_isOpenMap
    intro i
    have hEt : Etale (𝒰.f i) := 𝒰.map_prop i
    let : Flat (𝒰.f i) := (Etale.iff_flat_and_formallyUnramified.mp hEt).1
    let : LocallyOfFinitePresentation (𝒰.f i) :=
      (Etale.iff_flat_and_formallyUnramified.mp hEt).2.2
    exact Scheme.Hom.isOpenMap (𝒰.f i)
  obtain ⟨𝒲, r, hfin, hopen⟩ := AlgebraicGeometry.QuasiCompactCover.exists_hom 𝒰
  exact ⟨𝒲, hfin, r, hopen⟩

/-- **Every point of a scheme has an affine étale neighbourhood.** -/
theorem exists_affine_etale_neighborhood {V : Scheme.{u}} (v : V) :
    ∃ (N : EtaleNeighborhood V v), IsAffine N.scheme := by
  let 𝒜 := V.affineCover
  obtain ⟨x, hx⟩ := 𝒜.covers v
  let N : EtaleNeighborhood V v :=
    { scheme := 𝒜.X (𝒜.idx v)
      point := x
      toBase := 𝒜.f (𝒜.idx v)
      map_point := hx }
  refine ⟨N, ?_⟩
  dsimp [N]
  infer_instance

/-- The finite stages in an integral presentation over an affine base are affine. -/
private theorem affine_stage_of_integralLimitPresentation
    {X S : Scheme.{u}} {f : X ⟶ S} [IsAffine S]
    (p : IntegralLimitPresentation f) (i : p.indexType) :
    letI := p.indexPreorder
    letI := p.indexNonempty
    letI := p.indexDirected
    IsAffine (p.diagram.obj (Opposite.op i)) := by
  let := p.indexPreorder
  let := p.indexNonempty
  let := p.indexDirected
  let : IsAffine (((Functor.const p.indexTypeᵒᵖ).obj S).obj (Opposite.op i)) := by
    dsimp
    infer_instance
  let : IsFinite (p.structureMap.app (Opposite.op i)) := p.stageFinite (Opposite.op i)
  exact isAffine_of_isAffineHom (p.structureMap.app (Opposite.op i))

/-- Let `f : X ⟶ S` be an integral morphism of affine schemes. An étale covering of `X` has a
finite affine refinement by open immersions which is the base change of a finite affine étale
cover of a finite stage of a limit presentation of `f`. -/
private theorem exists_stage_etale_refinement
    (hpres : ∀ (X S : Scheme.{u}) (f : X ⟶ S), IsIntegralHom f → IsAffine S →
      IntegralLimitPresentation f)
    {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegralHom f] [IsAffine S] [IsAffine X]
    (𝒰 : X.Cover.{u} Scheme.etalePrecoverage) :
    ∃ (p : IntegralLimitPresentation f),
      letI := p.indexPreorder
      letI := p.indexNonempty
      letI := p.indexDirected
      ∃ (𝒲 : X.AffineCover.{u} @Etale) (_hfin : Finite 𝒲.I₀)
        (r : 𝒲.cover ⟶ 𝒰) (_hopen : ∀ j, IsOpenImmersion (r.h₀ j))
        (i : p.indexType) (𝒲ᵢ : (p.diagram.obj (Opposite.op i)).AffineCover.{u} @Etale)
        (_hfinᵢ : Finite 𝒲ᵢ.I₀) (e : 𝒲.I₀ ≃ 𝒲ᵢ.I₀),
        ∀ j, Nonempty (((Over.pullback (p.limitCone.app (Opposite.op i))).obj
          (Over.mk (𝒲ᵢ.f (e j)))) ≅ Over.mk
            (𝒲.f j)) := by
  obtain ⟨𝒲, hfin, r, hopen⟩ := exists_finite_affine_etale_refinement 𝒰
  let p := hpres X S f inferInstance inferInstance
  refine ⟨p, ?_⟩
  let := p.indexPreorder
  let := p.indexNonempty
  let := p.indexDirected
  let : ∀ i : p.indexTypeᵒᵖ, IsAffine (p.diagram.obj i) := fun i =>
    affine_stage_of_integralLimitPresentation p i.unop
  let : Finite 𝒲.I₀ := hfin
  obtain ⟨i, 𝒲ᵢ, hfinᵢ, e, he⟩ :=
    AlgebraicGeometry.exists_standardEtaleCovering_of_isLimit p.diagram
      (Cone.mk X p.limitCone) p.isLimit 𝒲
  exact ⟨𝒲, hfin, r, hopen, i.unop, 𝒲ᵢ, hfinᵢ, e, he⟩

/-- The morphism `Z ⟶ W` induced by `x : Z ⟶ X` and `wᵢ : Z ⟶ Wᵢ` agreeing over `Xᵢ`, where
`f : W ⟶ X` is identified with the base change of `fᵢ : Wᵢ ⟶ Xᵢ` along `c`. -/
private noncomputable def mapThroughRefinementIso
    {X Xᵢ W Wᵢ Z : Scheme.{u}} (c : X ⟶ Xᵢ) (fᵢ : Wᵢ ⟶ Xᵢ)
    (f : W ⟶ X)
    (e : Nonempty ((Over.pullback c).obj (Over.mk fᵢ) ≅ Over.mk f))
    (x : Z ⟶ X) (wᵢ : Z ⟶ Wᵢ) (hw : x ≫ c = wᵢ ≫ fᵢ) : Z ⟶ W := by
  let m : Z ⟶ pullback fᵢ c := pullback.lift wᵢ x hw.symm
  exact m ≫ (Classical.choice e).hom.left

/-- The morphism `mapThroughRefinementIso c fᵢ f e x wᵢ hw` lies over `x`. -/
private theorem mapThroughRefinementIso_over
    {X Xᵢ W Wᵢ Z : Scheme.{u}} (c : X ⟶ Xᵢ) (fᵢ : Wᵢ ⟶ Xᵢ)
    (f : W ⟶ X)
    (e : Nonempty ((Over.pullback c).obj (Over.mk fᵢ) ≅ Over.mk f))
    (x : Z ⟶ X) (wᵢ : Z ⟶ Wᵢ) (hw : x ≫ c = wᵢ ≫ fᵢ) :
    mapThroughRefinementIso c fᵢ f e x wᵢ hw ≫ f = x := by
  let ψ := Classical.choice e
  show (pullback.lift wᵢ x hw.symm ≫ ψ.hom.left) ≫ f = x
  have hψ : ψ.hom.left ≫ f = pullback.snd fᵢ c := by
    simpa using (Over.w ψ.hom)
  rw [Category.assoc, hψ, pullback.lift_snd]

/-- The canonical comparison from a further base change to the original pullback. -/
noncomputable def pullbackBaseChangeMap {X Y V W : Scheme.{u}}
    (f : X ⟶ Y) (g : V ⟶ Y) (n : W ⟶ V) :
    pullback f (n ≫ g) ⟶ pullback f g :=
  pullback.lift (pullback.fst f (n ≫ g)) (pullback.snd f (n ≫ g) ≫ n)
    (by rw [pullback.condition, Category.assoc])

/-- The comparison morphism of a further base change commutes with the projection to the first
factor. -/
@[reassoc (attr := simp)]
theorem pullbackBaseChangeMap_fst {X Y V W : Scheme.{u}}
    (f : X ⟶ Y) (g : V ⟶ Y) (n : W ⟶ V) :
    pullbackBaseChangeMap f g n ≫ pullback.fst f g = pullback.fst f (n ≫ g) :=
  pullback.lift_fst _ _ _

/-- The comparison morphism of a further base change carries the projection to the second factor
to that projection followed by the base change morphism. -/
@[reassoc (attr := simp)]
theorem pullbackBaseChangeMap_snd {X Y V W : Scheme.{u}}
    (f : X ⟶ Y) (g : V ⟶ Y) (n : W ⟶ V) :
    pullbackBaseChangeMap f g n ≫ pullback.snd f g =
      pullback.snd f (n ≫ g) ≫ n :=
  pullback.lift_snd _ _ _

/-- Property (B) for a morphism of schemes. Every étale covering after an étale base change
admits, after a further étale covering of the base, a componentwise subordinate disjoint-union
decomposition. -/
def HasPropertyB {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ {V : Scheme.{u}} (g : V ⟶ Y) [Etale g]
    (𝒰 : (pullback f g).Cover.{u} Scheme.etalePrecoverage),
    ∃ 𝒱 : V.Cover.{u} Scheme.etalePrecoverage, ∀ j,
      ∃ (q : pullback f (𝒱.f j ≫ g) ⟶ pullback f g),
        q ≫ pullback.fst f g = pullback.fst f (𝒱.f j ≫ g) ∧
        q ≫ pullback.snd f g = pullback.snd f (𝒱.f j ≫ g) ≫ 𝒱.f j ∧
      ∃ (W : 𝒰.I₀ → Scheme.{u}) (e : (∐ W) ≅ pullback f (𝒱.f j ≫ g))
          (a : ∀ i, W i ⟶ 𝒰.X i),
          ∀ i, a i ≫ 𝒰.f i = Sigma.ι W i ≫ e.hom ≫ q

/-- A morphism `f : X ⟶ Y` has property (B) as soon as, for every étale `g : V ⟶ Y`, every étale
covering `U` of `X ×ₗᵧ V` and every point `v` of `V`, there is a single étale neighborhood of `v`
over which `X ×ₗᵧ V` breaks up into pieces subordinate to `U`. -/
@[stacks 04DP]
theorem hasPropertyB_of_etaleNeighborhood_decomposition
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ {V : Scheme.{u}} (g : V ⟶ Y) [Etale g]
      (U : (pullback f g).Cover.{u} Scheme.etalePrecoverage) (v : V),
      ∃ (N : EtaleNeighborhood V v)
        (q : pullback f (N.toBase ≫ g) ⟶ pullback f g),
        q ≫ pullback.fst f g = pullback.fst f (N.toBase ≫ g) ∧
        q ≫ pullback.snd f g = pullback.snd f (N.toBase ≫ g) ≫ N.toBase ∧
        ∃ (W : U.I₀ → Scheme.{u}) (e : (∐ W) ≅ pullback f (N.toBase ≫ g))
          (a : ∀ i, W i ⟶ U.X i),
          ∀ i, a i ≫ U.f i = Sigma.ι W i ≫ e.hom ≫ q) :
    HasPropertyB f := by
  intro V g hg U
  choose N H using h g U
  exact ⟨Scheme.Cover.mkOfCovers V (fun v => (N v).scheme) (fun v => (N v).toBase)
    (fun v => ⟨v, (N v).point, (N v).map_point⟩), H⟩

/-- If finite morphisms have property (B), then every finite stage in an integral limit
presentation has property (B). -/
private theorem finite_stage_hasPropertyB
    (hFiniteB : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsFinite f → HasPropertyB f)
    {X S : Scheme.{u}} {f : X ⟶ S}
    (p : IntegralLimitPresentation f) (i : p.indexType) :
    letI := p.indexPreorder
    letI := p.indexNonempty
    letI := p.indexDirected
    HasPropertyB (p.structureMap.app (Opposite.op i)) := by
  let := p.indexPreorder
  let := p.indexNonempty
  let := p.indexDirected
  intro V g hg 𝒰
  exact hFiniteB _ _ _ (p.stageFinite (Opposite.op i)) g 𝒰

/-- The pullback of a map along the identity is canonically its source. -/
private noncomputable def pullbackRightIdIso {X S : Scheme.{u}} (f : X ⟶ S) :
    X ≅ pullback f (𝟙 S) := by
  letI : IsIso (pullback.fst f (𝟙 S)) := inferInstance
  exact (asIso (pullback.fst f (𝟙 S))).symm

@[simp]
private theorem pullbackRightIdIso_hom_fst {X S : Scheme.{u}} (f : X ⟶ S) :
    (pullbackRightIdIso f).hom ≫ pullback.fst f (𝟙 S) = 𝟙 X := by
  simp [pullbackRightIdIso]

/-- Transport an affine cover across the canonical identity-base-change isomorphism. -/
private noncomputable abbrev affineCoverOnRightIdPullback {X S : Scheme.{u}} (f : X ⟶ S)
    (𝒲 : X.AffineCover.{u} @Etale) :
    (pullback f (𝟙 S)).Cover.{u} Scheme.etalePrecoverage := by
  let e := pullbackRightIdIso f
  letI : Etale e.hom := inferInstance
  refine Scheme.Cover.mkOfCovers 𝒲.I₀ (fun i => Spec (𝒲.X i))
    (fun i => 𝒲.f i ≫ e.hom) ?_ ?_
  · intro z
    let i := 𝒲.idx (e.inv z)
    obtain ⟨x, hx⟩ := 𝒲.covers (e.inv z)
    refine ⟨i, x, ?_⟩
    change e.hom ((𝒲.f (𝒲.idx (e.inv z))) x) = z
    calc
      e.hom ((𝒲.f (𝒲.idx (e.inv z))) x) = e.hom (e.inv z) :=
        congrArg e.hom hx
      _ = z := by
        simp
  · intro i
    let : Etale (𝒲.f i) := 𝒲.map_prop i
    infer_instance

@[simp]
private theorem affineCoverOnRightIdPullback_f {X S : Scheme.{u}} (f : X ⟶ S)
    (𝒲 : X.AffineCover.{u} @Etale) (i : 𝒲.I₀) :
    (affineCoverOnRightIdPullback f 𝒲).f i = 𝒲.f i ≫ (pullbackRightIdIso f).hom := rfl

/-- If finite morphisms have property (B) and integral morphisms over affine bases have limit
presentations, then an integral morphism `f` admits, over an étale neighbourhood of every point
of `V`, a decomposition of `X ×ₗᵧ V` subordinate to a given étale covering `U`. -/
private theorem integral_has_local_decomposition
    (hpres : ∀ (X S : Scheme.{u}) (f : X ⟶ S), IsIntegralHom f → IsAffine S →
      IntegralLimitPresentation f)
    (hFiniteB : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsFinite f → HasPropertyB f)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    {V : Scheme.{u}} (g : V ⟶ Y) [Etale g]
    (U : (pullback f g).Cover.{u} Scheme.etalePrecoverage) (v : V) :
    ∃ (N : EtaleNeighborhood V v)
      (q : pullback f (N.toBase ≫ g) ⟶ pullback f g),
      q ≫ pullback.fst f g = pullback.fst f (N.toBase ≫ g) ∧
      q ≫ pullback.snd f g = pullback.snd f (N.toBase ≫ g) ≫ N.toBase ∧
      ∃ (W : U.I₀ → Scheme.{u}) (e : (∐ W) ≅ pullback f (N.toBase ≫ g))
        (a : ∀ i, W i ⟶ U.X i),
        ∀ i, a i ≫ U.f i = Sigma.ι W i ≫ e.hom ≫ q := by
  let : Scheme.JointlySurjective Scheme.etalePrecoverage := etalePrecoverage_jointlySurjective
  obtain ⟨N, hN⟩ := exists_affine_etale_neighborhood v
  let fb : N.scheme ⟶ Y := N.toBase ≫ g
  let fN : pullback f fb ⟶ N.scheme := pullback.snd f fb
  let : IsIntegralHom fN := inferInstance
  let : IsAffine N.scheme := hN
  let : IsAffine (pullback f fb) := isAffine_of_isAffineHom fN
  let qN : pullback f fb ⟶ pullback f g := pullbackBaseChangeMap f g N.toBase
  let : Scheme.IsJointlySurjectivePreserving @Etale :=
    Scheme.isJointlySurjectivePreserving @Etale
  let : MorphismProperty.IsStableUnderBaseChange (@Etale) :=
    Etale.etale_isStableUnderBaseChange
  let : Scheme.etalePrecoverage.IsStableUnderBaseChange :=
    schemePrecoverageStableUnderBaseChange @Etale
  let U' : (pullback f fb).Cover.{u} Scheme.etalePrecoverage := U.pullback₁ qN
  obtain ⟨p, W, hfin, r, hopen, i, Wᵢ, hfinᵢ, e, he⟩ :=
    exists_stage_etale_refinement hpres fN U'
  let := p.indexPreorder
  let := p.indexNonempty
  let := p.indexDirected
  let fᵢ := p.structureMap.app (Opposite.op i)
  let Uᵢ : (pullback fᵢ (𝟙 N.scheme)).Cover.{u} Scheme.etalePrecoverage :=
    affineCoverOnRightIdPullback fᵢ Wᵢ
  let : Finite Wᵢ.I₀ := hfinᵢ
  let : Finite Uᵢ.I₀ := hfinᵢ
  obtain ⟨𝒱, h𝒱⟩ := finite_stage_hasPropertyB hFiniteB p i (𝟙 N.scheme) Uᵢ
  obtain ⟨j, y, hy⟩ := 𝒱.exists_eq N.point
  obtain ⟨qᵢ, hqᵢ₁, hqᵢ₂, A, eᵢ, aᵢ, haᵢ⟩ := h𝒱 j
  let : Etale (𝒱.f j) := 𝒱.map_prop j
  let : Etale (𝒱.f j ≫ N.toBase) := Etale.etale_comp (𝒱.f j) N.toBase
  let N' : EtaleNeighborhood V v :=
    { scheme := 𝒱.X j
      point := y
      toBase := 𝒱.f j ≫ N.toBase
      map_point := (congrArg N.toBase hy).trans N.map_point }
  let t := 𝒱.f j
  have hBaseAssoc : t ≫ fb = N'.toBase ≫ g := by
    dsimp [fb, N']
    exact (Category.assoc _ _ _).symm
  let eAssoc : pullback f (t ≫ fb) ≅ pullback f (N'.toBase ≫ g) :=
    eqToIso (congrArg (fun h : 𝒱.X j ⟶ Y => pullback f h) hBaseAssoc)
  have hAssocInvFst : eAssoc.inv ≫ pullback.fst f (t ≫ fb) =
      pullback.fst f (N'.toBase ≫ g) := by
    dsimp [eAssoc]
    cases hBaseAssoc
    rfl
  have hAssocInvSnd : eAssoc.inv ≫ pullback.snd f (t ≫ fb) =
      pullback.snd f (N'.toBase ≫ g) := by
    dsimp [eAssoc]
    cases hBaseAssoc
    rfl
  let qMore : pullback f (t ≫ fb) ⟶ pullback f fb :=
    pullbackBaseChangeMap f fb t
  let c := p.limitCone.app (Opposite.op i)
  have hcompat : fN = c ≫ fᵢ := p.compatible (Opposite.op i)
  have hqMore : qMore ≫ fN = pullback.snd f (t ≫ fb) ≫ t := pullbackBaseChangeMap_snd f fb t
  let kStage : pullback f (t ≫ fb) ⟶ pullback fᵢ (t ≫ 𝟙 N.scheme) :=
    pullback.lift (qMore ≫ c) (pullback.snd f (t ≫ fb))
      (by rw [Category.assoc, ← hcompat, hqMore, Category.comp_id])
  let B : Wᵢ.I₀ → Scheme.{u} := fun l =>
    pullback kStage (Sigma.ι A l ≫ eᵢ.hom)
  let eLimit : (∐ B) ≅ pullback f (N'.toBase ≫ g) :=
    (baseChangeCoproductIso eᵢ kStage).trans eAssoc
  have hStageProj (l : Wᵢ.I₀) :
      aᵢ l ≫ Wᵢ.f l = Sigma.ι A l ≫ eᵢ.hom ≫
        pullback.fst fᵢ (t ≫ 𝟙 N.scheme) := by
    have hId : (pullbackRightIdIso fᵢ).hom ≫ pullback.fst fᵢ (𝟙 N.scheme) = 𝟙 _ :=
      pullbackRightIdIso_hom_fst fᵢ
    have hW : (Wᵢ.f l ≫ (pullbackRightIdIso fᵢ).hom) ≫ pullback.fst fᵢ (𝟙 N.scheme) =
        Wᵢ.f l := by
      rw [Category.assoc, hId, Category.comp_id]
    calc
      aᵢ l ≫ Wᵢ.f l = aᵢ l ≫ Uᵢ.f l ≫ pullback.fst fᵢ (𝟙 N.scheme) :=
        congrArg (fun m => aᵢ l ≫ m) hW.symm
      _ = Sigma.ι A l ≫ eᵢ.hom ≫ qᵢ ≫ pullback.fst fᵢ (𝟙 N.scheme) :=
        congrArg (fun m => m ≫ pullback.fst fᵢ (𝟙 N.scheme)) (haᵢ l)
      _ = Sigma.ι A l ≫ eᵢ.hom ≫ pullback.fst fᵢ (t ≫ 𝟙 N.scheme) := by rw [hqᵢ₁]
  have hOver (l : Wᵢ.I₀) :
      (pullback.fst kStage (Sigma.ι A l ≫ eᵢ.hom) ≫ qMore) ≫ c =
        (pullback.snd kStage (Sigma.ι A l ≫ eᵢ.hom) ≫ aᵢ l) ≫ Wᵢ.f l := by
    have hk : kStage ≫ pullback.fst fᵢ (t ≫ 𝟙 N.scheme) = qMore ≫ c := pullback.lift_fst _ _ _
    simp only [Category.assoc, ← hk, pullback.condition_assoc]
    exact (congrArg (pullback.snd kStage (Sigma.ι A l ≫ eᵢ.hom) ≫ ·) (hStageProj l).symm).trans
      (Category.assoc _ _ _).symm
  let xLim (l : Wᵢ.I₀) : B l ⟶ pullback f fb :=
    pullback.fst kStage (Sigma.ι A l ≫ eᵢ.hom) ≫ qMore
  let wStage (l : Wᵢ.I₀) : B l ⟶ Spec (Wᵢ.X l) :=
    pullback.snd kStage (Sigma.ι A l ≫ eᵢ.hom) ≫ aᵢ l
  have he' (l : Wᵢ.I₀) :
      Nonempty ((Over.pullback (p.limitCone.app (Opposite.op i))).obj
        (Over.mk (Wᵢ.f l)) ≅ Over.mk (W.f (e.symm l))) := by
    have hobj : (Over.pullback (p.limitCone.app (Opposite.op i))).obj
        (Over.mk (Wᵢ.f (e (e.symm l)))) =
        (Over.pullback (p.limitCone.app (Opposite.op i))).obj (Over.mk (Wᵢ.f l)) :=
      congrArg (fun k => (Over.pullback (p.limitCone.app (Opposite.op i))).obj
        (Over.mk (Wᵢ.f k))) (e.apply_symm_apply l)
    exact hobj ▸ he (e.symm l)
  let bFinal (l : Wᵢ.I₀) : B l ⟶ Spec (W.X (e.symm l)) :=
    mapThroughRefinementIso (p.limitCone.app (Opposite.op i)) (Wᵢ.f l)
      (W.f (e.symm l)) (he' l)
      (xLim l) (wStage l) (hOver l)
  let hIndex : Wᵢ.I₀ → U.I₀ := fun l => r.s₀ (e.symm l)
  let aFinal (l : Wᵢ.I₀) : B l ⟶ U.X (hIndex l) :=
      bFinal l ≫ r.h₀ (e.symm l) ≫ U.pullbackHom qN (hIndex l)
  let qFinal : pullback f (N'.toBase ≫ g) ⟶ pullback f g :=
    eAssoc.inv ≫ qMore ≫ qN
  have hqNfst : qN ≫ pullback.fst f g = pullback.fst f fb := pullbackBaseChangeMap_fst f g N.toBase
  have hqNsnd : qN ≫ pullback.snd f g = pullback.snd f fb ≫ N.toBase :=
    pullbackBaseChangeMap_snd f g N.toBase
  have hqFinalFst : qFinal ≫ pullback.fst f g = pullback.fst f (N'.toBase ≫ g) := by
    show eAssoc.inv ≫ pullbackBaseChangeMap f fb t ≫ qN ≫ pullback.fst f g = _
    rw [hqNfst, pullbackBaseChangeMap_fst, hAssocInvFst]
  have hqFinalSnd : qFinal ≫ pullback.snd f g =
      pullback.snd f (N'.toBase ≫ g) ≫ N'.toBase := by
    show eAssoc.inv ≫ pullbackBaseChangeMap f fb t ≫ qN ≫ pullback.snd f g = _
    rw [hqNsnd, pullbackBaseChangeMap_snd_assoc, reassoc_of% hAssocInvSnd]
  have hSub (l : Wᵢ.I₀) :
      aFinal l ≫ U.f (hIndex l) =
        Sigma.ι B l ≫ eLimit.hom ≫ qFinal := by
    have hPullbackHom : U.pullbackHom qN (hIndex l) ≫ U.f (hIndex l) = U'.f (hIndex l) ≫ qN :=
      pullback.condition.symm
    have hr : r.h₀ (e.symm l) ≫ U'.f (hIndex l) = W.f (e.symm l) := r.w₀ (e.symm l)
    have hMap : bFinal l ≫ W.f (e.symm l) = xLim l :=
      mapThroughRefinementIso_over c (Wᵢ.f l) (W.f (e.symm l)) (he' l) (xLim l) (wStage l)
        (hOver l)
    have hLimitι : Sigma.ι B l ≫ eLimit.hom =
        pullback.fst kStage (Sigma.ι A l ≫ eᵢ.hom) ≫ eAssoc.hom := by
      dsimp [eLimit]
      exact congrArg (fun m => m ≫ eAssoc.hom) (baseChangeCoproductIso_ι eᵢ kStage l)
    calc
      aFinal l ≫ U.f (hIndex l) = bFinal l ≫ r.h₀ (e.symm l) ≫ U'.f (hIndex l) ≫ qN :=
        congrArg (fun m => bFinal l ≫ r.h₀ (e.symm l) ≫ m) hPullbackHom
      _ = bFinal l ≫ W.f (e.symm l) ≫ qN := congrArg (fun m => bFinal l ≫ m) ((reassoc_of% hr) qN)
      _ = xLim l ≫ qN := (reassoc_of% hMap) qN
      _ = (pullback.fst kStage (Sigma.ι A l ≫ eᵢ.hom) ≫ eAssoc.hom) ≫ qFinal := by
        simp [xLim, qFinal]
      _ = Sigma.ι B l ≫ eLimit.hom ≫ qFinal := (congrArg (fun m => m ≫ qFinal) hLimitι).symm
  exact ⟨N', qFinal, hqFinalFst, hqFinalSnd, exists_subordinate_decomposition_of_refinement hIndex
    B U.X (pullback f (t ≫ fb)) (pullback f g) eLimit aFinal U.f qFinal hSub⟩

/-- **Dévissage for property (B).** If every finite morphism of schemes has property (B), and
every integral morphism with affine target admits a presentation as a directed limit of finite
morphisms, then every integral morphism of schemes has property (B). -/
theorem hasPropertyB_of_isIntegralHom_of_finite_case
    (hpres : ∀ (X S : Scheme.{u}) (f : X ⟶ S), IsIntegralHom f → IsAffine S →
      IntegralLimitPresentation f)
    (hFiniteB : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsFinite f → HasPropertyB f)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] :
    HasPropertyB f :=
  hasPropertyB_of_etaleNeighborhood_decomposition f fun g _ U v =>
    integral_has_local_decomposition hpres hFiniteB f g U v

/-- **The integral case of property (B) reduces to the finite case.** If every finite morphism of
schemes has property (B), then so does every integral morphism. -/
theorem hasPropertyB_of_isIntegralHom_of_finite
    (hFiniteB : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsFinite f → HasPropertyB f)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] :
    HasPropertyB f :=
  hasPropertyB_of_isIntegralHom_of_finite_case
    (fun _ _ g hg ha => @integralLimitPresentation _ _ g hg ha) hFiniteB f

end Stacks.EtaleCohomology

end
