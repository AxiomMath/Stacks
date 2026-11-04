module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.FieldValued
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.Reduced
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleEnlargementOfOpen.PointsAndDensity

/-!
# The elementary distinguished square of an etale chart, and coproduct covers

Auxiliary results for the enlargement of a dense open subspace of a Noetherian algebraic space by
an affine etale chart (Stacks 0F4C): the elementary distinguished square produced by an etale
chart of a stratum, the binary coproduct cover of the big fppf site, and the Zariski locality of
etaleness on the source of a morphism out of a representable.

## Main results

* `AlgebraicGeometry.Space.elementaryDistinguishedSquare_of_etale_neighborhood`: the elementary
  distinguished square produced by an etale chart of a stratum.
* `AlgebraicGeometry.Space.binary_coproduct_cover`: the two inclusions into a coproduct in the
  big fppf site are monomorphisms, generate a covering sieve and are disjoint.
* `AlgebraicGeometry.Space.isEtale_of_scheme_openCover`: etaleness of a morphism out of a
  representable is Zariski local on the source.

## References

* [Stacks Project, Tag 0F4C](https://stacks.math.columbia.edu/tag/0F4C)
* [Stacks Project, Tag 07ST](https://stacks.math.columbia.edu/tag/07ST)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space


/-- The elementary distinguished square produced by an étale chart of a stratum. If an open
subspace `A` of `X` carries a closed subspace `T` whose points are those of `A` outside `U`,
and an étale `f : Y ⟶ A` restricts to an isomorphism over `T`, then the restriction of `f`
to an open `Y' ⊆ Y` whose image together with `U` is `W` makes `(U ⊆ W, Y' ⟶ W)` an
elementary distinguished square. -/
theorem elementaryDistinguishedSquare_of_etale_neighborhood
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Y' : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hY' : AlgebraicGeometry.IsAlgebraicSpace B S hS Y')
    (U A W : Subfunctor X)
    (hU : AlgebraicGeometry.Space.IsOpenSubspace B S hS U)
    (hA : AlgebraicGeometry.Space.IsOpenSubspace B S hS A)
    (hW : AlgebraicGeometry.Space.IsOpenSubspace B S hS W) (hUW : U ≤ W)
    (T : Subfunctor A.toFunctor) (hT : AlgebraicGeometry.Space.IsClosedSubspace B S hS T)
    (f : Y ⟶ A.toFunctor) (hf : AlgebraicGeometry.Space.IsEtale B S hS f)
    (j : Y' ⟶ Y) (hj : AlgebraicGeometry.Space.IsOpenImmersion B S hS j)
    (f' : Y' ⟶ W.toFunctor) (hfac : f' ≫ W.ι = j ≫ f ≫ A.ι)
    (hcover : Set.range (AlgebraicGeometry.Space.pointsMap B S hS W.toFunctor W.ι) =
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι) ∪
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS Y' (f' ≫ W.ι)))
    (hstratum : Set.range (AlgebraicGeometry.Space.pointsMap B S hS A.toFunctor A.ι) \
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι) ⊆
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS T.toFunctor (T.ι ≫ A.ι)))
    [IsIso (pullback.fst T.ι f)] :
    AlgebraicGeometry.Space.IsElementaryDistinguishedSquare B S hS hW.1
      (Subfunctor.range (Subfunctor.homOfLe hUW)) f' := by
  classical
  let C := Subfunctor.range (Subfunctor.homOfLe hUW)
  have hC : AlgebraicGeometry.Space.IsOpenSubspace B S hS C :=
    AlgebraicGeometry.Space.isOpenSubspace_of_le B S hS U W hU hUW
  let := AlgebraicGeometry.Space.pointTopology B S hS W.toFunctor
  have hclosed : IsClosed
      (Set.range (AlgebraicGeometry.Space.pointsMap B S hS C.toFunctor C.ι))ᶜ := by
    apply isClosed_compl_iff.mpr
    rw [← AlgebraicGeometry.Space.openSubspacesOrderIso_apply
      B S hS W.toFunctor hW.1 ⟨C, hC⟩]
    exact (AlgebraicGeometry.Space.openSubspacesOrderIso
      B S hS W.toFunctor hW.1 ⟨C, hC⟩).2
  let Z := AlgebraicGeometry.Space.reducedClosedSubspace B S hS W.toFunctor hW.1 _ hclosed
  have hZclosed := AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace
    B S hS W.toFunctor hW.1 _ hclosed
  have hZrangeEq := AlgebraicGeometry.Space.range_pointsMap_ι_reducedClosedSubspace
    B S hS W.toFunctor hW.1 _ hclosed
  have hZred := AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace
    B S hS W.toFunctor hW.1 _ hclosed
  have hZavoid (z : AlgebraicGeometry.Space.points B S hS Z.toFunctor) :
      AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor (Z.ι ≫ W.ι) z ∉
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι) := by
    rintro ⟨v, hv⟩
    let k := Subfunctor.homOfLe hUW
    have heq : AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor k v =
        AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor Z.ι z := by
      apply AlgebraicGeometry.Space.pointsMap_injective_of_mono B S hS W.ι
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, Subfunctor.homOfLe_ι]
      exact hv
    have hz : AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor Z.ι z ∉
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS C.toFunctor C.ι) := by
      have hz := hZrangeEq ▸ (Set.mem_range_self z :
        AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor Z.ι z ∈
          Set.range (AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor Z.ι))
      exact hz
    apply hz
    refine ⟨AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor (Subfunctor.toRange k) v, ?_⟩
    rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]
    exact heq
  have hZrange (z : AlgebraicGeometry.Space.points B S hS Z.toFunctor) :
      AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor (Z.ι ≫ W.ι) z ∈
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS Y' (f' ≫ W.ι)) := by
    have hz : AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor (Z.ι ≫ W.ι) z ∈
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS W.toFunctor W.ι) :=
      ⟨AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor Z.ι z,
        (pointsMap_comp_apply _ _ _ _ _ z).symm⟩
    rw [hcover] at hz
    exact hz.resolve_left (hZavoid z)
  obtain ⟨a, ha⟩ := (AlgebraicGeometry.Space.factorsThrough_openSubspace_iff_points
    B S hS hX hZclosed.1 A hA (Z.ι ≫ W.ι)).2 (by
      rintro x ⟨z, rfl⟩
      obtain ⟨v, hv⟩ := hZrange z
      refine ⟨AlgebraicGeometry.Space.pointsMap B S hS Y' (j ≫ f) v, ?_⟩
      rw [← pointsMap_comp_apply, Category.assoc, ← hfac]
      exact hv)
  obtain ⟨b, hb⟩ := (AlgebraicGeometry.Space.exists_lift_closedSubspace_iff_pointsMap_range_subset
    B S hS hA.1 hZclosed.1 T hT hZred a).2 (by
      rintro x ⟨z, rfl⟩
      have hz : AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor (Z.ι ≫ W.ι) z ∈
          Set.range (AlgebraicGeometry.Space.pointsMap B S hS A.toFunctor A.ι) :=
        ⟨AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor a z,
          by rw [← pointsMap_comp_apply, ha]⟩
      obtain ⟨t, ht⟩ := hstratum ⟨hz, hZavoid z⟩
      refine ⟨t, ?_⟩
      apply AlgebraicGeometry.Space.pointsMap_injective_of_mono B S hS A.ι
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, ha]
      exact ht)
  let P := pullback T.ι f
  let p : P ⟶ T.toFunctor := pullback.fst T.ι f
  let q : P ⟶ Y := pullback.snd T.ι f
  let l : Z.toFunctor ⟶ P := b ≫ inv p
  let g : Z.toFunctor ⟶ Y := l ≫ q
  have hl : l ≫ p = b := by simp [l]
  have hgf : g ≫ f = a := by
    show (l ≫ q) ≫ f = a
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hl, hb]
  have hgin : Set.range (AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor g) ⊆
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS Y' j) := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨v, hv⟩ := hZrange z
    let PP : AlgebraicGeometry.AlgebraicSpaces B S hS :=
      ⟨P, AlgebraicGeometry.isAlgebraicSpace_pullback B S hS T.ι f hT.1 hY hA.1⟩
    let TT : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨T.toFunctor, hT.1⟩
    let YY : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨Y, hY⟩
    let AA : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨A.toFunctor, hA.1⟩
    have hpb : IsPullback (ObjectProperty.homMk p : PP ⟶ TT)
        (ObjectProperty.homMk q : PP ⟶ YY)
        (ObjectProperty.homMk T.ι : TT ⟶ AA) (ObjectProperty.homMk f : YY ⟶ AA) := by
      apply IsPullback.of_map_of_faithful
        (F := ObjectProperty.ι (AlgebraicGeometry.IsAlgebraicSpace B S hS))
      exact IsPullback.of_hasPullback T.ι f
    obtain ⟨r, hrp, hrq⟩ := AlgebraicGeometry.Space.exists_point_of_isPullback B S hS hpb
      (AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor b z)
      (AlgebraicGeometry.Space.pointsMap B S hS Y' j v) (by
        show AlgebraicGeometry.Space.pointsMap B S hS T.toFunctor T.ι
          (AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor b z) =
          AlgebraicGeometry.Space.pointsMap B S hS Y f
            (AlgebraicGeometry.Space.pointsMap B S hS Y' j v)
        apply AlgebraicGeometry.Space.pointsMap_injective_of_mono B S hS A.ι
        rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, ← pointsMap_comp_apply,
          ← pointsMap_comp_apply, ← Category.assoc b, hb, ha, ← hfac]
        exact hv.symm)
    have hr : AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor l z = r := by
      apply AlgebraicGeometry.Space.pointsMap_injective_of_mono B S hS p
      rw [← pointsMap_comp_apply, hl]
      exact hrp.symm
    refine ⟨v, ?_⟩
    rw [pointsMap_comp_apply _ _ _ l q z, hr]
    exact hrq.symm
  obtain ⟨g', hg'⟩ := factorsThrough_isOpenImmersion B S hS hY hZclosed.1 j hj g hgin
  have hg'f : g' ≫ f' = Z.ι := by
    apply (cancel_mono W.ι).mp
    rw [Category.assoc, hfac, ← Category.assoc g' j, hg', ← Category.assoc g f,
      hgf, ha]
  let N := Z.preimage f'
  let n := Z.fromPreimage f'
  have hn := CategoryTheory.Subfunctor.isPullback_preimage f' Z
  have heq : (n ≫ b) ≫ T.ι = (N.ι ≫ j) ≫ f := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc n b, hb, Category.assoc, ha, ← Category.assoc,
      hn.w, Category.assoc, hfac]
    simp only [Category.assoc, N]
  let k : N.toFunctor ⟶ P := pullback.lift (n ≫ b) (N.ι ≫ j) heq
  have hkp : k ≫ p = n ≫ b := pullback.lift_fst _ _ _
  have hkq : k ≫ q = N.ι ≫ j := pullback.lift_snd _ _ _
  have hk : k = n ≫ l := by
    apply (cancel_mono p).mp
    rw [Category.assoc, hl, hkp]
  have hnG : n ≫ g' = N.ι := by
    let : Mono j := mono_of_isOpenImmersion B S hS j hj
    apply (cancel_mono j).mp
    rw [Category.assoc, hg']
    show n ≫ (l ≫ q) = N.ι ≫ j
    rw [← Category.assoc, ← hk, hkq]
  have hIso : IsIso n := isIso_fromPreimage_of_section f' Z g' hg'f hnG
  have hfX : AlgebraicGeometry.Space.IsEtale B S hS (j ≫ f ≫ A.ι) :=
    isEtale_comp_aux j (f ≫ A.ι) (isEtale_of_isOpenImmersion_aux hj)
      (isEtale_comp_aux f A.ι hf (isEtale_of_isOpenImmersion_aux hA.2))
  have hf' : AlgebraicGeometry.Space.IsEtale B S hS f' :=
    AlgebraicGeometry.Space.isEtale_of_isEtale_over B S hS hY' hW.1 hX f'
      (j ≫ f ≫ A.ι) W.ι hfX (isEtale_of_isOpenImmersion_aux hW.2) hfac
  exact ⟨hY', hC, hf', hclosed, hIso⟩

/-- A family of morphisms of the big fppf site over `S` whose underlying family of schemes
is an fppf covering generates a covering sieve of the induced topology. -/
private lemma sieve_mem_of_fppf
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V : AlgebraicGeometry.BigFppfOver B S hS} (E : PreZeroHypercover.{u + 1} V)
    (hE : (E.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presieve₀ ∈
      Scheme.fppfPrecoverage ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V)) :
    E.sieve₀ ∈ AlgebraicGeometry.BigFppfOver.topology B S hS V := by
  let D := E.map (Over.forget (B.obj hS))
  have hD : AlgebraicGeometry.IsFppfCovering ⟨V.left, D⟩ := by
    rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
      ← PreZeroHypercover.presieve₀_map]
    exact hE
  obtain ⟨⟨T', D'⟩, hD', ht, heq⟩ := B.fppf_has_representative ⟨V.left, D⟩ hD
  cases ht
  obtain ⟨_, ⟨β, hX, hf⟩⟩ := heq
  have hle : D'.sieve₀ ≤ D.sieve₀ := by
    rw [Sieve.generate_le_iff]
    rintro Z f ⟨i⟩
    rw [hf i]
    exact D.sieve₀.downward_closed (D.sieve₀_f (β i)) (eqToHom (hX i))
  have hD'top : D'.sieve₀ ∈ B.topology V.left :=
    Precoverage.generate_mem_toGrothendieck
      (show D'.presieve₀ ∈ B.precoverage V.left from ⟨D', rfl, hD'⟩)
  apply (B.topology.mem_over_iff E.sieve₀).mpr
  show Sieve.overEquiv V (Sieve.ofArrows E.X E.f) ∈ _
  rw [Sieve.overEquiv_ofArrows]
  exact B.topology.superset_covering hle hD'top

/-- The empty sieve covers an object of the big fppf site over `S` with empty underlying
scheme. -/
private lemma bot_mem_of_isEmpty
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (V : AlgebraicGeometry.BigFppfOver B S hS)
    [IsEmpty ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V)] :
    ⊥ ∈ AlgebraicGeometry.BigFppfOver.topology B S hS V := by
  let E : PreZeroHypercover.{u + 1} V :=
    { I₀ := PEmpty, X := PEmpty.elim, f := fun i => i.elim }
  have he : (E.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presieve₀ ∈
      Scheme.fppfPrecoverage ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V) := by
    rw [PreZeroHypercover.presieve₀, Scheme.fppfPrecoverage,
      Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨fun x => isEmptyElim x, fun i => PEmpty.elim i⟩
  simpa [E, PreZeroHypercover.sieve₀, Sieve.ofArrows, Presieve.ofArrows_of_isEmpty] using
    sieve_mem_of_fppf B S hS E he


/-- The images of the two coproduct inclusions of schemes are disjoint. -/
private theorem coprod_inl_apply_ne_inr_apply {X Y : Scheme.{u}} (x : X) (y : Y) :
    (coprod.inl : X ⟶ X ⨿ Y) x ≠ (coprod.inr : Y ⟶ X ⨿ Y) y := fun h => by
  have h' : (Sum.inl x : X ⊕ Y) = Sum.inr y :=
    (coprodMk X Y).injective (by simpa only [coprodMk_inl, coprodMk_inr] using h)
  cases h'

/-- The two inclusions into a coproduct in the big fppf site are monomorphisms, generate a
covering sieve, and are disjoint: any object mapping to both over the coproduct is covered by
the empty sieve. -/
theorem binary_coproduct_cover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A D E : AlgebraicGeometry.BigFppfOver B S hS} (i : A ⟶ E) (j : D ⟶ E)
    (e : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj A ⨿
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj D) ≅
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj E)
    (hi : coprod.inl ≫ e.hom = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i)
    (hj : coprod.inr ≫ e.hom = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j) :
    let K : Bool → AlgebraicGeometry.BigFppfOver B S hS := fun b => cond b A D
    let k : ∀ b, K b ⟶ E := fun b => Bool.rec j i b
    (∀ b, Mono (k b)) ∧
    Sieve.ofArrows K k ∈ AlgebraicGeometry.BigFppfOver.topology B S hS E ∧
    (∀ {b c}, b ≠ c → ∀ {Y : AlgebraicGeometry.BigFppfOver B S hS}
      (a : Y ⟶ K b) (d : Y ⟶ K c), a ≫ k b = d ≫ k c →
        ⊥ ∈ AlgebraicGeometry.BigFppfOver.topology B S hS Y) := by
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let K : Bool → AlgebraicGeometry.BigFppfOver B S hS := fun b => cond b A D
  let k : ∀ b, K b ⟶ E := fun b => Bool.rec j i b
  let inc : ∀ b, T.obj (K b) ⟶ T.obj A ⨿ T.obj D := fun b => Bool.rec coprod.inr coprod.inl b
  have hinc : ∀ b, inc b ≫ e.hom = T.map (k b) := fun b => by cases b <;> assumption
  have hopen : ∀ b, AlgebraicGeometry.IsOpenImmersion (T.map (k b)) ∧
      AlgebraicGeometry.Flat (T.map (k b)) ∧
      AlgebraicGeometry.LocallyOfFinitePresentation (T.map (k b)) := fun b => by
    rw [← hinc]
    cases b <;> exact ⟨inferInstance, inferInstance, inferInstance⟩
  refine ⟨fun b => by
    let := (hopen b).1
    exact T.mono_of_mono_map inferInstance, ?_, ?_⟩
  · let C : PreZeroHypercover.{u + 1} E :=
      { I₀ := ULift.{u + 1} Bool, X := fun b => K b.down, f := fun b => k b.down }
    have hC : (C.map T).presieve₀ ∈ Scheme.fppfPrecoverage (T.obj E) := by
      rw [PreZeroHypercover.presieve₀, Scheme.fppfPrecoverage,
        Scheme.ofArrows_mem_precoverage_iff]
      constructor
      · intro x
        obtain ⟨x, rfl⟩ := e.hom.homeomorph.surjective x
        obtain ⟨x, rfl⟩ := (coprodMk (T.obj A) (T.obj D)).surjective x
        cases x with
        | inl a =>
          refine ⟨⟨true⟩, a, ?_⟩
          show T.map i a = _
          rw [← hi]
          simp only [coprodMk_inl, Scheme.Hom.comp_apply]
          rfl
        | inr d =>
          refine ⟨⟨false⟩, d, ?_⟩
          show T.map j d = _
          rw [← hj]
          simp only [coprodMk_inr, Scheme.Hom.comp_apply]
          rfl
      · intro ⟨b⟩
        exact (hopen b).2
    have hc := sieve_mem_of_fppf B S hS C hC
    have heq : C.sieve₀ = Sieve.ofArrows K k := by
      apply le_antisymm <;> rw [Sieve.generate_le_iff]
      · rintro Z f ⟨b⟩
        exact Sieve.ofArrows_mk K k b.down
      · rintro Z f ⟨b⟩
        exact C.sieve₀_f ⟨b⟩
    rwa [heq] at hc
  · intro b c hbc Y a d had
    have hempty : IsEmpty (T.obj Y) := by
      refine ⟨fun y => ?_⟩
      have heq := congrArg (fun f => T.map f y) had
      rw [Functor.map_comp, Functor.map_comp] at heq
      change (T.map (k b)) ((T.map a) y) = (T.map (k c)) ((T.map d) y) at heq
      rw [← hinc, ← hinc] at heq
      have hh : inc b (T.map a y) = inc c (T.map d y) :=
        e.hom.homeomorph.injective (by
          simpa only [Scheme.Hom.comp_apply, Scheme.Hom.homeomorph_apply] using heq)
      cases b <;> cases c
      · exact hbc rfl
      · exact coprod_inl_apply_ne_inr_apply _ _ hh.symm
      · exact coprod_inl_apply_ne_inr_apply _ _ hh
      · exact hbc rfl
    let := hempty
    exact bot_mem_of_isEmpty B S hS Y

/-- An étale morphism out of a representable presheaf is étale as a relative property pulled
back from schemes. -/
private theorem relative_etale_of_isEtale
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {E : AlgebraicGeometry.BigFppfOver B S hS}
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : yoneda.obj E ⟶ X) (hf : AlgebraicGeometry.Space.IsEtale B S hS f) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f := by
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  let : P.IsStableUnderBaseChange := etale_inverseImage_isStableUnderBaseChange B S hS
  have hid : P.presheaf (𝟙 (yoneda.obj E)) := by
    rw [← yoneda.map_id]
    apply MorphismProperty.relative_map
    show Etale (T.map (𝟙 E))
    rw [T.map_id]
    infer_instance
  simpa using hf E (𝟙 _) hid

/-- A morphism which is étale as a relative property pulled back from schemes is étale. -/
private theorem isEtale_of_relative_etale
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ X)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f) :
    AlgebraicGeometry.Space.IsEtale B S hS f := by
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  let : P.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage T
  let : P.presheaf.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition P
  intro A g hg
  exact MorphismProperty.comp_mem P.presheaf g f hg hf

/-- Étaleness of a morphism out of a representable is Zariski local on the source: a family
of open immersions covering the representing scheme whose composites with the morphism are
étale makes the morphism étale. -/
theorem isEtale_of_scheme_openCover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {E : AlgebraicGeometry.BigFppfOver B S hS}
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (f : yoneda.obj E ⟶ X)
    {I : Type*} (A : I → AlgebraicGeometry.BigFppfOver B S hS) (j : ∀ i, A i ⟶ E)
    (hj : ∀ i, AlgebraicGeometry.IsOpenImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (j i)))
    (hcover : ∀ x : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj E,
      ∃ i, ∃ a, (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (j i) a = x)
    (hf : ∀ i, AlgebraicGeometry.Space.IsEtale B S hS (yoneda.map (j i) ≫ f)) :
    AlgebraicGeometry.Space.IsEtale B S hS f := by
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  let : P.IsStableUnderBaseChange := etale_inverseImage_isStableUnderBaseChange B S hS
  let : HasBinaryProducts (AlgebraicGeometry.BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hr : yoneda.relativelyRepresentable f :=
    Functor.relativelyRepresentable.of_diag hX.diagonal_representable f
  apply isEtale_of_relative_etale B S hS f
  apply MorphismProperty.relative_of_snd (P := P) hr
  intro Q g
  let R := hr.pullback g
  let a : R ⟶ E := hr.fst' g
  let b : R ⟶ Q := hr.snd g
  have hs : IsPullback (yoneda.map a) (yoneda.map b) f g := by
    show IsPullback (yoneda.map (hr.fst' g)) (yoneda.map (hr.snd g)) f g
    rw [Functor.relativelyRepresentable.map_fst']
    exact hr.isPullback g
  let R' (i : I) := pullback a (j i)
  let r (i : I) : R' i ⟶ R := pullback.fst a (j i)
  let s (i : I) : R' i ⟶ A i := pullback.snd a (j i)
  have hsq (i : I) : IsPullback (yoneda.map (s i)) (yoneda.map (r i))
      (yoneda.map (j i)) (yoneda.map a) := (IsPullback.of_hasPullback a (j i)).flip.map yoneda
  have hsqi (i : I) : IsPullback (T.map (r i)) (T.map (s i)) (T.map a) (T.map (j i)) :=
    (IsPullback.of_hasPullback a (j i)).map T
  have hri (i : I) : AlgebraicGeometry.IsOpenImmersion (T.map (r i)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.IsOpenImmersion) (hsqi i).flip (hj i)
  let C : (T.obj R).OpenCover := {
    I₀ := I
    X := fun i => T.obj (R' i)
    f := fun i => T.map (r i)
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨?_, hri⟩
      intro x
      obtain ⟨i, y, hy⟩ := hcover (T.map a x)
      obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (hsqi i) x y hy.symm
      exact ⟨i, z, hz⟩ }
  show Etale (T.map b)
  let : HasRingHomProperty (@Etale.{u}) RingHom.Etale := inferInstance
  let : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  apply IsZariskiLocalAtSource.of_openCover (P := @Etale) C
  intro i
  have hi := relative_etale_of_isEtale B S hS _ (hf i)
  have hisq : IsPullback (yoneda.map (s i)) (yoneda.map (r i ≫ b))
      (yoneda.map (j i) ≫ f) g := by
    rw [Functor.map_comp]
    exact (hsq i).paste_vert hs
  have hh : P (r i ≫ b) := hi.property g (yoneda.map (s i)) (r i ≫ b) hisq
  simpa only [P, MorphismProperty.inverseImage, Functor.map_comp] using hh

end AlgebraicGeometry.Space

end
