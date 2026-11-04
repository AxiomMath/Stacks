module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFullyFaithful
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactRepresentables
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigSiteCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
import all StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigSiteCoverings

/-!
# Finite quasi-compact refinements of coverings of the small étale site

On the small étale site of a quasi-compact quasi-separated scheme, every covering sieve of a
quasi-compact object is refined by a finite covering family whose members are affine, and whose
pairwise fibre products are quasi-compact objects of the site. This is the hypothesis of part (4)
of Stacks 0738, verified for the small étale site, and it is what makes sections over such an
object commute with filtered colimits of sheaves.

The covering sieves of the small étale site are those of the Grothendieck topology *generated* by
the étale covering families, so a sieve in it need not come from a family; the first step is an
induction over that generation showing that a covering sieve contains, through each point of the
underlying scheme, an étale arrow belonging to it.

## Main results

* `AlgebraicGeometry.BigEtaleSite.exists_affine_covering_refining_etale_cover` — an ambient étale
  covering family of an object of a big étale site is refined by an internal covering family with
  affine sources.
* `AlgebraicGeometry.SmallEtale.exists_finite_affine_refinement_of_mem_topology` — a covering
  sieve of a quasi-compact object of the small étale site is refined by a finite covering family
  with affine sources.
* `AlgebraicGeometry.SmallEtale.hasFiniteQuasiCompactCoverings` — **the hypothesis of part (4) of
  Stacks 0738 for the small étale site**: the finite refinement can be chosen with quasi-compact
  pairwise fibre products.

## Implementation notes

`AlgebraicGeometry.BigEtaleSite.exists_affine_covering_refining_etale_cover` is
`AlgebraicGeometry.BigEtaleSite.exists_covering_refining_etale_cover` (Stacks 03WW) with the extra
conclusion that the sources of the refinement are affine. The conclusion is not recoverable from
that statement, which discards the comparison with the site's chosen representative along which
affineness transfers, so it is proved again here; the size estimate it rests on is the private
`AlgebraicGeometry.BigEtaleSite.affineOpen_etale_size_lt` of that file, reached through
`import all`.

Affineness of the members of the refinement is what makes their pairwise fibre products
quasi-compact: an affine scheme is a compact space, a quasi-compact morphism has quasi-compact
fibre products over a quasi-separated target, and quasi-compactness of the underlying space is
transported to the site by the same finite-refinement statement.

## References

* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
* [Stacks Project, Tag 03WW](https://stacks.math.columbia.edu/tag/03WW)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.BigEtaleSite

/-- **Stacks 03WW with affine sources.** Every étale covering family of an object of a big étale
site, formed in the ambient category of schemes, is refined by a covering family internal to the
site whose source schemes are affine. -/
public theorem exists_affine_covering_refining_etale_cover
    (B : BigEtaleSite.{u}) {T : B.Scheme}
    (𝒰 : PreZeroHypercover.{u + 1} (B.inclusion.obj T))
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.etalePrecoverage (B.inclusion.obj T)) :
    ∃ 𝒱 : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, 𝒱⟩ ∧ Nonempty ((𝒱.map B.inclusion).Hom 𝒰) ∧
        ∀ i, IsAffine (B.inclusion.obj (𝒱.X i)) := by
  classical
  have hcover : (∀ x, ∃ i, x ∈ Set.range (𝒰.f i)) ∧ ∀ i, Etale (𝒰.f i) :=
    (Scheme.presieve₀_mem_precoverage_iff 𝒰).mp
      (by simpa only [Scheme.etalePrecoverage] using h𝒰)
  let I : Type (u + 1) :=
    Σ i : 𝒰.I₀, Σ V : T.1.affineOpens,
      {U : (𝒰.X i).affineOpens // U.1 ≤ (𝒰.f i) ⁻¹ᵁ V.1}
  let 𝒱 : PreZeroHypercover.{u + 1} T := {
    I₀ := I
    X a := B.obj (a.2.2.1.1.toScheme)
      (affineOpen_etale_size_lt T.2 (𝒰.f a.1) (hcover.2 a.1)
        a.2.1 a.2.2.1 a.2.2.2)
    f a := ⟨a.2.2.1.1.ι ≫ 𝒰.f a.1⟩
  }
  have h𝒱cover :
      (∀ x, ∃ a : I, x ∈ Set.range ((𝒱.map B.inclusion).f a)) ∧
        ∀ a, Etale ((𝒱.map B.inclusion).f a) := by
    refine ⟨fun x => ?_, fun a => ?_⟩
    · obtain ⟨i, y, hy⟩ := hcover.1 x
      obtain ⟨V, hV, hxV, -⟩ :=
        exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
      have hyV : y ∈ (𝒰.f i) ⁻¹ᵁ V := by
        show 𝒰.f i y ∈ V
        rw [hy]
        exact hxV
      obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset hyV
      exact ⟨⟨i, ⟨V, hV⟩, ⟨U, hU⟩, hUV⟩, ⟨y, hyU⟩, hy⟩
    · dsimp [𝒱, PreZeroHypercover.map]
      have : Etale (𝒰.f a.1) := hcover.2 a.1
      infer_instance
  obtain ⟨W', hW', htarget, hcomb⟩ := B.exists_covering_rep ⟨T, 𝒱⟩
    ((Scheme.presieve₀_mem_precoverage_iff (𝒱.map B.inclusion)).mpr h𝒱cover)
  cases htarget
  obtain ⟨β, hX, hf⟩ := hcomb.2
  let χ : (𝒱.map B.inclusion).Hom 𝒰 := {
    s₀ := fun a => a.1
    h₀ := fun a => a.2.2.1.1.ι
    w₀ _ := rfl
  }
  let θ : (W'.2.map B.inclusion).Hom (𝒱.map B.inclusion) := {
    s₀ := β
    h₀ := fun j => B.inclusion.map (eqToHom (hX j))
    w₀ j := by
      show B.inclusion.map (eqToHom (hX j)) ≫
          B.inclusion.map (𝒱.f (β j)) = B.inclusion.map (W'.2.f j)
      rw [← Functor.map_comp, hf j]
  }
  refine ⟨W'.2, hW', ⟨θ.comp χ⟩, fun j => ?_⟩
  rw [hX j]
  exact (β j).2.2.1.2

end AlgebraicGeometry.BigEtaleSite

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- A covering sieve of an object of the small étale site contains, through every point of the
underlying scheme, an étale arrow of the site belonging to it. This is an induction over the
generation of the topology by the étale covering families. -/
private theorem exists_etale_mem_of_saturate
    {Y : SmallEtale B X.1 X.property} {R : Sieve Y}
    (hR : (SmallEtale.precoverage B X.1 X.property).Saturate Y R) :
    ∀ x : (SmallEtale.toScheme B X.1 X.property).obj Y,
      ∃ (Z : SmallEtale B X.1 X.property) (f : Z ⟶ Y),
        R f ∧ Etale ((SmallEtale.toScheme B X.1 X.property).map f) ∧
          x ∈ Set.range ((SmallEtale.toScheme B X.1 X.property).map f).base := by
  intro x
  induction hR with
  | of Y P hP =>
      obtain ⟨E, hEq, hE⟩ :=
        (SmallEtale.mem_precoverage_iff B X.1 X.property).mp hP
      subst P
      let T := SmallEtale.toScheme B X.1 X.property
      let E' := E.map T
      have hEtale : E'.presieve₀ ∈ Scheme.etalePrecoverage (T.obj Y) := by
        have hEtaleB : AlgebraicGeometry.IsEtaleCovering
            ⟨Y.obj.left, E.map (SmallEtale.inclusion B X.1 X.property ⋙
              BigEtaleOver.forget B X.1 X.property)⟩ := hE.1
        simpa [E', T, SmallEtale.toScheme, SmallEtale.inclusion,
          BigEtaleOver.toScheme, BigEtaleOver.forget, AlgebraicGeometry.IsEtaleCovering,
          PreZeroHypercover.map, Functor.comp_map] using hEtaleB
      have hcover := (Scheme.presieve₀_mem_precoverage_iff E').mp hEtale
      obtain ⟨i, y, hy⟩ := hcover.1 x
      exact ⟨E.X i, E.f i, Sieve.le_generate E.presieve₀ _ _ ⟨i⟩, hcover.2 i, y, hy⟩
  | top Y =>
      exact ⟨Y, 𝟙 Y, by simp, inferInstance, x, by simp⟩
  | pullback Y S hS Z f ih =>
      let T := SmallEtale.toScheme B X.1 X.property
      obtain ⟨V, g, hg, hget, ⟨y, hy⟩⟩ := ih ((T.map f).base x)
      have hpb : IsPullback (T.map (pullback.fst g f)) (T.map (pullback.snd g f))
          (T.map g) (T.map f) :=
        IsPullback.of_iso_pullback
          (⟨by simpa only [Functor.map_comp] using congrArg T.map pullback.condition⟩)
          (PreservesPullback.iso T g f)
          (PreservesPullback.iso_hom_fst T g f)
          (PreservesPullback.iso_hom_snd T g f)
      obtain ⟨z, hzf, hzs⟩ := Scheme.exists_preimage_of_isPullback hpb y x hy
      refine ⟨pullback g f, pullback.snd g f, ?_, ?_, z, hzs⟩
      · show S ((pullback.snd g f) ≫ f)
        rw [← pullback.condition]
        exact Sieve.downward_closed S hg (pullback.fst g f)
      · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
          (P := @Etale) hpb hget
  | transitive Y S R hS hlocal ihS ihlocal =>
      obtain ⟨V, g, hg, hget, ⟨y, hy⟩⟩ := ihS x
      obtain ⟨W, f, hf, hfet, ⟨z, hz⟩⟩ := ihlocal hg y
      refine ⟨W, f ≫ g, ?_, ?_, ?_⟩
      · simpa using hf
      · rw [Functor.map_comp]
        exact MorphismProperty.comp_mem @Etale _ _ hfet hget
      · refine ⟨z, ?_⟩
        rw [Functor.map_comp]
        show ((SmallEtale.toScheme B X.1 X.property).map g).base
          (((SmallEtale.toScheme B X.1 X.property).map f).base z) = x
        rw [hz, hy]

/-- Finitely many members of a covering family of an object of the small étale site with
quasi-compact underlying scheme already form a covering family. -/
public theorem exists_finset_isCovering_restrictIndex (U : SmallEtale B X.1 X.property)
    (hU : CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj U))
    (V : PreZeroHypercover.{u + 1} U.obj.left) (hV : B.IsCovering ⟨U.obj.left, V⟩) :
    ∃ F : Finset V.I₀,
      B.IsCovering ⟨U.obj.left, V.restrictIndex (fun i : {i // i ∈ F} => i.1)⟩ := by
  classical
  have hVambient : (V.map B.inclusion).presieve₀ ∈
      Scheme.etalePrecoverage (B.inclusion.obj U.obj.left) := by
    simpa [AlgebraicGeometry.IsEtaleCovering] using hV.1
  have hcov := (Scheme.presieve₀_mem_precoverage_iff (V.map B.inclusion)).mp hVambient
  have : CompactSpace (B.inclusion.obj U.obj.left) := hU
  obtain ⟨F, hF⟩ :=
    isCompact_univ.elim_finite_subcover (fun i => Set.range ((V.map B.inclusion).f i).base)
      (fun i => by
        have := hcov.2 i
        exact (Scheme.Hom.isOpenMap ((V.map B.inclusion).f i)).isOpen_range)
      (fun x _ => by
        obtain ⟨i, y, hy⟩ := hcov.1 x
        exact Set.mem_iUnion.mpr ⟨i, y, hy⟩)
  have hcover :
      ((V.restrictIndex (fun i : {i // i ∈ F} => i.1)).map B.inclusion).presieve₀ ∈
        Scheme.etalePrecoverage (B.inclusion.obj U.obj.left) := by
    refine (Scheme.presieve₀_mem_precoverage_iff _).2 ⟨fun x => ?_, fun i => ?_⟩
    · obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ x))
      exact ⟨⟨i, hi⟩, hx⟩
    · have : Etale (((V.restrictIndex (fun i : {i // i ∈ F} => i.1)).map B.inclusion).f i) :=
        hcov.2 i.1
      infer_instance
  exact ⟨F, hcover, (Cardinal.mk_subtype_le _).trans hV.2⟩

/-- A sieve on an object of the small étale site contains every arrow whose underlying morphism
of schemes factors through the underlying morphism of an arrow of the sieve. -/
public theorem mem_of_comp_toScheme_map_eq {Y Z U : SmallEtale B X.1 X.property} (S : Sieve U)
    {f : Y ⟶ U} {k : Z ⟶ U} (hk : S k)
    (w : (SmallEtale.toScheme B X.1 X.property).obj Y ⟶
      (SmallEtale.toScheme B X.1 X.property).obj Z)
    (hw : w ≫ (SmallEtale.toScheme B X.1 X.property).map k =
      (SmallEtale.toScheme B X.1 X.property).map f) : S f := by
  have hcomp : ∀ {W : SmallEtale B X.1 X.property} (g : W ⟶ U),
      (SmallEtale.toScheme B X.1 X.property).map g ≫ B.inclusion.map U.obj.hom =
        B.inclusion.map W.obj.hom := fun g => by
    have hh := congrArg B.inclusion.map g.hom.w
    rw [Functor.map_comp] at hh
    exact hh
  let a : Y ⟶ Z := by
    refine ObjectProperty.homMk (Over.homMk (B.inclusion.preimage w) ?_)
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, Functor.map_preimage B.inclusion]
    show w ≫ B.inclusion.map Z.obj.hom = B.inclusion.map Y.obj.hom
    rw [← hcomp k, ← hcomp f, ← hw, Category.assoc]
  have hmapa : (SmallEtale.toScheme B X.1 X.property).map a = w := by
    dsimp [a]
    show B.inclusion.map (B.inclusion.preimage w) = w
    exact B.inclusion.map_preimage _
  have ha : a ≫ k = f := by
    apply ObjectProperty.hom_ext
    ext
    show (SmallEtale.toScheme B X.1 X.property).map (a ≫ k) =
      (SmallEtale.toScheme B X.1 X.property).map f
    rw [Functor.map_comp, hmapa, hw]
  rw [← ha]
  exact S.downward_closed hk a

/-- A covering sieve of an object of the small étale site is refined, in the ambient category of
schemes, by an étale covering family with affine sources each of whose members factors through an
arrow of the sieve. -/
public theorem exists_affine_covering_lifting_mem_topology (U : SmallEtale B X.1 X.property)
    {S : Sieve U} (hS : S ∈ SmallEtale.topology B X.1 X.property U) :
    ∃ V : PreZeroHypercover.{u + 1} U.obj.left, B.IsCovering ⟨U.obj.left, V⟩ ∧
      (∀ i, _root_.AlgebraicGeometry.IsAffine (B.inclusion.obj (V.X i))) ∧
      ∀ i, ∃ (Z : SmallEtale B X.1 X.property) (k : Z ⟶ U), S k ∧
        ∃ w : B.inclusion.obj (V.X i) ⟶ (SmallEtale.toScheme B X.1 X.property).obj Z,
          w ≫ (SmallEtale.toScheme B X.1 X.property).map k = B.inclusion.map (V.f i) := by
  let T := SmallEtale.toScheme B X.1 X.property
  have hpoint := exists_etale_mem_of_saturate B X ((Precoverage.mem_toGrothendieck_iff).mp hS)
  let I : Type (u + 1) :=
    {p : Σ Z : SmallEtale B X.1 X.property, Z ⟶ U //
      S p.2 ∧ Etale (T.map p.2)}
  let Q : PreZeroHypercover.{u + 1} (B.inclusion.obj U.obj.left) := {
    I₀ := I
    X i := T.obj i.val.1
    f i := T.map i.val.2
  }
  have hQ : Q.presieve₀ ∈ Scheme.etalePrecoverage (B.inclusion.obj U.obj.left) :=
    (Scheme.presieve₀_mem_precoverage_iff Q).2
      ⟨fun x => by
        obtain ⟨Z, f, hf, hfet, hxf⟩ := hpoint x
        exact ⟨⟨⟨Z, f⟩, hf, hfet⟩, hxf⟩, fun i => i.property.2⟩
  obtain ⟨V, hV, ⟨φ⟩, hAffineV⟩ :=
    BigEtaleSite.exists_affine_covering_refining_etale_cover B Q hQ
  exact ⟨V, hV, hAffineV, fun i =>
    ⟨(φ.s₀ i).1.1, (φ.s₀ i).1.2, (φ.s₀ i).2.1, φ.h₀ i, φ.w₀ i⟩⟩

/-- **A covering sieve of a quasi-compact object of the small étale site is refined by a finite
covering family with affine sources.** The site's topology is generated by the étale covering
families, so a covering sieve first has to be shown to contain an étale arrow through every point;
those arrows are then refined by a family with affine sources, and quasi-compactness of the
underlying scheme cuts the family down to a finite one. -/
public theorem exists_finite_affine_refinement_of_mem_topology
    [CompactSpace X.1] [QuasiSeparatedSpace X.1] (U : SmallEtale B X.1 X.property)
    (hU : CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj U)) :
    ∀ S ∈ SmallEtale.topology B X.1 X.property U,
      ∃ 𝒱 : PreZeroHypercover.{u + 1} U,
        Finite 𝒱.I₀ ∧ 𝒱.sieve₀ ∈ SmallEtale.topology B X.1 X.property U ∧
          𝒱.sieve₀ ≤ S ∧
          ∀ i, _root_.AlgebraicGeometry.IsAffine
            ((SmallEtale.toScheme B X.1 X.property).obj (𝒱.X i)) := by
  classical
  intro S hS
  obtain ⟨V, hV, hAffineV, hlift⟩ := exists_affine_covering_lifting_mem_topology B X U hS
  let Vsite : PreZeroHypercover U := {
    I₀ := (V.map B.inclusion).I₀
    X i := by
      change V.I₀ at i
      have : Etale (B.inclusion.map (V.f i)) :=
        ((Scheme.presieve₀_mem_precoverage_iff (V.map B.inclusion)).mp hV.1).2 i
      have : Etale (B.inclusion.map U.obj.hom) := U.property
      exact ⟨Over.mk (V.f i ≫ U.obj.hom), by
        show Etale (B.inclusion.map (V.f i) ≫ B.inclusion.map U.obj.hom)
        infer_instance⟩
    f i := by
      change V.I₀ at i
      exact ObjectProperty.homMk (Over.homMk (V.f i) rfl)
  }
  obtain ⟨F, hF⟩ := exists_finset_isCovering_restrictIndex B X U hU V hV
  let K := {i : V.I₀ // i ∈ F}
  let 𝒱 : PreZeroHypercover U := {
    I₀ := K
    X i := Vsite.X i.1
    f i := Vsite.f i.1
  }
  have h𝒱scheme : 𝒱.sieve₀ ∈ SmallEtale.topology B X.1 X.property U := by
    show (SmallEtale.precoverage B X.1 X.property).Saturate U 𝒱.sieve₀
    apply Precoverage.Saturate.of
    refine ⟨𝒱, rfl, ?_⟩
    show B.IsCovering ⟨U.obj.left,
      (𝒱.map (SmallEtale.inclusion B X.1 X.property)).map
        (BigEtaleOver.forget B X.1 X.property)⟩
    have hmap :
        (𝒱.map (SmallEtale.inclusion B X.1 X.property)).map
          (BigEtaleOver.forget B X.1 X.property) =
            V.restrictIndex (fun i : K => i.1) := by
      ext <;> rfl
    rw [hmap]
    exact hF
  have hle : 𝒱.sieve₀ ≤ S := by
    intro Y f hf
    obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff 𝒱.X 𝒱.f f).mp hf
    obtain ⟨Z, k, hk, w, hw⟩ := hlift i.1
    exact S.downward_closed (mem_of_comp_toScheme_map_eq B X S (f := 𝒱.f i) hk w hw) g
  exact ⟨𝒱, inferInstance, h𝒱scheme, hle, fun i => by
    show _root_.AlgebraicGeometry.IsAffine (B.inclusion.obj (V.X i.1))
    exact hAffineV i.1⟩

/-- **The hypothesis of part (4) of Stacks 0738, for the small étale site.** On a quasi-compact
quasi-separated scheme, every covering sieve of a quasi-compact quasi-separated object of the small
étale site is refined by a finite covering family whose pairwise fibre products are quasi-compact
objects of the site.

With this in hand, sections over such an object commute with filtered colimits of sheaves, which
is what makes a sheaf with a finite presentation by such objects a compact object. -/
public theorem hasFiniteQuasiCompactCoverings
    [CompactSpace X.1] [QuasiSeparatedSpace X.1] (U : SmallEtale B X.1 X.property)
    (hU : CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj U))
    (hQS : QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj U)) :
    (SmallEtale.topology B X.1 X.property).HasFiniteQuasiCompactCoverings U := by
  classical
  let T := SmallEtale.toScheme B X.1 X.property
  intro S hS
  obtain ⟨𝒱, hfin, hcover, hle, hAffine⟩ :=
    exists_finite_affine_refinement_of_mem_topology B X U hU S hS
  refine ⟨𝒱, hfin, hcover, hle, fun j j' => ?_⟩
  have : _root_.AlgebraicGeometry.IsAffine (T.obj (𝒱.X j)) := hAffine j
  have : _root_.AlgebraicGeometry.IsAffine (T.obj (𝒱.X j')) := hAffine j'
  have : CompactSpace (T.obj (𝒱.X j)) := Scheme.compactSpace_of_isAffine _
  have : CompactSpace (T.obj (𝒱.X j')) := Scheme.compactSpace_of_isAffine _
  have : QuasiSeparatedSpace (T.obj U) := hQS
  let Wsite := pullback (𝒱.f j) (𝒱.f j')
  have : CompactSpace (T.obj Wsite) := by
    have : QuasiCompact (T.map (𝒱.f j)) := inferInstance
    have : CompactSpace
        (Limits.pullback (C := Scheme) (T.map (𝒱.f j)) (T.map (𝒱.f j'))) := inferInstance
    exact isCompact_univ_iff.mp
      ((PreservesPullback.iso T (𝒱.f j) (𝒱.f j')).hom.homeomorph.isCompact_preimage.mpr
        isCompact_univ)
  exact ⟨Wsite, pullback.fst _ _, pullback.snd _ _, IsPullback.of_hasPullback _ _,
    isQuasiCompactObject_of_compactSpace B X.1 X.property Wsite inferInstance⟩

end AlgebraicGeometry.SmallEtale

end
