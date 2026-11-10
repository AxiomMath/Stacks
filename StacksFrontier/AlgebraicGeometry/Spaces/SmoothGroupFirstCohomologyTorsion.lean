module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.RingTheory.Etale.Field
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringRestrictionCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineIntersections
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothOverField
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
import StacksFrontier.AlgebraicGeometry.Spaces.Points
import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFpqcLocalAtTarget
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Torsion of first fppf cohomology of a smooth commutative group algebraic space

Over a field `K`, every class in the first fppf cohomology group of a smooth commutative group
algebraic space `G` has finite order: a `G`-torsor is smooth, so it has a point over a finite
separable extension `L/K`, and the symmetric power of that point trivialises `n` times the class
of the torsor, where `n = [L : K]`.

## Main results

* `AlgebraicGeometry.Space.fppfH1_isAddTorsion`: **Stacks 0AFA**, torsion of first fppf
  cohomology.

## Implementation notes

A commutative group algebraic space is presented by its sheaf of abelian groups on the big fppf
site: the underlying set-valued sheaf is an algebraic space and the structural morphism to the
base is smooth, which makes the coefficient sheaf of `CategoryTheory.Sheaf.H` explicit.

Showing a torsor to be an algebraic space uses the fppf descent statement of Stacks 04SK,
`AlgebraicGeometry.isAlgebraicSpace_of_isCovering`, which rests on the bootstrap theorem
Stacks 04S6, condition (3).

## References

* [Stacks Project, Tag 0AFA](https://stacks.math.columbia.edu/tag/0AFA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Space.pointTopology

/-- After an étale base change near a point of the base, a finite étale morphism becomes a
finite family of pairwise disjoint opens each mapping isomorphically onto the base. -/
private theorem exists_etale_disjoint_open_decomposition {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.IsFinite f] [Etale f] (s : S) :
    ∃ (N : AlgebraicGeometry.EtaleNeighborhood S s) (n : ℕ)
      (V : Fin n → (pullback f N.toBase).Opens),
      sSup (Set.range V) = ⊤ ∧ _root_.Pairwise (fun i j => Disjoint (V i) (V j)) ∧
        ∀ j, IsIso ((V j).ι ≫ pullback.snd f N.toBase) := by
  classical
  obtain ⟨U, g, hg, u, hu, ι, hι, e, he⟩ := Stacks.Etale.exists_etale_pullback_iso_sigma f s
  have : Etale g := hg
  have : Finite ι := hι
  let N : AlgebraicGeometry.EtaleNeighborhood S s :=
    { scheme := U, point := u, toBase := g, map_point := hu }
  let φ : Fin (Nat.card ι) ≃ ι := (Finite.equivFin ι).symm
  have hoi (i : ι) : IsOpenImmersion (Sigma.ι (fun _ : ι ↦ U) i) := by
    have h0 := (sigmaOpenCover (fun _ : ι ↦ U)).map_prop i
    rwa [sigmaOpenCover_f] at h0
  have hjoint (y : ↥(∐ fun _ : ι ↦ U)) :
      ∃ (i : ι) (z : U), (Sigma.ι (fun _ : ι ↦ U) i) z = y := by
    obtain ⟨⟨i, z⟩, hz⟩ := (sigmaMk (fun _ : ι ↦ U)).surjective y
    exact ⟨i, z, by rw [← sigmaMk_mk]; exact hz⟩
  have hopen (i : ι) : IsOpenImmersion (Sigma.ι (fun _ : ι ↦ U) i ≫ e.inv) := by
    have := hoi i
    infer_instance
  let W (i : ι) : (pullback f g).Opens :=
    @Scheme.Hom.opensRange _ _ (Sigma.ι (fun _ : ι ↦ U) i ≫ e.inv) (hopen i)
  have hpre (i : ι) : W i = e.hom ⁻¹ᵁ @Scheme.Hom.opensRange _ _
      (Sigma.ι (fun _ : ι ↦ U) i) (hoi i) := by
    ext x
    simp only [W, Scheme.Hom.coe_opensRange, Scheme.Hom.coe_preimage, Set.mem_preimage,
      Set.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [← Scheme.Hom.comp_apply, Category.assoc, e.inv_hom_id,
        Category.comp_id]⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl⟩
  refine ⟨N, Nat.card ι, fun j => W (φ j), ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro x _
    rw [TopologicalSpace.Opens.mem_sSup]
    obtain ⟨i, z, hz⟩ := hjoint (e.hom.base x)
    exact ⟨W (φ (φ.symm i)), ⟨φ.symm i, rfl⟩, by rw [φ.apply_symm_apply, hpre]; exact ⟨z, hz⟩⟩
  · intro a b hab
    change Disjoint (W (φ a)) (W (φ b))
    rw [disjoint_iff, hpre, hpre, ← Scheme.Hom.preimage_inf,
      disjoint_iff.mp (disjoint_opensRange_sigmaι (fun _ : ι ↦ U) (φ a) (φ b)
        (fun hc => hab (φ.injective hc))), Scheme.Hom.preimage_bot]
  · intro j
    have hoj := hopen (φ j)
    have hsnd : (Sigma.ι (fun _ : ι ↦ U) (φ j) ≫ e.inv) ≫ pullback.snd f g = 𝟙 U := by
      rw [show pullback.snd f g = e.hom ≫ Sigma.desc fun _ : ι ↦ 𝟙 U from he.symm]
      simp
    change IsIso ((W (φ j)).ι ≫ pullback.snd f g)
    rw [← @Scheme.Hom.isoOpensRange_inv_comp _ _ _ hoj, Category.assoc, hsnd, Category.comp_id]
    infer_instance

/-- A cofan on a one-element index type whose single leg is the identity is a colimit. -/
private def isColimit_cofan_unique.{t, v, w'} {C : Type t} [Category.{v} C]
    {I : Type w'} [Unique I] (Y : C) : IsColimit (Cofan.mk Y (fun _ : I => 𝟙 Y)) := by
  refine Cofan.IsColimit.mk _ (fun c => c.ι.app ⟨default⟩) ?_ ?_
  · intro c i
    obtain rfl : i = default := Unique.eq_default i
    exact Category.id_comp _
  · intro c m hm
    exact (Category.id_comp m).symm.trans (hm default)

/-- The singleton family of a surjective, flat, locally finitely presented object of the big
fppf category over `S` satisfies the covering conditions on points and morphisms. -/
private theorem singleton_surjective_flat_lfp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (V : AlgebraicGeometry.BigFppfOver B S hS)
    [Flat (B.inclusion.map V.hom)]
    [LocallyOfFinitePresentation (B.inclusion.map V.hom)]
    [Surjective (B.inclusion.map V.hom)] :
    (∀ t : (Over.mk (𝟙 (B.obj hS)) : AlgebraicGeometry.BigFppfOver B S hS).left.obj,
      ∃ _ : PUnit.{u + 2}, ∃ v : V.left.obj,
        B.inclusion.map (Over.mkIdTerminal.from V).left v = t) ∧
    ∀ _ : PUnit.{u + 2}, Flat (B.inclusion.map (Over.mkIdTerminal.from V).left) ∧
      LocallyOfFinitePresentation (B.inclusion.map (Over.mkIdTerminal.from V).left) := by
  refine ⟨fun s => ?_, fun _ => ?_⟩
  · obtain ⟨v, hv⟩ := (inferInstance : Surjective (B.inclusion.map V.hom)).1 s
    exact ⟨PUnit.unit, v, by simpa only [Over.mkIdTerminal_from_left, Over.mk_left] using hv⟩
  · simpa only [Over.mkIdTerminal_from_left] using
      (show Flat (B.inclusion.map V.hom) ∧
        LocallyOfFinitePresentation (B.inclusion.map V.hom) from ⟨inferInstance, inferInstance⟩)

/-- The singleton family of a surjective, flat, locally finitely presented object of the big
fppf category over `S` is a covering family of the terminal object. -/
private theorem isCovering_singleton_of_fppf
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (V : AlgebraicGeometry.BigFppfOver B S hS)
    [Flat (B.inclusion.map V.hom)]
    [LocallyOfFinitePresentation (B.inclusion.map V.hom)]
    [Surjective (B.inclusion.map V.hom)] :
    AlgebraicGeometry.BigFppfOver.IsCovering B S hS
      ⟨Over.mk (𝟙 (B.obj hS)),
        PreZeroHypercover.singleton.{u + 1} (Over.mkIdTerminal.from V)⟩ := by
  refine ⟨?_, (B.coverings_isSite.1 (𝟙 (B.obj hS))).2⟩
  rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
    PreZeroHypercover.presieve₀, Presieve.map_ofArrows, Scheme.fppfPrecoverage,
    Scheme.ofArrows_mem_precoverage_iff]
  exact singleton_surjective_flat_lfp B S hS V

private theorem schemeSpaceMap_isFlat
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (g : U ⟶ V)
    (hg : Flat ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) :
    AlgebraicGeometry.Space.IsFlat B S hS (AlgebraicGeometry.schemeSpaceMap g).hom := by
  change AlgebraicGeometry.Space.HoldsOnEveryEtaleChart B S hS (@Flat) (yoneda.map g)
  rw [AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_representable
    B S hS (@Flat) AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget]
  let eU := yoneda.preimage (yoneda.obj U).reprW.hom
  let eV := yoneda.preimage (yoneda.obj V).reprW.inv
  have hreprU : IsIso (yoneda.obj U).reprW.hom := (yoneda.obj U).reprW.isIso_hom
  have hreprV : IsIso (yoneda.obj V).reprW.inv := (yoneda.obj V).reprW.isIso_inv
  have heU : IsIso eU := by
    let : IsIso (yoneda.map eU) := by
      simpa [eU] using hreprU
    exact Yoneda.fullyFaithful.isIso_of_isIso_map eU
  have heV : IsIso eV := by
    let : IsIso (yoneda.map eV) := by
      simpa [eV] using hreprV
    exact Yoneda.fullyFaithful.isIso_of_isIso_map eV
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have heU' : IsIso (T.map eU) := by infer_instance
  have heV' : IsIso (T.map eV) := by infer_instance
  have hpre : Flat (T.map eU ≫ T.map g) := by
    let : IsIso (T.map eU) := heU'
    let : Flat (T.map g) := hg
    infer_instance
  have hg' : Flat ((T.map eU ≫ T.map g) ≫ T.map eV) := by
    let : IsIso (T.map eV) := heV'
    let : Flat (T.map eU ≫ T.map g) := hpre
    infer_instance
  have heq : yoneda.preimage ((yoneda.obj U).reprW.hom ≫ yoneda.map g ≫
      (yoneda.obj V).reprW.inv) = eU ≫ g ≫ eV := by
    apply yoneda.map_injective
    simp [eU, eV]
  rw [heq]
  exact hg'

private noncomputable def affineOpenOver
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : AlgebraicGeometry.BigFppfOver B S hS)
    (W : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj P).Opens)
    (hW : IsAffineOpen W) : AlgebraicGeometry.BigAffineFppf B S hS := by
  let A : B.Schemes := ⟨W.toScheme,
    Scheme.size_lt_of_isOpenImmersion W.ι P.left.property⟩
  let j : A ⟶ P.left := ⟨W.ι⟩
  let Q : AlgebraicGeometry.BigFppfOver B S hS := Over.mk (j ≫ P.hom)
  refine ⟨Q, ?_⟩
  change IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Q)
  change IsAffine W.toScheme
  exact hW

private noncomputable def affineOpenOverMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : AlgebraicGeometry.BigFppfOver B S hS)
    (W : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj P).Opens)
    (hW : IsAffineOpen W) :
    (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
      (affineOpenOver B S hS P W hW) ⟶ P := by
  let A : B.Schemes := ⟨W.toScheme,
    Scheme.size_lt_of_isOpenImmersion W.ι P.left.property⟩
  let j : A ⟶ P.left := ⟨W.ι⟩
  change (Over.mk (j ≫ P.hom)) ⟶ P
  exact Over.homMk j

private theorem schemeFppfCover_isFpqcCovering
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V : AlgebraicGeometry.BigFppfOver B S hS}
    (E : PreZeroHypercover V)
    (hf : (E.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presieve₀ ∈
        Scheme.fppfPrecoverage
          ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V)) :
    AlgebraicGeometry.Space.IsFpqcCovering B S hS
      (fun i => (AlgebraicGeometry.schemeSpaceMap (E.f i)).hom) := by
  classical
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hf' : (E.map G).presieve₀ ∈ Scheme.fppfPrecoverage (G.obj V) := hf
  refine ⟨?_, ?_⟩
  · intro i
    obtain ⟨_, hprop⟩ := (Scheme.presieve₀_mem_precoverage_iff (E.map G)).mp hf'
    exact schemeSpaceMap_isFlat B S hS (E.f i) (hprop i |>.1)
  · intro A h
    let Aover := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj A
    change yoneda.obj Aover ⟶ yoneda.obj V at h
    let : IsAffine (G.obj Aover) := A.property
    let g : (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj A ⟶ V :=
      yonedaEquiv h
    let GA := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g
    let E₀ : Scheme.fppfPrecoverage.ZeroHypercover (G.obj V) := ⟨E.map G, hf'⟩
    let F := E₀.pullback₂ GA
    let K := F.toPreZeroHypercover
    have hK := (Scheme.presieve₀_mem_precoverage_iff K).mp F.mem₀
    have hsize (i : K.I₀) : (K.X i).size < B.cutoff := by
      change (pullback (G.map (E.f i)) GA).size < B.cutoff
      exact Scheme.size_pullback_lt _ _ (E.X i).left.property Aover.left.property
    have hpoints (x : (G.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj A))) :
        ∃ i : K.I₀, ∃ y : K.X i, K.f i y = x := by
      have hx := hK.1 x
      simp only [Set.mem_range] at hx
      rcases hx with ⟨i, y, hy⟩
      exact ⟨i, y, hy⟩
    choose i y hy using hpoints
    choose W hW hmem hsubset using fun x =>
      exists_isAffineOpen_mem_and_subset (X := K.X (i x)) (x := y x)
        (U := ⊤) (by simp)
    let q (x : (G.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj A))) :
        Scheme.{u} := (W x).toScheme
    let qmap (x : (G.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj A))) :
        q x ⟶ G.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj A) :=
      (W x).ι ≫ K.f (i x)
    have hqFlat (x : (G.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj A))) :
        Flat (qmap x) := by
      let : Flat (K.f (i x)) := hK.2 (i x) |>.1
      let : Flat (W x).ι := inferInstance
      infer_instance
    have hqLfp (x : (G.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj A))) :
        LocallyOfFinitePresentation (qmap x) := by
      let : LocallyOfFinitePresentation (K.f (i x)) := hK.2 (i x) |>.2
      let : LocallyOfFinitePresentation (W x).ι := inferInstance
      infer_instance
    have hqOpen (x : (G.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj A))) :
        IsOpen (Set.range (qmap x)) := by
      let : Flat (qmap x) := hqFlat x
      let : LocallyOfFinitePresentation (qmap x) := hqLfp x
      have ho : IsOpenMap (qmap x) := Scheme.Hom.isOpenMap (qmap x)
      simpa using ho Set.univ isOpen_univ
    have hcover : ∀ x, x ∈ Set.range (qmap x) := by
      intro x
      refine ⟨⟨y x, hmem x⟩, ?_⟩
      change (K.f (i x)) ((W x).ι ⟨y x, hmem x⟩) = x
      rw [Scheme.Opens.ι_apply]
      exact hy x
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
      (fun x => Set.range (qmap x)) hqOpen (by
        intro x _
        exact Set.mem_iUnion.mpr ⟨x, hcover x⟩)
    let J₀ := {x // x ∈ s}
    let J := ULift.{u + 1} J₀
    let Kobj (k : K.I₀) : B.Schemes := ⟨K.X k, hsize k⟩
    let P (k : K.I₀) : AlgebraicGeometry.BigFppfOver B S hS :=
      Over.mk ((⟨K.f k⟩ : Kobj k ⟶ Aover.left) ≫ Aover.hom)
    let pA (k : K.I₀) : P k ⟶
        Aover := Over.homMk ⟨K.f k⟩
    let pV (k : K.I₀) : P k ⟶ E.X k := by
      refine Over.homMk (f := ⟨pullback.fst (G.map (E.f k)) GA⟩) ?_
      apply B.inclusion.map_injective
      change pullback.fst (G.map (E.f k)) GA ≫
          B.inclusion.map (Over.hom (E.X k)) =
        pullback.snd (G.map (E.f k)) GA ≫ B.inclusion.map (Over.hom Aover)
      rw [← (E.f k).w, ← g.w]
      change pullback.fst (G.map (E.f k)) GA ≫ G.map (E.f k) ≫
          B.inclusion.map (Over.hom V) =
        pullback.snd (G.map (E.f k)) GA ≫ G.map g ≫
          B.inclusion.map (Over.hom V)
      rw [← Category.assoc, pullback.condition]
      rfl
    let U : PreZeroHypercover.{u + 1} A := {
      I₀ := J
      X := fun x => affineOpenOver B S hS (P (i x.down.1)) (W x.down.1) (hW x.down.1)
      f := fun x => ObjectProperty.homMk
        (affineOpenOverMap B S hS (P (i x.down.1)) (W x.down.1) (hW x.down.1) ≫ pA (i x.down.1)) }
    let : Fintype J₀ := Fintype.ofFinset s (by intro x; rfl)
    let : Fintype J := inferInstance
    refine ⟨U, ?_, ?_, ?_⟩
    · exact Finite.of_fintype J
    · apply Scheme.fppfPrecoverage_le_fpqcPrecoverage
      rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows,
        Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
      constructor
      · intro z
        have hz : z ∈ ⋃ x ∈ s, Set.range (qmap x) := by
          exact hs (Set.mem_univ z)
        rcases Set.mem_iUnion.mp hz with ⟨x, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨hxS, hxrange⟩
        rcases hxrange with ⟨y, hy⟩
        refine ⟨ULift.up ⟨x, hxS⟩, ?_⟩
        refine ⟨y, ?_⟩
        change K.f (i x) ((W x).ι y) = z
        exact hy
      · intro x
        change Flat (qmap x.down.1) ∧
          LocallyOfFinitePresentation (qmap x.down.1)
        exact ⟨hqFlat x.down.1, hqLfp x.down.1⟩
    · intro x
      refine ⟨i x.down.1, yoneda.map (affineOpenOverMap B S hS
        (P (i x.down.1)) (W x.down.1) (hW x.down.1) ≫ pV (i x.down.1)), ?_⟩
      have hpull : pV (i x.down.1) ≫ E.f (i x.down.1) =
          pA (i x.down.1) ≫ g := by
        apply Over.OverMorphism.ext
        apply B.inclusion.map_injective
        change pullback.fst (G.map (E.f (i x.down.1))) GA ≫
            G.map (E.f (i x.down.1)) =
          pullback.snd (G.map (E.f (i x.down.1))) GA ≫ G.map g
        exact pullback.condition
      have hh : yoneda.map g = h := by
        apply yonedaEquiv.injective
        rw [yonedaEquiv_yoneda_map]
      let k : K.I₀ := i x.down.1
      have hpull' : pV k ≫ E.f k = pA k ≫ g := by
        simpa [k, K, F, E₀] using hpull
      dsimp [AlgebraicGeometry.schemeSpaceMap, AlgebraicGeometry.schemeSpace, K, F, E₀,
        U, affineOpenOverMap, affineOpenOver] at ⊢
      change yoneda.map
          (affineOpenOverMap B S hS (P (i x.down.1)) (W x.down.1)
            (hW x.down.1) ≫ pV (i x.down.1)) ≫
            yoneda.map (E.f (i x.down.1)) =
        yoneda.map
          (affineOpenOverMap B S hS (P (i x.down.1)) (W x.down.1)
            (hW x.down.1) ≫ pA (i x.down.1)) ≫ h
      rw [← Functor.map_comp, ← hh]
      conv_rhs => rw [← Functor.map_comp]
      have hcomp :
          affineOpenOverMap B S hS (P k) (W x.down.1) (hW x.down.1) ≫
              pV k ≫ E.f k =
            affineOpenOverMap B S hS (P k) (W x.down.1) (hW x.down.1) ≫
              pA k ≫ g := by
        simpa [Category.assoc] using congrArg
          (fun t => affineOpenOverMap B S hS (P k) (W x.down.1)
            (hW x.down.1) ≫ t) hpull'
      exact congrArg (fun m => yoneda.map m) hcomp

private theorem exists_base_cover_refining_sieve
    (𝒞 : AlgebraicGeometry.BigFppfSite.{u}) {T : 𝒞.Schemes} {R : Sieve T}
    (hR : R ∈ 𝒞.topology T) :
    ∃ E : PreZeroHypercover T, 𝒞.IsCovering ⟨T, E⟩ ∧ E.presieve₀ ≤ R := by
  rw [AlgebraicGeometry.BigFppfSite.topology, Precoverage.mem_toGrothendieck_iff] at hR
  induction hR with
  | of T P hP =>
      obtain ⟨E, hEq, hE⟩ := hP
      refine ⟨E, hE, ?_⟩
      rw [hEq]
      exact Sieve.le_generate _
  | top T =>
      exact ⟨PreZeroHypercover.singleton (𝟙 T), 𝒞.coverings_isSite.1 (𝟙 T), by
        intro Y f hf
        trivial⟩
  | pullback T R hR Y f ih =>
      obtain ⟨E, hE, hle⟩ := ih
      obtain ⟨P, p₁, p₂, hpb, hP⟩ := 𝒞.coverings_isSite.2.2 ⟨T, E⟩ hE Y f
      let F : PreZeroHypercover Y := ⟨E.I₀, P, p₂⟩
      refine ⟨F, hP, ?_⟩
      rw [Presieve.ofArrows_le_iff]
      intro i
      rw [Sieve.pullback_apply]
      rw [← (hpb i).w]
      exact R.downward_closed (hle _ _ ⟨i⟩) (p₁ i)
  | transitive T R Q hR hRQ ihR ihRQ =>
      obtain ⟨E, hE, hle⟩ := ihR
      have hlocal (i : E.I₀) := ihRQ (hle _ _ ⟨i⟩)
      choose F hF hFle using hlocal
      let EF := E.bind F
      have hEF : 𝒞.IsCovering ⟨T, EF⟩ :=
        𝒞.coverings_isSite.2.1 ⟨T, E⟩ hE (fun i ↦ ⟨E.X i, F i⟩) hF (fun _ ↦ rfl)
      refine ⟨EF, hEF, ?_⟩
      rw [Presieve.ofArrows_le_iff]
      rintro ⟨i, j⟩
      change Q ((F i).f j ≫ E.f i)
      exact hFle i _ _ ⟨j⟩

private theorem generate_mem_topology_of_isFppfCovering
    (𝒞 : AlgebraicGeometry.BigFppfSite.{u}) {T : 𝒞.Schemes}
    {E : PreZeroHypercover.{u + 1, u, u + 1} T}
    (hE : AlgebraicGeometry.IsFppfCovering ⟨T, E⟩) :
    Sieve.generate E.presieve₀ ∈ 𝒞.topology T := by
  obtain ⟨E', hE', hEquiv⟩ := 𝒞.fppf_has_representative ⟨T, E⟩ hE
  have hpre : E.presieve₀ ∈ 𝒞.precoverage T := by
    obtain ⟨hT, hComb⟩ := hEquiv
    cases hT
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb]
    exact ⟨E'.2, rfl, hE'⟩
  exact Precoverage.generate_mem_toGrothendieck hpre

private theorem exists_nonempty_fppf_torsor_section
    (k : Type u) [Field k] (B : AlgebraicGeometry.BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    (G : SheafOfGroups (AlgebraicGeometry.BigFppfOver.topology B (Spec (.of k)) hk))
    (F : PseudoTorsor G) (hF : F.IsTorsor) :
    ∃ (V : AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk),
      Nonempty V.left.obj ∧ Flat (B.inclusion.map V.hom) ∧
      LocallyOfFinitePresentation (B.inclusion.map V.hom) ∧
      Nonempty (F.presheaf.obj (Opposite.op V)) := by
  classical
  let T : AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk := Over.mk (𝟙 (B.obj hk))
  obtain ⟨R, hR, hs⟩ := hF T
  obtain ⟨E, hE, hle⟩ := exists_base_cover_refining_sieve B
    ((GrothendieckTopology.mem_over_iff _ _).mp hR)
  dsimp only [T, Over.mk_left] at E hE hle
  have hEfp := B.isFppfCovering_of_isCovering hE
  have hEfp' : (E.map B.inclusion).presieve₀ ∈
      Scheme.fppfPrecoverage (B.inclusion.obj (B.obj hk)) := by
    simpa [AlgebraicGeometry.IsFppfCovering, Scheme.fppfPrecoverage,
      PreZeroHypercover.presieve₀_map] using hEfp
  let P : MorphismProperty Scheme.{u} := @Flat ⊓ @LocallyOfFinitePresentation
  obtain ⟨hcover, hprop⟩ := (Scheme.ofArrows_mem_precoverage_iff P).mp hEfp'
  obtain ⟨i, v, _⟩ := hcover (Classical.arbitrary (Spec (.of k)))
  refine ⟨Over.mk (E.f i), ⟨v⟩, (hprop i).1, (hprop i).2, ?_⟩
  have hRi := (Sieve.overEquiv_iff R (E.f i)).mp (hle _ _ ⟨i⟩)
  have hs' := hs hRi
  have hcomp : E.f i ≫ T.hom = E.f i := Category.comp_id _
  rw [hcomp] at hs'
  exact hs'

private theorem ofArrows_mem_topology_of_fppf
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T : AlgebraicGeometry.BigFppfOver B S hS}
    {I : Type (u + 1)} (V : I → AlgebraicGeometry.BigFppfOver B S hS)
    (q : ∀ i, V i ⟶ T)
    (hc : ∀ t : T.left.obj, ∃ i, ∃ v : (V i).left.obj, B.inclusion.map (q i).left v = t)
    (hf : ∀ i, Flat (B.inclusion.map (q i).left) ∧
      LocallyOfFinitePresentation (B.inclusion.map (q i).left)) :
    Sieve.ofArrows V q ∈ AlgebraicGeometry.BigFppfOver.topology B S hS T := by
  rw [AlgebraicGeometry.BigFppfOver.topology, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_ofArrows]
  let E : PreZeroHypercover.{u + 1} T.left := ⟨I, fun i => (V i).left, fun i => (q i).left⟩
  apply generate_mem_topology_of_isFppfCovering B (E := E)
  rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff]
  rw [← PreZeroHypercover.presieve₀_map]
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  exact ⟨hc, hf⟩

private theorem singleton_cover_of_fppf
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (V : AlgebraicGeometry.BigFppfOver B S hS)
    [Flat (B.inclusion.map V.hom)]
    [LocallyOfFinitePresentation (B.inclusion.map V.hom)]
    [Surjective (B.inclusion.map V.hom)] :
    (PreZeroHypercover.singleton.{u + 1} (Over.mkIdTerminal.from V)).sieve₀ ∈
      AlgebraicGeometry.BigFppfOver.topology B S hS (Over.mk (𝟙 (B.obj hS))) := by
  let E := PreZeroHypercover.singleton.{u + 1} (Over.mkIdTerminal.from V)
  change Sieve.ofArrows E.X E.f ∈ _
  exact ofArrows_mem_topology_of_fppf B S hS E.X E.f
    (singleton_surjective_flat_lfp B S hS V).1 (singleton_surjective_flat_lfp B S hS V).2

private noncomputable def terminalYonedaIso
    (𝒞 : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) :
    yoneda.obj (Over.mk (𝟙 (𝒞.obj hS)) : AlgebraicGeometry.BigFppfOver 𝒞 S hS) ≅
      ⊤_ ((AlgebraicGeometry.BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) :=
  ((Over.mkIdTerminal (X := 𝒞.obj hS)).isTerminalObj yoneda _).uniqueUpToIso terminalIsTerminal

private theorem nsmul_extClass_eq_zero_of_lift
    {D : Type*} [Category D] [Abelian D] [HasExt.{w} D]
    (S : ShortComplex D) (hS : S.ShortExact) (n : ℕ)
    (f : S.X₃ ⟶ S.X₂) (hf : f ≫ S.g = n • 𝟙 S.X₃) :
    n • hS.extClass = 0 := by
  let δ : (S.X₃ ⟶ S.X₃) →+ Abelian.Ext S.X₃ S.X₁ 1 :=
    (hS.extClass.postcomp S.X₃ (zero_add 1)).comp
      Abelian.Ext.addEquiv₀.symm.toAddMonoidHom
  have hδ : δ (n • 𝟙 S.X₃) = 0 :=
    (Stacks.Cohomology.Torsors.ext_one_boundary_eq_zero_iff_lift S hS S.X₃ _).2 ⟨f, hf⟩
  have hδone : δ (𝟙 S.X₃) = hS.extClass := Abelian.Ext.mk₀_id_comp _
  rwa [map_nsmul, hδone] at hδ

private theorem nsmul_torsorClass_eq_zero_of_sectionFamily
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
    (H : Sheaf J AddCommGrpCat.{u}) (F : Stacks.Cohomology.Torsors.AbelianTorsor H) (n : ℕ)
    (s : ∀ U, (Stacks.Cohomology.Torsors.torsorPushoutMiddle H F).obj.obj U)
    (hs : ∀ {U V} (f : U ⟶ V),
      (Stacks.Cohomology.Torsors.torsorPushoutMiddle H F).obj.map f (s U) = s V)
    (hp : ∀ U, (Stacks.Cohomology.Torsors.torsorPushoutProjection H F).hom.app U (s U) =
      n • (Stacks.Cohomology.Torsors.constantUnit (J := J)).app U (⟨1⟩ : ULift.{u} ℤ)) :
    n • Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 H (Quotient.mk _ F) = 0 := by
  let S := Stacks.Cohomology.Torsors.torsorPushoutComplex H F
  let r := Stacks.Cohomology.Torsors.morphismOfSectionFamily S.X₂.obj s hs
  let adj := sheafificationAdjunction J AddCommGrpCat.{u}
  let f : S.X₃ ⟶ S.X₂ := (adj.homEquiv _ _).symm r
  apply nsmul_extClass_eq_zero_of_lift S
    (Stacks.Cohomology.Torsors.torsorPushoutComplex_shortExact H F) n f
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  apply Stacks.Cohomology.Torsors.liftedInt_hom_ext
  change S.g.hom.app U (r.app U ⟨1⟩) = _
  rw [Stacks.Cohomology.Torsors.morphismOfSectionFamily_one]
  change (Stacks.Cohomology.Torsors.torsorPushoutProjection H F).hom.app U (s U) = _
  rw [hp U]
  let P := (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  change n • ((adj.homEquiv P ((presheafToSheaf J AddCommGrpCat.{u}).obj P))
    (𝟙 _)).app U ⟨1⟩ =
      ((adj.homEquiv P ((presheafToSheaf J AddCommGrpCat.{u}).obj P))
        (n • 𝟙 _)).app U ⟨1⟩
  rw [adj.homEquiv_unit, adj.homEquiv_unit]
  rfl

private theorem nsmul_torsorClass_eq_zero_of_locally_permuted_sections
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
    (H : Sheaf J AddCommGrpCat.{u}) (F : Stacks.Cohomology.Torsors.AbelianTorsor H)
    {T : C} (hT : IsTerminal T) (R : J.Cover T) (n : ℕ)
    (p : ∀ I : R.Arrow, Fin n → F.1.presheaf.obj (Opposite.op I.Y))
    (hp : ∀ {I₁ I₂ : R.Arrow} (r : I₁.Relation I₂),
      ∃ R' : J.Cover r.Z, ∀ I : R'.Arrow, ∃ e : Fin n ≃ Fin n, ∀ i,
        F.1.presheaf.map (I.f ≫ r.g₁).op (p I₁ i) =
          F.1.presheaf.map (I.f ≫ r.g₂).op (p I₂ (e i))) :
    n • Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 H (Quotient.mk _ F) = 0 := by
  classical
  let E := Stacks.Cohomology.Torsors.torsorPushoutMiddle H F
  let Q := (Stacks.Cohomology.Torsors.torsorPushoutComplex H F).X₃
  let η : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ Q.obj :=
    Stacks.Cohomology.Torsors.constantUnit (J := J)
  let π : E ⟶ Q := Stacks.Cohomology.Torsors.torsorPushoutProjection H F
  let g := Stacks.Cohomology.Torsors.torsorPushoutGenerator H F
  let z (I : R.Arrow) : E.obj.obj (Opposite.op I.Y) :=
    ∑ i, g.app (Opposite.op I.Y) (p I i)
  let a (I : R.Arrow) : AddCommGrpCat.of (ULift.{u} ℤ) ⟶
      E.obj.obj (Opposite.op I.Y) :=
    AddCommGrpCat.ofHom ((uliftZMultiplesHom _) (z I))
  have ha : ∀ {I₁ I₂ : R.Arrow} (r : I₁.Relation I₂),
      a I₁ ≫ E.obj.map r.g₁.op = a I₂ ≫ E.obj.map r.g₂.op := by
    intro I₁ I₂ r
    obtain ⟨R', hp'⟩ := hp r
    apply E.property.hom_ext R'
    intro I
    simp only [Category.assoc, ← E.obj.map_comp]
    apply Stacks.Cohomology.Torsors.liftedInt_hom_ext
    change E.obj.map (I.f ≫ r.g₁).op ((uliftZMultiplesHom _) (z I₁) ⟨1⟩) =
      E.obj.map (I.f ≫ r.g₂).op ((uliftZMultiplesHom _) (z I₂) ⟨1⟩)
    simp only [uliftZMultiplesHom_apply_apply]
    change E.obj.map (I.f ≫ r.g₁).op ((1 : ℤ) • z I₁) =
      E.obj.map (I.f ≫ r.g₂).op ((1 : ℤ) • z I₂)
    rw [one_zsmul, one_zsmul]
    dsimp only [z]
    rw [map_sum, map_sum]
    obtain ⟨e, he⟩ := hp' I
    apply Fintype.sum_equiv e
    intro i
    change (E.obj ⋙ forget AddCommGrpCat).map (I.f ≫ r.g₁).op (g.app _ (p I₁ i)) =
      (E.obj ⋙ forget AddCommGrpCat).map (I.f ≫ r.g₂).op (g.app _ (p I₂ (e i)))
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, he i]
  let q := E.property.amalgamate R a @ha
  have hq : q ≫ π.hom.app (Opposite.op T) =
      n • η.app (Opposite.op T) := by
    apply Q.property.hom_ext R
    intro I
    rw [Category.assoc, ← π.hom.naturality, ← Category.assoc]
    rw [E.property.amalgamate_map R a @ha I]
    rw [Preadditive.nsmul_comp, ← η.naturality]
    simp only [Functor.const_obj_map]
    apply Stacks.Cohomology.Torsors.liftedInt_hom_ext
    change π.hom.app _ ((uliftZMultiplesHom _) (z I) ⟨1⟩) =
      n • η.app (Opposite.op I.Y) ⟨1⟩
    simp only [uliftZMultiplesHom_apply_apply]
    change π.hom.app _ ((1 : ℤ) • z I) = _
    rw [one_zsmul]
    dsimp only [z]
    rw [map_sum]
    have hg (i : Fin n) : π.hom.app _ (g.app _ (p I i)) =
        η.app (Opposite.op I.Y) ⟨1⟩ :=
      (Stacks.Cohomology.Torsors.torsorPushoutGenerator_projection H F _ _).trans
        (Stacks.Cohomology.Torsors.constantUnit_app_one _).symm
    simp only [hg, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  let s (U : Cᵒᵖ) : E.obj.obj U :=
    E.obj.map (hT.from U.unop).op (q ⟨1⟩)
  have hs : ∀ {U V : Cᵒᵖ} (f : U ⟶ V), E.obj.map f (s U) = s V := by
    intro U V f
    dsimp only [s]
    rw [← ConcreteCategory.comp_apply, ← E.obj.map_comp]
    rw [show (hT.from U.unop).op ≫ f = (hT.from V.unop).op from
      Quiver.Hom.unop_inj (hT.hom_ext _ _)]
  apply nsmul_torsorClass_eq_zero_of_sectionFamily H F n s hs
  intro U
  change π.hom.app U (E.obj.map (hT.from U.unop).op (q ⟨1⟩)) = _
  rw [NatTrans.naturality_apply]
  have hq1 := ConcreteCategory.congr_hom hq (⟨1⟩ : ULift.{u} ℤ)
  change π.hom.app (Opposite.op T) (q ⟨1⟩) =
    n • (Stacks.Cohomology.Torsors.constantUnit (J := J)).app (Opposite.op T) ⟨1⟩ at hq1
  rw [hq1, map_nsmul]
  congr 1
  exact Stacks.Cohomology.Torsors.sectionFamilyOfMorphism_naturality Q.obj
    (Stacks.Cohomology.Torsors.constantUnit (J := J)) (hT.from U.unop).op

private noncomputable def torsorProductIso
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
    (H : Sheaf J AddCommGrpCat.{u}) (F : Stacks.Cohomology.Torsors.AbelianTorsor H)
    (U : C) (s : F.1.presheaf.obj (Opposite.op U)) :
    yoneda.obj U ⨯ (H.obj ⋙ forget AddCommGrpCat) ≅
      yoneda.obj U ⨯ F.1.presheaf := by
  let A := yoneda.obj U ⨯ (H.obj ⋙ forget AddCommGrpCat)
  let P := yoneda.obj U ⨯ F.1.presheaf
  let a : A ⟶ F.1.presheaf :=
    { app := fun V => ↾fun t => F.1.act V
        (Multiplicative.ofAdd ((prod.snd : A ⟶ _).app V t))
        (F.1.presheaf.map ((prod.fst : A ⟶ _).app V t).op s)
      naturality := by
        intro V W f
        ext t
        change F.1.act W
          (Multiplicative.ofAdd ((prod.snd : A ⟶ _).app W (A.map f t)))
          (F.1.presheaf.map ((prod.fst : A ⟶ _).app W (A.map f t)).op s) =
          F.1.presheaf.map f (F.1.act V
            (Multiplicative.ofAdd ((prod.snd : A ⟶ _).app V t))
            (F.1.presheaf.map ((prod.fst : A ⟶ _).app V t).op s))
        refine Eq.trans ?_ (F.1.naturality f _ _).symm
        rw [NatTrans.naturality_apply (prod.snd : A ⟶ _)]
        rw [NatTrans.naturality_apply (prod.fst : A ⟶ _)]
        congr 1
        change F.1.presheaf.map
          (f.unop ≫ (prod.fst : A ⟶ _).app V t).op s = _
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
        rfl }
  let d : P ⟶ H.obj ⋙ forget AddCommGrpCat :=
    { app := fun V => ↾fun t => Stacks.Cohomology.Torsors.torsorDifference H F V
        ((prod.snd : P ⟶ _).app V t)
        (F.1.presheaf.map ((prod.fst : P ⟶ _).app V t).op s)
      naturality := by
        intro V W f
        ext t
        change Stacks.Cohomology.Torsors.torsorDifference H F W
          ((prod.snd : P ⟶ _).app W (P.map f t))
          (F.1.presheaf.map ((prod.fst : P ⟶ _).app W (P.map f t)).op s) =
          H.obj.map f (Stacks.Cohomology.Torsors.torsorDifference H F V
            ((prod.snd : P ⟶ _).app V t)
            (F.1.presheaf.map ((prod.fst : P ⟶ _).app V t).op s))
        rw [Stacks.Cohomology.Torsors.torsorDifference_naturality H F]
        rw [NatTrans.naturality_apply (prod.snd : P ⟶ _)]
        rw [NatTrans.naturality_apply (prod.fst : P ⟶ _)]
        congr 1
        change F.1.presheaf.map
          (f.unop ≫ (prod.fst : P ⟶ _).app V t).op s = _
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
        rfl }
  refine ⟨prod.lift prod.fst a, prod.lift prod.fst d, ?_, ?_⟩
  · apply prod.hom_ext
    · simp
    · simp only [Category.assoc, prod.lift_snd, Category.id_comp]
      ext V t
      change Stacks.Cohomology.Torsors.torsorDifference H F V
        ((prod.snd : P ⟶ _).app V ((prod.lift prod.fst a).app V t))
        (F.1.presheaf.map
          ((prod.fst : P ⟶ _).app V ((prod.lift prod.fst a).app V t)).op s) = _
      have hfst := ConcreteCategory.congr_hom
        (NatTrans.congr_app (prod.lift_fst (prod.fst : A ⟶ _) a) V) t
      have hsnd := ConcreteCategory.congr_hom
        (NatTrans.congr_app (prod.lift_snd (prod.fst : A ⟶ _) a) V) t
      change (prod.fst : P ⟶ _).app V ((prod.lift prod.fst a).app V t) = _ at hfst
      change (prod.snd : P ⟶ _).app V ((prod.lift prod.fst a).app V t) = _ at hsnd
      rw [hfst, hsnd]
      exact Stacks.Cohomology.Torsors.torsorDifference_eq_of_act H F V _ _ _ rfl
  · apply prod.hom_ext
    · simp
    · simp only [Category.assoc, prod.lift_snd, Category.id_comp]
      ext V t
      change F.1.act V
        (Multiplicative.ofAdd ((prod.snd : A ⟶ _).app V ((prod.lift prod.fst d).app V t)))
        (F.1.presheaf.map
          ((prod.fst : A ⟶ _).app V ((prod.lift prod.fst d).app V t)).op s) = _
      have hfst := ConcreteCategory.congr_hom
        (NatTrans.congr_app (prod.lift_fst (prod.fst : P ⟶ _) d) V) t
      have hsnd := ConcreteCategory.congr_hom
        (NatTrans.congr_app (prod.lift_snd (prod.fst : P ⟶ _) d) V) t
      change (prod.fst : A ⟶ _).app V ((prod.lift prod.fst d).app V t) = _ at hfst
      change (prod.snd : A ⟶ _).app V ((prod.lift prod.fst d).app V t) = _ at hsnd
      rw [hfst, hsnd]
      exact Stacks.Cohomology.Torsors.torsorDifference_act H F V _ _

private theorem isAlgebraicSpace_torsor
    (k : Type u) [Field k] (B : AlgebraicGeometry.BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology B (Spec (.of k)) hk) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (AlgebraicGeometry.BigFppfOver.topology B (Spec (.of k)) hk)
      AddCommGrpCat.{u})]
    (G : Sheaf (AlgebraicGeometry.BigFppfOver.topology B (Spec (.of k)) hk)
      AddCommGrpCat.{u})
    (hG : AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk
      (G.obj ⋙ forget AddCommGrpCat))
    (F : Stacks.Cohomology.Torsors.AbelianTorsor G) :
    AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk F.1.presheaf := by
  classical
  obtain ⟨V, ⟨v⟩, hvFlat, hvLfp, ⟨s⟩⟩ :=
    exists_nonempty_fppf_torsor_section k B hk _ F.1 F.2
  have : Surjective (B.inclusion.map V.hom) :=
    ⟨fun x => ⟨v, @Subsingleton.elim (Spec (.of k)) inferInstance _ _⟩⟩
  let E := PreZeroHypercover.singleton.{u + 1} (Over.mkIdTerminal.from V)
  have hProd : AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk
      (yoneda.obj V ⨯ F.1.presheaf) :=
    AlgebraicGeometry.Space.isAlgebraicSpace_of_iso B (Spec (.of k)) hk (torsorProductIso G F V s)
      (AlgebraicGeometry.isAlgebraicSpace_prod B (Spec (.of k)) hk
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of k)) hk V) hG)
  let Q : Sheaf (AlgebraicGeometry.BigFppfOver.topology B (Spec (.of k)) hk) (Type u) :=
    ⟨yoneda.obj V ⨯ F.1.presheaf, hProd.isSheaf⟩
  exact AlgebraicGeometry.isAlgebraicSpace_of_isCovering F.1.isSheaf E
    (isCovering_singleton_of_fppf B (Spec (.of k)) hk V) (fun _ => hProd)
    (G := Q) (fun _ => 𝟙 Q) (isColimit_cofan_unique Q) hProd

private theorem isSmooth_comp_iso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (e : Y ≅ Z) (hf : AlgebraicGeometry.Space.IsSmooth B S hS f) :
    AlgebraicGeometry.Space.IsSmooth B S hS (f ≫ e.hom) := by
  intro U V a b h ha hb hh
  let Q := (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf
  have hb' : Q (b ≫ e.inv) :=
    MorphismProperty.RespectsIso.postcomp Q e.inv b hb
  apply hf U V a (b ≫ e.inv) h ha hb'
  have heq := congrArg (fun t => t ≫ e.inv) hh
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using heq

private theorem isSmooth_torsor
    (k : Type u) [Field k] (B : AlgebraicGeometry.BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology B (Spec (.of k)) hk) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (AlgebraicGeometry.BigFppfOver.topology B (Spec (.of k)) hk)
      AddCommGrpCat.{u})]
    (G : Sheaf (AlgebraicGeometry.BigFppfOver.topology B (Spec (.of k)) hk)
      AddCommGrpCat.{u})
    (hG : AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk
      (G.obj ⋙ forget AddCommGrpCat))
    (hSmooth : AlgebraicGeometry.Space.IsSmooth B (Spec (.of k)) hk
      (terminal.from (G.obj ⋙ forget AddCommGrpCat)))
    (F : Stacks.Cohomology.Torsors.AbelianTorsor G) :
    AlgebraicGeometry.Space.IsSmooth B (Spec (.of k)) hk (terminal.from F.1.presheaf) := by
  classical
  let C := AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk
  let T : C := Over.mk (𝟙 (B.obj hk))
  let eT := terminalYonedaIso B (Spec (.of k)) hk
  have ht : IsTerminal (yoneda.obj T) := IsTerminal.ofIso terminalIsTerminal eT.symm
  let Tsp := AlgebraicGeometry.schemeSpace T
  let Gsp : AlgebraicGeometry.AlgebraicSpaces B (Spec (.of k)) hk := ⟨_, hG⟩
  have hF := isAlgebraicSpace_torsor k B hk G hG F
  let Fsp : AlgebraicGeometry.AlgebraicSpaces B (Spec (.of k)) hk := ⟨_, hF⟩
  let f : Fsp ⟶ Tsp := ObjectProperty.homMk (ht.from _)
  let g : Gsp ⟶ Tsp := ObjectProperty.homMk (ht.from _)
  let P := AlgebraicGeometry.Space.smoothMorphismProperty B (Spec (.of k)) hk
  let : P.IsLocalAtTarget
      (AlgebraicGeometry.Space.Topology.precoverage.{u, u + 1} .fpqc B (Spec (.of k)) hk) :=
    AlgebraicGeometry.Space.smooth_isLocalAtTarget_fpqc.{u, u + 1} B (Spec (.of k)) hk
  -- supply `RespectsIso` from base change, so that instance search does not reach it through a
  -- locality instance of free universe, which would leave a universe metavariable
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hg : P g := by
    have hg' := isSmooth_comp_iso B (Spec (.of k)) hk _ eT.symm hSmooth
    have heq : terminal.from (G.obj ⋙ forget AddCommGrpCat) ≫ eT.inv = ht.from _ :=
      ht.hom_ext _ _
    rwa [Iso.symm_hom, heq] at hg'
  obtain ⟨V, ⟨v⟩, hvFlat, hvLfp, ⟨s⟩⟩ :=
    exists_nonempty_fppf_torsor_section k B hk _ F.1 F.2
  have hvSurj : Surjective (B.inclusion.map V.hom) :=
    ⟨fun x => ⟨v, @Subsingleton.elim (Spec (.of k)) inferInstance _ _⟩⟩
  let Vsp := AlgebraicGeometry.schemeSpace V
  let q : Vsp ⟶ Tsp := ObjectProperty.homMk (ht.from _)
  let E := PreZeroHypercover.singleton.{u + 1} (Over.mkIdTerminal.from V)
  have hEcov : (E.map (AlgebraicGeometry.BigFppfOver.toScheme B (Spec (.of k)) hk)).presieve₀ ∈
      Scheme.fppfPrecoverage (Spec (.of k)) := by
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    exact singleton_surjective_flat_lfp B (Spec (.of k)) hk V
  have hcov : AlgebraicGeometry.Space.IsFpqcCovering B (Spec (.of k)) hk
      (fun _ : PUnit.{u + 2} => q.hom) := by
    have hc := schemeFppfCover_isFpqcCovering B (Spec (.of k)) hk E hEcov
    have he (i : E.I₀) : (AlgebraicGeometry.schemeSpaceMap (E.f i)).hom = q.hom :=
      ht.hom_ext _ _
    simp only [he] at hc
    exact hc
  let hPG := AlgebraicGeometry.isAlgebraicSpace_prod B (Spec (.of k)) hk Vsp.property hG
  let hPF := AlgebraicGeometry.isAlgebraicSpace_prod B (Spec (.of k)) hk Vsp.property hF
  let PG : AlgebraicGeometry.AlgebraicSpaces B (Spec (.of k)) hk := ⟨Vsp.obj ⨯ Gsp.obj, hPG⟩
  let PF : AlgebraicGeometry.AlgebraicSpaces B (Spec (.of k)) hk := ⟨Vsp.obj ⨯ Fsp.obj, hPF⟩
  let qG : PG ⟶ Vsp := ObjectProperty.homMk prod.fst
  let qF : PF ⟶ Vsp := ObjectProperty.homMk prod.fst
  let pG : PG ⟶ Gsp := ObjectProperty.homMk prod.snd
  let pF : PF ⟶ Fsp := ObjectProperty.homMk prod.snd
  have hpbG : IsPullback pG qG g q := by
    refine IsPullback.of_map (ObjectProperty.ι _) ?_ ?_
    · apply ObjectProperty.hom_ext
      exact ht.hom_ext _ _
    · exact (IsPullback.of_is_product (limit.isLimit (pair Vsp.obj Gsp.obj)) ht).flip
  have hpbF : IsPullback pF qF f q := by
    refine IsPullback.of_map (ObjectProperty.ι _) ?_ ?_
    · apply ObjectProperty.hom_ext
      exact ht.hom_ext _ _
    · exact (IsPullback.of_is_product (limit.isLimit (pair Vsp.obj Fsp.obj)) ht).flip
  have hqG : P qG :=
    (AlgebraicGeometry.Space.isSmooth_isStableUnderBaseChange B (Spec (.of k)) hk).of_isPullback
      hpbG hg
  let e : PG ≅ PF := ObjectProperty.isoMk _ (torsorProductIso G F V s)
  have he : e.hom ≫ qF = qG := by
    apply ObjectProperty.hom_ext
    change (torsorProductIso G F V s).hom ≫ prod.fst = prod.fst
    exact prod.lift_fst _ _
  have hqF : P qF := by
    apply (MorphismProperty.cancel_left_of_respectsIso P e.hom qF).mp
    rwa [he]
  have hf : P f := by
    apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (P := P)
      (K := AlgebraicGeometry.Space.Topology.precoverage.{u, u + 1} .fpqc B (Spec (.of k)) hk)
      (R := Presieve.ofArrows (fun _ : PUnit.{u + 2} => Vsp) (fun _ => q))
      ⟨_, _, _, rfl, Tsp.property, (fun _ => Vsp.property), hcov⟩
    rintro _ _ _ ⟨i⟩
    have hh : P (hpbF.isoPullback.inv ≫ qF) :=
      MorphismProperty.RespectsIso.precomp P hpbF.isoPullback.inv qF hqF
    rwa [hpbF.isoPullback_inv_snd] at hh
  have hf' := isSmooth_comp_iso B (Spec (.of k)) hk f.hom eT hf
  have heq : f.hom ≫ eT.hom = terminal.from F.1.presheaf := terminalIsTerminal.hom_ext _ _
  rwa [heq] at hf'

private theorem nonempty_points_of_section
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (V : AlgebraicGeometry.BigFppfOver B S hS) (v : V.left.obj)
    (s : X.obj (Opposite.op V)) : Nonempty (AlgebraicGeometry.Space.points B S hS X) := by
  have hK : B.Contains (Spec (V.left.obj.residueField v)) := by
    have : Mono (V.left.obj.fromSpecResidueField v) := inferInstance
    have : QuasiCompact (V.left.obj.fromSpecResidueField v) := by
      rw [quasiCompact_iff_forall_isAffineOpen]
      intro W hW
      exact (Set.toFinite (V.left.obj.fromSpecResidueField v ⁻¹' (W : Set V.left.obj))).isCompact
    exact lt_of_le_of_lt
      (Scheme.size_le_of_mono_quasiCompact (V.left.obj.fromSpecResidueField v)) V.left.property
  let i : B.obj hK ⟶ V.left := ObjectProperty.homMk (V.left.obj.fromSpecResidueField v)
  let W : AlgebraicGeometry.BigFppfOver B S hS := Over.mk (i ≫ V.hom)
  let t : W ⟶ V := Over.homMk i
  let p : AlgebraicGeometry.Space.FieldValuedPoint B S hS X :=
    ⟨V.left.obj.residueField v, hK, B.inclusion.map (i ≫ V.hom), X.map t.op s⟩
  exact ⟨p.class B S hS X⟩

private theorem exists_finite_separable_point_of_nonempty_smooth
    (k : Type u) [Field k] (B : AlgebraicGeometry.BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    (X : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hf : AlgebraicGeometry.Space.IsSmooth B (Spec (.of k)) hk f)
    [Nonempty (AlgebraicGeometry.Space.points B (Spec (.of k)) hk X)] :
    ∃ (p : AlgebraicGeometry.Space.FieldValuedPoint B (Spec (.of k)) hk X)
      (a : Algebra k p.carrier),
      (letI : Algebra k p.carrier := a
       Module.Finite k p.carrier ∧ Algebra.IsSeparable k p.carrier) ∧
      p.toBase = Spec.map (CommRingCat.ofHom (algebraMap k p.carrier)) := by
  obtain ⟨-, p, -, a, hfin, hsep, hbase⟩ :=
    (AlgebraicGeometry.Space.dense_setOf_class_finiteSeparable_of_isSmooth k B hk hX f hf).nonempty
  exact ⟨p, a, ⟨hfin, hsep⟩, hbase⟩

private theorem exists_finite_separable_torsor_point
    (k : Type u) [Field k] (B : AlgebraicGeometry.BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology B (Spec (.of k)) hk) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (AlgebraicGeometry.BigFppfOver.topology B (Spec (.of k)) hk)
      AddCommGrpCat.{u})]
    (G : Sheaf (AlgebraicGeometry.BigFppfOver.topology B (Spec (.of k)) hk)
      AddCommGrpCat.{u})
    (hG : AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk
      (G.obj ⋙ forget AddCommGrpCat))
    (hSmooth : AlgebraicGeometry.Space.IsSmooth B (Spec (.of k)) hk
      (terminal.from (G.obj ⋙ forget AddCommGrpCat)))
    (F : Stacks.Cohomology.Torsors.AbelianTorsor G) :
    ∃ (p : AlgebraicGeometry.Space.FieldValuedPoint B (Spec (.of k)) hk F.1.presheaf)
      (a : Algebra k p.carrier),
      (letI : Algebra k p.carrier := a
       Module.Finite k p.carrier ∧ Algebra.IsSeparable k p.carrier) ∧
      p.toBase = Spec.map (CommRingCat.ofHom (algebraMap k p.carrier)) := by
  obtain ⟨V, ⟨v⟩, _, _, ⟨s⟩⟩ :=
    exists_nonempty_fppf_torsor_section k B hk _ F.1 F.2
  have : Nonempty (AlgebraicGeometry.Space.points B (Spec (.of k)) hk F.1.presheaf) :=
    nonempty_points_of_section B (Spec (.of k)) hk F.1.presheaf V v s
  exact exists_finite_separable_point_of_nonempty_smooth k B hk F.1.presheaf
    (isAlgebraicSpace_torsor k B hk G hG F) _
    (isSmooth_comp_iso B (Spec (.of k)) hk _ (terminalYonedaIso B (Spec (.of k)) hk).symm
      (isSmooth_torsor k B hk G hG hSmooth F))

private noncomputable def splitSection {X Y : Scheme.{u}}
    (q : X ⟶ Y) (U : X.Opens) [IsIso (U.ι ≫ q)] : Y ⟶ X :=
  inv (U.ι ≫ q) ≫ U.ι

private theorem splitSection_comp {X Y : Scheme.{u}}
    (q : X ⟶ Y) (U : X.Opens) [IsIso (U.ι ≫ q)] :
    splitSection q U ≫ q = 𝟙 Y := by
  exact IsIso.inv_hom_id (U.ι ≫ q)

private theorem splitSection_mem {X Y : Scheme.{u}}
    (q : X ⟶ Y) (U : X.Opens) [IsIso (U.ι ≫ q)] (y : Y) :
    splitSection q U y ∈ U := by
  change U.ι ((inv (U.ι ≫ q)) y) ∈ U
  exact ((inv (U.ι ≫ q)) y).2

private theorem restrict_eq_splitSection {X Y Z : Scheme.{u}}
    (q : X ⟶ Y) (U : X.Opens) [IsIso (U.ι ≫ q)]
    (h : Z ⟶ X) (W : Z.Opens) (hW : W ≤ h ⁻¹ᵁ U) :
    W.ι ≫ h = W.ι ≫ h ≫ q ≫ splitSection q U := by
  let l := h.resLE U W hW
  have hl : l ≫ U.ι = W.ι ≫ h := Scheme.Hom.resLE_comp_ι h hW
  have hq : (U.ι ≫ q) ≫ splitSection q U = U.ι := by
    simp only [splitSection, IsIso.hom_inv_id_assoc]
  calc
    W.ι ≫ h = l ≫ U.ι := hl.symm
    _ = l ≫ (U.ι ≫ q) ≫ splitSection q U := by rw [hq]
    _ = W.ι ≫ h ≫ q ≫ splitSection q U := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ q ≫ splitSection q U) hl

-- Comparing the finite family of pullback morphisms requires additional elaboration steps.
private theorem locally_permuted_split_sections
    {X Y S Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {n : ℕ} (U : Fin n → (pullback f g).Opens)
    (hcover : sSup (Set.range U) = ⊤)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    [∀ i, IsIso ((U i).ι ≫ pullback.snd f g)]
    (a b : Z ⟶ Y) (hab : a ≫ g = b ≫ g) (z : Z) :
    ∃ (W : Z.Opens), z ∈ W ∧ ∃ e : Fin n ≃ Fin n, ∀ i,
      W.ι ≫ a ≫ splitSection (pullback.snd f g) (U i) ≫ pullback.fst f g =
        W.ι ≫ b ≫ splitSection (pullback.snd f g) (U (e i)) ≫ pullback.fst f g := by
  classical
  let s (i : Fin n) := splitSection (pullback.snd f g) (U i)
  have hs (i : Fin n) : s i ≫ pullback.snd f g = 𝟙 Y := splitSection_comp _ _
  have hsf (i : Fin n) : s i ≫ pullback.fst f g ≫ f = g := by
    rw [pullback.condition, ← Category.assoc, hs, Category.id_comp]
  let c (i : Fin n) : Z ⟶ pullback f g :=
    pullback.lift (a ≫ s i ≫ pullback.fst f g) b (by
      simpa only [Category.assoc, hsf] using hab)
  have hj (i : Fin n) : ∃ j, c i z ∈ U j := by
    have hmem : c i z ∈ sSup (Set.range U) := by rw [hcover]; trivial
    obtain ⟨V, ⟨j, rfl⟩, hj⟩ := TopologicalSpace.Opens.mem_sSup.mp hmem
    exact ⟨j, hj⟩
  choose j hj using hj
  let W : Z.Opens := Finset.univ.inf (fun i => c i ⁻¹ᵁ U (j i))
  have hz : z ∈ W := by
    change z ∈ (W : Set Z)
    rw [show (W : Set Z) = Finset.univ.inf
      (fun i => ((c i ⁻¹ᵁ U (j i) : Z.Opens) : Set Z)) from
        TopologicalSpace.Opens.coe_finset_inf _ _]
    simpa using hj
  have hWi (i : Fin n) : W ≤ c i ⁻¹ᵁ U (j i) := Finset.inf_le (Finset.mem_univ i)
  have hc (i : Fin n) : W.ι ≫ c i = W.ι ≫ b ≫ s (j i) := by
    have h := restrict_eq_splitSection (pullback.snd f g) (U (j i)) (c i) W (hWi i)
    simpa only [Category.assoc, c, pullback.lift_snd_assoc] using h
  have ht (i : Fin n) : W.ι ≫ a ≫ s i ≫ pullback.fst f g =
      W.ι ≫ b ≫ s (j i) ≫ pullback.fst f g := by
    have h := congrArg (fun t => t ≫ pullback.fst f g) (hc i)
    simpa only [Category.assoc, c, pullback.lift_fst] using h
  have hinj : Function.Injective j := by
    intro i i' hij
    by_contra hii
    have he : W.ι ≫ a ≫ s i = W.ι ≫ a ≫ s i' := by
      apply pullback.hom_ext
      · have hti := ht i
        rw [hij] at hti
        simpa only [Category.assoc] using hti.trans (ht i').symm
      · simp only [Category.assoc, hs, Category.comp_id]
    have hep := congrArg (fun m : W.toScheme ⟶ pullback f g => m ⟨z, hz⟩) he
    have hi : (W.ι ≫ a ≫ s i) (⟨z, hz⟩ : W) ∈ U i :=
      splitSection_mem (pullback.snd f g) (U i) (a (W.ι ⟨z, hz⟩))
    have hi' : (W.ι ≫ a ≫ s i') (⟨z, hz⟩ : W) ∈ U i' :=
      splitSection_mem (pullback.snd f g) (U i') (a (W.ι ⟨z, hz⟩))
    rw [hep] at hi
    have hmem : (W.ι ≫ a ≫ s i') (⟨z, hz⟩ : W) ∈ U i ⊓ U i' := ⟨hi, hi'⟩
    rw [(hdisj hii).eq_bot] at hmem
    exact hmem
  let e : Fin n ≃ Fin n := Equiv.ofBijective j ⟨hinj, Finite.surjective_of_injective hinj⟩
  exact ⟨W, hz, e, ht⟩

private theorem nsmul_torsorClass_eq_zero_of_local_permutations
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
    (H : Sheaf J AddCommGrpCat.{u}) (F : Stacks.Cohomology.Torsors.AbelianTorsor H)
    {T V L : C} (hT : IsTerminal T) (R : J.Cover T)
    (l : ∀ I : R.Arrow, I.Y ⟶ V) (n : ℕ) (t : Fin n → (V ⟶ L))
    (s : F.1.presheaf.obj (Opposite.op L))
    (hperm : ∀ {Z : C} (a b : Z ⟶ V), ∃ R' : J.Cover Z,
      ∀ I : R'.Arrow, ∃ e : Fin n ≃ Fin n, ∀ i,
        I.f ≫ a ≫ t i = I.f ≫ b ≫ t (e i)) :
    n • Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 H (Quotient.mk _ F) = 0 := by
  apply nsmul_torsorClass_eq_zero_of_locally_permuted_sections H F hT R n
    (fun I i => F.1.presheaf.map (l I ≫ t i).op s)
  intro I₁ I₂ r
  obtain ⟨R', hR'⟩ := hperm (r.g₁ ≫ l I₁) (r.g₂ ≫ l I₂)
  refine ⟨R', ?_⟩
  intro I
  obtain ⟨e, he⟩ := hR' I
  refine ⟨e, fun i => ?_⟩
  simp only [← ConcreteCategory.comp_apply, ← F.1.presheaf.map_comp, ← op_comp]
  apply congrArg (fun f : I.Y ⟶ L => F.1.presheaf.map f.op s)
  simpa only [Category.assoc] using he i

private theorem split_sections_locally_permuted_on_site
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (L V : AlgebraicGeometry.BigFppfOver B S hS) (Y : Scheme.{u}) (g : Y ⟶ S)
    {n : ℕ} (U : Fin n → (pullback (B.inclusion.map L.hom) g).Opens)
    (hcover : sSup (Set.range U) = ⊤)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    [∀ i, IsIso ((U i).ι ≫ pullback.snd (B.inclusion.map L.hom) g)]
    (j : V.left.obj ⟶ Y) (hj : j ≫ g = B.inclusion.map V.hom)
    (t : Fin n → (V ⟶ L))
    (ht : ∀ i, B.inclusion.map (t i).left =
      j ≫ splitSection (pullback.snd (B.inclusion.map L.hom) g) (U i) ≫
        pullback.fst (B.inclusion.map L.hom) g)
    {Z : AlgebraicGeometry.BigFppfOver B S hS} (a b : Z ⟶ V) :
    ∃ R : (AlgebraicGeometry.BigFppfOver.topology B S hS).Cover Z,
      ∀ I : R.Arrow, ∃ e : Fin n ≃ Fin n, ∀ i,
        I.f ≫ a ≫ t i = I.f ≫ b ≫ t (e i) := by
  classical
  let A := B.inclusion.map a.left ≫ j
  let C := B.inclusion.map b.left ≫ j
  have hab : A ≫ g = C ≫ g := by
    have ha := congrArg (fun f => B.inclusion.map f) (Over.w a)
    have hb := congrArg (fun f => B.inclusion.map f) (Over.w b)
    simp only [Functor.map_comp] at ha hb
    dsimp only [A, C]
    rw [Category.assoc, Category.assoc, hj, ha, hb]
  have hlocal (z : Z.left.obj) :=
    locally_permuted_split_sections (B.inclusion.map L.hom) g U hcover hdisj A C hab z
  choose W hz e he using hlocal
  let Wsite (z : Z.left.obj) : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk ((ObjectProperty.homMk (W z).ι :
      B.obj (Scheme.size_lt_of_isOpenImmersion (W z).ι Z.left.property) ⟶ Z.left) ≫ Z.hom)
  let q (z : Z.left.obj) : Wsite z ⟶ Z := Over.homMk (ObjectProperty.homMk (W z).ι)
  let R₀ := Sieve.ofArrows (fun z : ULift.{u + 1} Z.left.obj => Wsite z.down)
    (fun z => q z.down)
  have hR : R₀ ∈ AlgebraicGeometry.BigFppfOver.topology B S hS Z := by
    apply ofArrows_mem_topology_of_fppf
    · intro z
      exact ⟨ULift.up z, ⟨z, hz z⟩, rfl⟩
    · intro z
      change Flat (W z.down).ι ∧ LocallyOfFinitePresentation (W z.down).ι
      exact ⟨inferInstance, inferInstance⟩
  refine ⟨⟨R₀, hR⟩, ?_⟩
  intro I
  obtain ⟨z, d, hd⟩ := Sieve.ofArrows.exists I.hf
  refine ⟨e z.down, ?_⟩
  intro i
  have heq : q z.down ≫ a ≫ t i = q z.down ≫ b ≫ t (e z.down i) := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change B.inclusion.map ((q z.down).left ≫ a.left ≫ (t i).left) =
      B.inclusion.map ((q z.down).left ≫ b.left ≫ (t (e z.down i)).left)
    simp only [Functor.map_comp, ht]
    exact he z.down i
  rw [hd]
  simpa only [Category.assoc] using congrArg (fun f => d ≫ f) heq

/-- **Stacks 0AFA.** The first fppf cohomology group of a smooth commutative group algebraic
space over a field is torsion. -/
@[stacks 0AFA]
public theorem Space.fppfH1_isAddTorsion
    (k : Type u) [Field k]
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology B (Spec (.of k)) hk) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (AlgebraicGeometry.BigFppfOver.topology B (Spec (.of k)) hk)
      AddCommGrpCat.{u})]
    (G : Sheaf (AlgebraicGeometry.BigFppfOver.topology B (Spec (.of k)) hk)
      AddCommGrpCat.{u})
    (hG : AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk
      (G.obj ⋙ forget AddCommGrpCat))
    (hSmooth : AlgebraicGeometry.Space.IsSmooth B (Spec (.of k)) hk
      (terminal.from (G.obj ⋙ forget AddCommGrpCat))) :
    IsAddTorsion (Sheaf.H G 1) := by
  classical
  intro x
  obtain ⟨c, hc⟩ := Stacks.Cohomology.Torsors.torsorIsoClassesToH1_surjective G x
  obtain ⟨F, rfl⟩ := Quotient.exists_rep c
  rw [← hc]
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  obtain ⟨p, a, hp, hbase⟩ :=
    exists_finite_separable_torsor_point k B hk G hG hSmooth F
  let : Algebra k p.carrier := a
  have : Module.Finite k p.carrier := hp.1
  have : Algebra.IsSeparable k p.carrier := hp.2
  have hpFinite : _root_.AlgebraicGeometry.IsFinite p.toBase := by
    rw [hbase]
    exact (_root_.AlgebraicGeometry.IsFinite.SpecMap_iff _).2
      (RingHom.finite_algebraMap.mpr inferInstance)
  have hpEtale : Etale p.toBase := by
    rw [hbase]
    have : Algebra.FormallyEtale k p.carrier := Algebra.FormallyEtale.of_isSeparable k p.carrier
    have : Algebra.FinitePresentation k p.carrier :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    have : Algebra.Etale k p.carrier := ⟨inferInstance, inferInstance⟩
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).2
      (RingHom.etale_algebraMap.mpr inferInstance)
  obtain ⟨N, n, U, hcover, hdisj, hiso⟩ :=
    exists_etale_disjoint_open_decomposition p.toBase
      (Classical.arbitrary (Spec (.of k)))
  let _ (i : Fin n) : IsIso ((U i).ι ≫ pullback.snd p.toBase N.toBase) := hiso i
  have hpSurj : Surjective p.toBase :=
    ⟨fun x => ⟨Classical.arbitrary (Spec (.of p.carrier)), Subsingleton.elim _ _⟩⟩
  have hn : 0 < n := by
    obtain ⟨z, _⟩ := (pullback.snd p.toBase N.toBase).surjective N.point
    have hz : z ∈ sSup (Set.range U) := by rw [hcover]; trivial
    obtain ⟨_, ⟨i, rfl⟩, _⟩ := TopologicalSpace.Opens.mem_sSup.mp hz
    exact lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  obtain ⟨O, hO, hmem, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := N.scheme) (x := N.point) (U := ⊤) (by trivial)
  have : IsAffine O.toScheme := hO
  let g := O.ι ≫ N.toBase
  have : Etale g := inferInstance
  have hsize : B.Contains O.toScheme :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact g hk
  let V : AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk :=
    Over.mk (ObjectProperty.homMk g : B.obj hsize ⟶ B.obj hk)
  let L := p.siteObject
  let : ∀ i, IsIso ((U i).ι ≫ pullback.snd (B.inclusion.map L.hom) N.toBase) := hiso
  let T : AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk := Over.mk (𝟙 (B.obj hk))
  let q : V ⟶ T := Over.mkIdTerminal.from V
  have : Flat (B.inclusion.map V.hom) := (inferInstance : Flat g)
  have : LocallyOfFinitePresentation (B.inclusion.map V.hom) :=
    (inferInstance : LocallyOfFinitePresentation g)
  have : Surjective (B.inclusion.map V.hom) :=
    ⟨fun x => ⟨⟨N.point, hmem⟩, @Subsingleton.elim (Spec (.of k)) inferInstance _ _⟩⟩
  let R : (AlgebraicGeometry.BigFppfOver.topology B (Spec (.of k)) hk).Cover T :=
    ⟨(PreZeroHypercover.singleton.{u + 1} q).sieve₀,
      singleton_cover_of_fppf B (Spec (.of k)) hk V⟩
  have hl (I : R.Arrow) : ∃ l : I.Y ⟶ V, l ≫ q = I.f := by
    have hI : Sieve.ofArrows (fun _ : PUnit.{u + 2} => V) (fun _ => q) I.f := I.hf
    obtain ⟨i, l, hl⟩ := Sieve.ofArrows.exists hI
    exact ⟨l, hl.symm⟩
  choose l hl using hl
  let t (i : Fin n) : V ⟶ L := Over.homMk
    (ObjectProperty.homMk (O.ι ≫ splitSection (pullback.snd p.toBase N.toBase) (U i) ≫
      pullback.fst p.toBase N.toBase)) (by
        apply B.inclusion.map_injective
        change (O.ι ≫ splitSection (pullback.snd p.toBase N.toBase) (U i) ≫
          pullback.fst p.toBase N.toBase) ≫ p.toBase = O.ι ≫ N.toBase
        rw [Category.assoc, Category.assoc, pullback.condition,
          ← Category.assoc (splitSection _ _) (pullback.snd _ _),
          splitSection_comp, Category.id_comp])
  refine ⟨n, hn, ?_⟩
  apply nsmul_torsorClass_eq_zero_of_local_permutations G F Over.mkIdTerminal R l n t p.value
  intro Z a b
  exact split_sections_locally_permuted_on_site B (Spec (.of k)) hk L V N.scheme N.toBase
    U hcover hdisj O.ι rfl t (fun _ => rfl) a b


end AlgebraicGeometry

end
