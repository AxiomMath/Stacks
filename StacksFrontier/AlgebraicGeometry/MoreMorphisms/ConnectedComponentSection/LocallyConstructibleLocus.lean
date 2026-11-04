module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.Limits.OverPullbackId
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Section
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Constructible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.BaseChange
public import StacksFrontier.Topology.Noetherian.ConstructibleDichotomy
public import StacksFrontier.Algebra.Category.Ring.FiniteSubalgebras

/-!
# Local constructibility of the connected component along a section

Let `f : X ⟶ Y` be a morphism of schemes with a specified section. If `f` is of finite
presentation, then the union `X⁰` in `X` of the connected components of the fibres containing
the section is locally constructible. This is Stacks Tag 055P, which is reduced here to the
statement that `X⁰` becomes open and closed after shrinking the closure of a point of the
target to a nonempty open subset — the content of Stacks Tag 055N, not yet available in the
library and therefore carried as a hypothesis.

## Main definitions

* `AlgebraicGeometry.ConnectedAlongSection.ClopenLocusAfterShrinking` is the conclusion of
  Stacks Tag 055N, phrased for all finite type sectioned morphisms at once.

## Main results

* `AlgebraicGeometry.ConnectedAlongSection.isLocallyConstructible_locus_of_clopenLocus`:
  Stacks Tag 055P, granted `ClopenLocusAfterShrinking`.

## Implementation notes

Following Mathlib's conventions, finite presentation of a scheme morphism is expressed by local
finite presentation, quasi-compactness and quasi-separatedness; the subset `X⁰` is
`AlgebraicGeometry.ConnectedAlongSection.locus`.

The argument is in three steps. Over an affine base `Spec R`, the sectioned morphism is
descended to a Noetherian base: `Spec R` is the limit of the spectra of the finitely generated
`ℤ`-subalgebras of `R`, indexed by the finite subsets of `R`, each of which is a Noetherian
ring; the scheme is descended by Stacks Tag 01ZM part (1) and its section by part (2), applied
to the structure morphism of the base regarded as the identity in the over category. Over a
Noetherian source the hypothesis from Tag 055N gives one half or the other of the dichotomy of
Stacks Tag 053Z on every irreducible closed subset, because a clopen subset of a
preirreducible space is either everything or nothing; hence `X⁰` is constructible there. The
two steps are joined by the base change formula of Stacks Tag 055M and the stability of local
constructibility under inverse images, Stacks Tag 054I. The general case follows by covering
the target with affine opens.

## References

* [Stacks Project, Tag 055P](https://stacks.math.columbia.edu/tag/055P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace ConnectedAlongSection

noncomputable section

/-! ### Descending a sectioned morphism to a Noetherian base -/

/-- A sectioned morphism of finite presentation over `Spec R` is the base change of a sectioned
morphism of finite presentation over a Noetherian scheme, and the section downstairs induces
the given one. -/
private theorem exists_noetherian_section_model {X : Scheme.{u}}
    (R : CommRingCat.{u}) (f : X ⟶ Spec R) (s : Spec R ⟶ X)
    (hsec : s ≫ f = 𝟙 _) (hf : FinitePresentation f) :
    ∃ (Y₀ X₀ : Scheme.{u}) (g : Spec R ⟶ Y₀) (f₀ : X₀ ⟶ Y₀) (s₀ : Y₀ ⟶ X₀),
      IsNoetherian Y₀ ∧ FinitePresentation f₀ ∧
      ∃ (hsec₀ : s₀ ≫ f₀ = 𝟙 Y₀),
      ∃ (e : Over.mk f ≅ (Over.pullback g).obj (Over.mk f₀)),
        s ≫ e.hom.left = (overPullbackIdIso g).inv.left ≫
          ((Over.pullback g).map (Over.homMk s₀ hsec₀)).left := by
  let D := R.finiteSubalgebras.op ⋙ Scheme.Spec
  let cBase := Scheme.Spec.mapCone R.finiteSubalgebrasCocone.op
  let c : Cone D := { pt := Spec R, π := cBase.π }
  have hc : IsLimit c := by
    show IsLimit cBase
    exact isLimitOfPreserves _ R.finiteSubalgebrasIsColimit.op
  have : ∀ i, IsAffine (D.obj i) := fun i => inferInstanceAs (IsAffine (Spec _))
  obtain ⟨i, Xi, hXi, eX⟩ :=
    LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall D c hc (Over.mk f) hf
  let s' : c.pt ⟶ X := s
  let f' : X ⟶ c.pt := f
  have hsec' : s' ≫ f' = 𝟙 c.pt := hsec
  let πi := c.π.app i
  let Bi : Over (D.obj i) := Over.mk (𝟙 (D.obj i))
  have hBi : FinitePresentation Bi.hom := by
    show FinitePresentation (𝟙 (D.obj i))
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  let BLim := (Over.pullback πi).obj Bi
  let uIso : BLim ≅ Over.mk (𝟙 c.pt) := overPullbackIdIso πi
  let XLim := (Over.pullback πi).obj Xi
  have hXcomm : eX.some.hom.left ≫ XLim.hom = f' := by
    show eX.some.hom.left ≫ pullback.snd Xi.hom πi = f
    exact Over.w eX.some.hom
  have hsLim : (s' ≫ eX.some.hom.left) ≫ XLim.hom = 𝟙 c.pt := by
    rw [Category.assoc, hXcomm, hsec']
  let sLim : Over.mk (𝟙 c.pt) ⟶ XLim := Over.homMk (s' ≫ eX.some.hom.left) hsLim
  let fLim := uIso.hom ≫ sLim
  obtain ⟨j, eij, gj, α, β, hα, hβ, hgj⟩ :=
    exists_morphism_after_baseChange D c hc i Bi Xi hBi hXi fLim
  let πj := c.π.app j
  let Xj := (Over.pullback (D.map eij)).obj Xi
  let Bj := (Over.pullback (D.map eij)).obj Bi
  let uIsoj : Bj ≅ Over.mk (𝟙 (D.obj j)) := overPullbackIdIso (D.map eij)
  let sj := uIsoj.inv ≫ gj
  let e : Over.mk f ≅ (Over.pullback πj).obj Xj := eX.some ≪≫ β.symm
  have hXj : FinitePresentation Xj.hom := by
    have : LocallyOfFinitePresentation Xi.hom := hXi.1
    have : QuasiCompact Xi.hom := hXi.2.1
    have : QuasiSeparated Xi.hom := hXi.2.2
    show FinitePresentation (pullback.snd Xi.hom (D.map eij))
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  refine ⟨D.obj j, Xj.left, πj, Xj.hom, sj.left, ?_, hXj, ⟨Over.w sj, e, ?_⟩⟩
  · have : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (j.unop : Set R)) :=
      (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _)
    have : IsNoetherianRing (Algebra.adjoin ℤ (j.unop : Set R)) :=
      Algebra.FiniteType.isNoetherianRing ℤ (Algebra.adjoin ℤ (j.unop : Set R))
    show IsNoetherian (Spec (CommRingCat.of (Algebra.adjoin ℤ (j.unop : Set R))))
    exact AlgebraicGeometry.IsNoetherian.mk
  · have h1 : α.hom ≫ fLim ≫ β.inv = (Over.pullback πj).map gj := by
      calc
        α.hom ≫ fLim ≫ β.inv = (α.hom ≫ fLim) ≫ β.inv := by simp [Category.assoc]
        _ = ((Over.pullback πj).map gj ≫ β.hom) ≫ β.inv := by rw [hgj]
        _ = (Over.pullback πj).map gj := by simp [Category.assoc]
    have h2 : fLim ≫ β.inv = α.inv ≫ (Over.pullback πj).map gj := by
      calc
        fLim ≫ β.inv = α.inv ≫ (α.hom ≫ fLim ≫ β.inv) := by simp
        _ = α.inv ≫ (Over.pullback πj).map gj := by rw [h1]
    have h3 : sLim ≫ β.inv = uIso.inv ≫ α.inv ≫ (Over.pullback πj).map gj := by
      have h := congrArg (fun k => uIso.inv ≫ k) h2
      simpa [fLim, sLim, Category.assoc] using h
    let sourceJLim := (Over.pullback πj).obj Bj
    let : IsIso Bj.hom := by
      show IsIso (pullback.snd (𝟙 (D.obj i)) (D.map eij))
      infer_instance
    let : IsIso sourceJLim.hom := by
      show IsIso (pullback.snd Bj.hom πj)
      infer_instance
    have hsource : (uIso.inv ≫ α.inv).left =
        ((overPullbackIdIso πj).inv ≫ (Over.pullback πj).map uIsoj.inv).left := by
      apply (cancel_mono sourceJLim.hom).mp
      calc
        (uIso.inv ≫ α.inv).left ≫ sourceJLim.hom = 𝟙 c.pt := Over.w (uIso.inv ≫ α.inv)
        _ = ((overPullbackIdIso πj).inv ≫ (Over.pullback πj).map uIsoj.inv).left ≫
            sourceJLim.hom := (Over.w ((overPullbackIdIso πj).inv ≫
              (Over.pullback πj).map uIsoj.inv)).symm
    have h3left : sLim.left ≫ β.inv.left =
        (uIso.inv ≫ α.inv).left ≫ ((Over.pullback πj).map gj).left := by
      simpa only [Over.comp_left, Category.assoc] using congrArg Over.Hom.left h3
    have heleft : e.hom.left = eX.some.hom.left ≫ β.inv.left := rfl
    calc
      s ≫ e.hom.left = (uIso.inv ≫ α.inv).left ≫ ((Over.pullback πj).map gj).left := by
        rw [heleft, ← h3left]
        simp [sLim, Category.assoc]
        rfl
      _ = (overPullbackIdIso πj).inv.left ≫ ((Over.pullback πj).map sj).left := by
        rw [hsource]
        have hmap : (Over.pullback πj).map uIsoj.inv ≫
            (Over.pullback πj).map gj = (Over.pullback πj).map sj := by
          simp [sj]
        simpa only [Over.comp_left, Category.assoc] using
          congrArg (fun k => (overPullbackIdIso πj).inv.left ≫ k.left) hmap

/-! ### A computation with the base change of a section -/

/-- The base change of a section, followed by the first projection, is the first projection
followed by the section. -/
private theorem pullback_map_homMk_left_comp_fst {Y₀ X₀ S : Scheme.{u}} (f₀ : X₀ ⟶ Y₀)
    (s₀ : Y₀ ⟶ X₀) (hsec₀ : s₀ ≫ f₀ = 𝟙 Y₀) (g : S ⟶ Y₀) :
    ((Over.pullback g).map (Over.homMk s₀ hsec₀ : Over.mk (𝟙 Y₀) ⟶ Over.mk f₀)).left ≫
        pullback.fst f₀ g = pullback.fst (𝟙 Y₀) g ≫ s₀ := by
  show pullback.lift (pullback.fst (𝟙 Y₀) g ≫ s₀) (pullback.snd (𝟙 Y₀) g) _ ≫
    pullback.fst f₀ g = pullback.fst (𝟙 Y₀) g ≫ s₀
  exact pullback.lift_fst _ _ _

/-! ### The input supplied by Stacks Tag 055N -/

/-- The conclusion of **Stacks Project, Tag 055N**: for every finite type sectioned morphism and
every point `y` of the target there is a nonempty open subset of the closure of `y` over which
the locus `X⁰` is open and closed in the inverse image.

This is the one input of Tag 055P which is not yet available in the library, so the results
below take it as a hypothesis. -/
def ClopenLocusAfterShrinking : Prop :=
  ∀ D : ConnectedAlongSection.{u}, LocallyOfFiniteType D.f → QuasiCompact D.f → ∀ y : D.Y,
    ∃ V : TopologicalSpace.Opens (↑(closure ({y} : Set D.Y))), Nonempty V ∧
      IsClopen {x : {x : D.X // D.f x ∈ Set.range (fun z : V ↦ (z.1.1 : D.Y))} |
        (x.1 : D.X) ∈ D.locus}

/-! ### Constructibility over a Noetherian base -/

/-- The intersection of a preirreducible set with an open set is preirreducible. -/
private theorem isPreirreducible_inter_isOpen {α : Type*} [TopologicalSpace α] {Z O : Set α}
    (hZ : IsPreirreducible Z) (hO : IsOpen O) : IsPreirreducible (Z ∩ O) := by
  rintro A B hA hB ⟨a, haW, haA⟩ ⟨b, hbW, hbB⟩
  obtain ⟨c, hcZ, hcOA, hcOB⟩ := hZ (O ∩ A) (O ∩ B) (hO.inter hA) (hO.inter hB)
    ⟨a, haW.1, haW.2, haA⟩ ⟨b, hbW.1, hbW.2, hbB⟩
  exact ⟨c, ⟨hcZ, hcOA.1⟩, hcOA.2, hcOB.2⟩

/-- Granted the conclusion of Tag 055N, the locus `X⁰` satisfies the dichotomy of Tag 053Z on
every irreducible closed subset of the source: shrinking the closure of the image of the
generic point makes `X⁰` clopen there, and a clopen set is either everything or nothing. -/
private theorem containsNonemptyOpenOf_or_not_isDenseIn_locus
    (H : ClopenLocusAfterShrinking.{u}) (D : ConnectedAlongSection.{u})
    [LocallyOfFiniteType D.f] [QuasiCompact D.f] (Z : Set D.X) (hZ : IsIrreducible Z)
    (hZclosed : IsClosed Z) : ContainsNonemptyOpenOf D.locus Z ∨ ¬ IsDenseIn D.locus Z := by
  let x : D.X := hZ.genericPoint
  have hxZ : x ∈ Z := by
    rw [← hZ.closure_genericPoint hZclosed]
    exact subset_closure (Set.mem_singleton x)
  let y : D.Y := D.f x
  obtain ⟨V, hV, hVcl⟩ := H D inferInstance inferInstance y
  obtain ⟨U, hU, he⟩ := isOpen_induced_iff.mp V.isOpen
  obtain ⟨z, hzV⟩ := hV
  have hzU : z.1 ∈ U := by
    have hz : z ∈ (V : Set (closure ({y} : Set D.Y))) := hzV
    rw [← he] at hz
    exact hz
  have hyU : y ∈ U := by
    obtain ⟨a, haU, haY⟩ := (mem_closure_iff.mp z.2) U hU hzU
    exact Set.mem_singleton_iff.mp haY ▸ haU
  let O : Set D.X := D.f ⁻¹' U
  have hO : IsOpen O := hU.preimage D.f.continuous
  have hWne : (Z ∩ O).Nonempty := ⟨x, hxZ, hyU⟩
  have himage : ∀ w ∈ Z, D.f w ∈ closure ({y} : Set D.Y) := by
    intro w hw
    have hwcl : w ∈ closure ({x} : Set D.X) := by rwa [hZ.closure_genericPoint hZclosed]
    simpa [y] using image_closure_subset_closure_image (f := (D.f : D.X → D.Y)) D.f.continuous
      (Set.mem_image_of_mem _ hwcl)
  let W' := {w : D.X // w ∈ Z ∩ O}
  let j : W' → {w : D.X // D.f w ∈ Set.range (fun z : V ↦ (z.1.1 : D.Y))} := fun w => ⟨w.1, by
    have hw : w.1 ∈ Z ∩ O := w.2
    have hqV : (⟨D.f w.1, himage w.1 hw.1⟩ :
        {a : D.Y // a ∈ closure ({y} : Set D.Y)}) ∈ V := by
      show (⟨D.f w.1, himage w.1 hw.1⟩ : {a : D.Y // a ∈ closure ({y} : Set D.Y)}) ∈
        (V : Set (closure ({y} : Set D.Y)))
      rw [← he]
      simpa [O] using hw.2
    exact ⟨⟨_, hqV⟩, rfl⟩⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk fun w => (j w).2
  have hWclopen : IsClopen {w : W' | (w.1 : D.X) ∈ D.locus} := hVcl.preimage hj
  have : PreirreducibleSpace W' := Subtype.preirreducibleSpace
    (isPreirreducible_inter_isOpen hZ.2 hO)
  rcases isClopen_iff.mp hWclopen with hE | hE
  · right
    intro hdense
    obtain ⟨a, haO, haEZ⟩ := (mem_closure_iff.mp (hdense hxZ)) O hO hyU
    have hmem : (⟨a, ⟨haEZ.2, haO⟩⟩ : W') ∈ {w : W' | (w.1 : D.X) ∈ D.locus} := haEZ.1
    simp [hE] at hmem
  · left
    refine ⟨O, hO, by simpa [Set.inter_comm] using hWne, ?_⟩
    intro a ha
    have hmem : (⟨a, ⟨ha.2, ha.1⟩⟩ : W') ∈ {w : W' | (w.1 : D.X) ∈ D.locus} := by simp [hE]
    exact ⟨hmem, ha.2⟩

/-- Granted the conclusion of Tag 055N, the locus `X⁰` is constructible whenever the source is
a Noetherian space. -/
private theorem isConstructible_locus_of_noetherianSpace
    (H : ClopenLocusAfterShrinking.{u}) (D : ConnectedAlongSection.{u})
    [TopologicalSpace.NoetherianSpace D.X] [LocallyOfFiniteType D.f] [QuasiCompact D.f] :
    Topology.IsConstructible D.locus := by
  obtain ⟨n, U, V, hU, hUr, hV, hVr, e⟩ :=
    (constructible_iff_dichotomy_irreducible_closed D.locus).2
      (containsNonemptyOpenOf_or_not_isDenseIn_locus H D)
  rw [e]
  exact Topology.IsConstructible.iUnion fun i => ((hUr i).isConstructible (hU i)).inter
    (((hVr i).isConstructible (hV i)).compl)

/-! ### The case of an affine base -/

/-- Granted the conclusion of Tag 055N, the locus `X⁰` is locally constructible for a sectioned
morphism of finite presentation over an affine base. -/
private theorem isLocallyConstructible_locus_over_spec
    (H : ClopenLocusAfterShrinking.{u}) (X : Scheme.{u}) (R : CommRingCat.{u})
    (f : X ⟶ Spec R) (s : Spec R ⟶ X) (hsec : s ≫ f = 𝟙 (Spec R))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    Topology.IsLocallyConstructible (ConnectedAlongSection.locus ⟨X, Spec R, f, s, hsec⟩) := by
  let D : ConnectedAlongSection := ⟨X, Spec R, f, s, hsec⟩
  have hf : FinitePresentation D.f := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨Y₀, X₀, g, f₀, s₀, hY₀, hf₀, ⟨hsec₀, e, hcompat⟩⟩ :=
    exists_noetherian_section_model R D.f D.s D.section_fac hf
  let D₀ : ConnectedAlongSection := ⟨X₀, Y₀, f₀, s₀, hsec₀⟩
  let : IsNoetherian Y₀ := hY₀
  let : LocallyOfFinitePresentation f₀ := hf₀.1
  let : QuasiCompact f₀ := hf₀.2.1
  let : QuasiSeparated f₀ := hf₀.2.2
  let : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  let : LocallyOfFiniteType f₀ := inferInstance
  let : IsLocallyNoetherian X₀ := LocallyOfFiniteType.isLocallyNoetherian f₀
  let : IsNoetherian X₀ := AlgebraicGeometry.IsNoetherian.mk
  have hD₀ : Topology.IsConstructible D₀.locus := isConstructible_locus_of_noetherianSpace H D₀
  let P₀ := (Over.pullback g).obj (Over.mk f₀)
  let p₀fst : P₀.left ⟶ X₀ := pullback.fst f₀ g
  let g' : D.X ⟶ X₀ := e.hom.left ≫ p₀fst
  let eX : D.X ≅ P₀.left := (Over.forget (Spec R)).mapIso e
  have hP : IsPullback p₀fst P₀.hom f₀ g := IsPullback.of_hasPullback f₀ g
  have hpb : IsPullback g' D.f f₀ g := by
    refine hP.of_iso eX.symm (Iso.refl X₀) (Iso.refl (Spec R)) (Iso.refl Y₀) ?_ ?_ ?_ ?_
    · show p₀fst = eX.inv ≫ eX.hom ≫ p₀fst
      simp
    · have hw : eX.hom ≫ P₀.hom = D.f := Over.w e.hom
      calc
        P₀.hom = (eX.inv ≫ eX.hom) ≫ P₀.hom := by simp
        _ = eX.inv ≫ D.f := by rw [Category.assoc, hw]
    · simp
    · simp
  have hs : D.s ≫ g' = g ≫ D₀.s := by
    show (D.s ≫ e.hom.left) ≫ p₀fst = g ≫ s₀
    rw [hcompat, Category.assoc,
      pullback_map_homMk_left_comp_fst f₀ s₀ hsec₀ g, ← Category.assoc,
      overPullbackIdIso_inv_left_comp_fst g]
  rw [ConnectedAlongSection.locus_eq_preimage_of_isPullback D₀ D g' g hpb hs]
  exact isLocallyConstructible_preimage g' hD₀.isLocallyConstructible

/-! ### The general case -/

/-- **Stacks Project, Tag 055P**, granted the conclusion of Tag 055N. For a morphism of finite
presentation with a specified section, the union of the connected components of the fibres
containing the section is locally constructible in the source. -/
theorem isLocallyConstructible_locus_of_clopenLocus
    (H : ClopenLocusAfterShrinking.{u}) (D : ConnectedAlongSection.{u})
    [LocallyOfFinitePresentation D.f] [QuasiCompact D.f] [QuasiSeparated D.f] :
    Topology.IsLocallyConstructible D.locus := by
  let 𝒰 := D.Y.affineCover
  let 𝒱 : D.X.OpenCover := 𝒰.pullback₁ D.f
  have hCover : TopologicalSpace.IsOpenCover (fun i => (𝒱.f i).opensRange) :=
    TopologicalSpace.IsOpenCover.mk <| TopologicalSpace.Opens.ext <| by
      rw [TopologicalSpace.Opens.coe_iSup]
      exact Scheme.Cover.iUnion_range 𝒱
  refine Topology.IsLocallyConstructible.of_isOpenCover hCover fun i => ?_
  let Rᵢ : CommRingCat := Classical.choose (Classical.choose_spec (D.Y.local_affine i))
  let g : Spec Rᵢ ⟶ D.Y := 𝒰.f i
  let g' : 𝒱.X i ⟶ D.X := 𝒱.f i
  let fᵢ : 𝒱.X i ⟶ Spec Rᵢ := 𝒰.pullbackHom D.f i
  let sᵢ : Spec Rᵢ ⟶ 𝒱.X i :=
    pullback.lift (g ≫ D.s) (𝟙 (Spec Rᵢ))
      (by rw [Category.assoc, D.section_fac, Category.comp_id]; exact (Category.id_comp _).symm)
  have hsecᵢ : sᵢ ≫ fᵢ = 𝟙 (Spec Rᵢ) := pullback.lift_snd _ _ _
  have : MorphismProperty.IsStableUnderBaseChangeAlong (@LocallyOfFinitePresentation) g :=
    ⟨fun h hp => MorphismProperty.IsStableUnderBaseChange.of_isPullback h hp⟩
  have : MorphismProperty.IsStableUnderBaseChangeAlong (@QuasiCompact) g :=
    ⟨fun h hp => MorphismProperty.IsStableUnderBaseChange.of_isPullback h hp⟩
  have : MorphismProperty.IsStableUnderBaseChangeAlong (@QuasiSeparated) g :=
    ⟨fun h hp => MorphismProperty.IsStableUnderBaseChange.of_isPullback h hp⟩
  have : LocallyOfFinitePresentation fᵢ := MorphismProperty.pullback_snd D.f g inferInstance
  have : QuasiCompact fᵢ := MorphismProperty.pullback_snd D.f g inferInstance
  have : QuasiSeparated fᵢ := MorphismProperty.pullback_snd D.f g inferInstance
  let Dᵢ : ConnectedAlongSection := ⟨𝒱.X i, Spec Rᵢ, fᵢ, sᵢ, hsecᵢ⟩
  have hLocᵢ : Topology.IsLocallyConstructible Dᵢ.locus :=
    isLocallyConstructible_locus_over_spec H (𝒱.X i) Rᵢ fᵢ sᵢ hsecᵢ
  have hPB : IsPullback g' fᵢ D.f g := IsPullback.of_hasPullback D.f g
  have hSecPB : sᵢ ≫ g' = g ≫ D.s := pullback.lift_fst _ _ _
  let eᵣ := Scheme.homeoOfIso g'.isoOpensRange
  have hLocRange := hLocᵢ.preimage_of_isOpenEmbedding eᵣ.symm.isOpenEmbedding
  have hSet : eᵣ.symm ⁻¹' Dᵢ.locus = {z : ↥(g'.opensRange) | (z.1 : D.X) ∈ D.locus} := by
    ext z
    show (eᵣ.symm z ∈ Dᵢ.locus) ↔ z.1 ∈ D.locus
    rw [ConnectedAlongSection.locus_eq_preimage_of_isPullback D Dᵢ g' g hPB hSecPB]
    show D.locus (g' (eᵣ.symm z)) ↔ z.1 ∈ D.locus
    have hv : g' (eᵣ.symm z) = z.1 := by
      calc
        g' (eᵣ.symm z) = (g'.isoOpensRange.inv ≫ g') z := by
          rw [show eᵣ.symm z = g'.isoOpensRange.inv z by simp [eᵣ, Scheme.homeoOfIso_symm],
            Scheme.Hom.comp_apply]
        _ = g'.opensRange.ι z := congrArg (fun k => k z) (Scheme.Hom.isoOpensRange_inv_comp g')
        _ = z.1 := rfl
    rw [hv]
    rfl
  rwa [hSet] at hLocRange

end

end ConnectedAlongSection

end AlgebraicGeometry
