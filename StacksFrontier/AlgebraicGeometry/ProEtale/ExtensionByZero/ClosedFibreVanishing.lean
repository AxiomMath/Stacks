module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.Abelian
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.Localization
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Slices
public import StacksFrontier.RingTheory.WeaklyEtale.Descent
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.Localization.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of extension by zero near a closed subscheme

Let a weakly étale morphism be disjoint from a closed subscheme. On an affine pro-étale object
whose points all specialize to the closed fibre, extension by zero of any abelian sheaf has zero
sections.

## Main results

* `AlgebraicGeometry.ProEtale.isZero_extensionByZero_sections_of_specializes_to_closed` gives
  the vanishing of sections on such an affine pro-étale object.

## Implementation notes

Disjointness is expressed by emptiness of the scheme-theoretic fibre product. The specialization
hypothesis uses points of this same fibre product. The conclusion is categorical vanishing of the
abelian group of sections.

The proof refines an arbitrary pro-étale covering of the affine object by a finite affine family
of localizations at the ideal cutting out the closed fibre, over which no arrow to the weakly
étale source exists; the left Kan extension computing extension by zero therefore vanishes on
each member of the refinement, and separatedness of the sheafification propagates the vanishing
to the object itself.

## References

* [Stacks Project, Tag 09AG](https://stacks.math.columbia.edu/tag/09AG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

universe u v u₁ u₂ v₁ v₂

namespace AlgebraicGeometry.ProEtale

private lemma exists_finite_affine_refinement_of_ProEt_presieve
    {X : Scheme.{u}} {V : X.ProEt} [IsAffine V.left] (R : Presieve V)
    (hR : R ∈ Scheme.ProEt.precoverage X V) :
    ∃ (U : Scheme.Cover.{u + 1} (Scheme.precoverage @WeaklyEtale) V.left),
      U.presieve₀ = R.map (Scheme.ProEt.forget X ⋙ Over.forget X) ∧
        QuasiCompactCover U.toPreZeroHypercover ∧
        ∃ (A : Scheme.AffineCover @WeaklyEtale V.left) (q : A.cover ⟶ U),
          Finite A.I₀ ∧ ∀ i, IsOpenImmersion (q.h₀ i) := by
  have hscheme :
      (R.map (Scheme.ProEt.forget X ⋙ Over.forget X)) ∈
        Scheme.proetalePrecoverage V.left := by
    change _ ∈ Scheme.proetalePrecoverage V.left at hR
    exact hR
  have hqc :
      (R.map (Scheme.ProEt.forget X ⋙ Over.forget X)) ∈
        Scheme.propQCPrecoverage @WeaklyEtale V.left := by
    simpa [Scheme.proetalePrecoverage] using hscheme
  obtain ⟨U, hcover, hUeq⟩ :=
    (Scheme.mem_propQCPrecoverage_iff_exists_quasiCompactCover).mp hqc
  let : MorphismProperty.RespectsLeft @WeaklyEtale @IsOpenImmersion := by
    constructor
    intro A C D i hi f hf
    let : WeaklyEtale i := by infer_instance
    exact inferInstance
  let : CompactSpace V.left := inferInstance
  let : QuasiCompactCover U.toPreZeroHypercover := hcover
  obtain ⟨A, q, hfin, hopen⟩ := QuasiCompactCover.exists_hom U
  exact ⟨U, hUeq.symm, hcover, A, q, hfin, hopen⟩

private lemma localizedPoint_has_specialization
    {A : Type u} [CommRing A] (I : Ideal A)
    (p : PrimeSpectrum (localizationRing I 1)) :
    ∃ q : PrimeSpectrum (localizationRing I 1),
      p ⤳ q ∧ I ≤ (PrimeSpectrum.comap (algebraMap A
        (localizationRing I 1)) q).asIdeal := by
  let B := Localization (localizationSubmonoid I 1)
  let f : PrimeSpectrum B → PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B)
  have hp : f p ∈ Set.range f := ⟨p, rfl⟩
  rw [localization_comap_range] at hp
  obtain ⟨q, hq, hpq⟩ := hp
  have hq' : q ∈ Set.range f := by
    change q ∈ Set.range (PrimeSpectrum.comap (algebraMap A B))
    rw [localization_comap_range]
    exact ⟨q, hq, specializes_rfl⟩
  obtain ⟨q', hq'⟩ := hq'
  refine ⟨q', ?_, ?_⟩
  · apply (PrimeSpectrum.localization_comap_isEmbedding B
      (localizationSubmonoid I 1)).isInducing.specializes_iff.mp
    simpa [f, hq'] using hpq
  · have heq : PrimeSpectrum.comap (algebraMap A B) q' = q := hq'
    change I ≤ (PrimeSpectrum.comap (algebraMap A B) q').asIdeal
    rw [heq]
    exact hq.1

/-- A ring map that is weakly étale as an algebra map has weakly étale spectrum map. -/
private lemma weaklyEtale_specMap_of_algebra {R S : CommRingCat.{u}} (f : R ⟶ S)
    (h : @Algebra.WeaklyEtale R S _ _ f.hom.toAlgebra) :
    WeaklyEtale (Spec.map f) := by
  let : Algebra R S := f.hom.toAlgebra
  refine ⟨(Flat.SpecMap_iff).mpr h.flat, ?_⟩
  rw [show f = CommRingCat.ofHom (algebraMap R S) from rfl, diagonal_SpecMap]
  exact MorphismProperty.comp_mem @Flat _ _
    ((Flat.SpecMap_iff).mpr h.flat_lmul') inferInstance

private lemma closed_fibre_point_of_kernel
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : Scheme.{u}) [IsAffine T] (g : T ⟶ X)
    (q : PrimeSpectrum Γ(T, ⊤))
    (hq : RingHom.ker (pullback.fst g i).appTop.hom ≤ q.asIdeal) :
    ∃ z : (pullback g i : Scheme.{u}),
      (pullback.fst g i).base z = T.isoSpec.inv.base q := by
  let f := pullback.fst g i
  let I : Ideal Γ(T, ⊤) := RingHom.ker f.appTop.hom
  have hzero : T.isoSpec.inv.base q ∈ T.zeroLocus (I : Set Γ(T, ⊤)) := by
    have hq : q ∈ PrimeSpectrum.zeroLocus I := (PrimeSpectrum.mem_zeroLocus q I).2 hq
    have hpre : q ∈ T.isoSpec.inv.base ⁻¹' T.zeroLocus (I : Set Γ(T, ⊤)) := by
      rw [T.isoSpec_inv_preimage_zeroLocus]
      exact hq
    exact hpre
  have hker : (T.isoSpec.inv.base q) ∈ f.ker.support := by
    rw [Scheme.ker_of_isAffine f]
    apply (Scheme.IdealSheafData.mem_support_iff_of_mem
      (I := Scheme.IdealSheafData.ofIdealTop I) (x := T.isoSpec.inv.base q)
      (U := ⟨⊤, isAffineOpen_top T⟩) (Set.mem_univ _)).2
    simpa using hzero
  have hrange : T.isoSpec.inv.base q ∈ Set.range f := by
    have hcl : T.isoSpec.inv.base q ∈ closure (Set.range f) := by
      rw [← Scheme.Hom.support_ker]
      exact hker
    rw [f.isClosedEmbedding.isClosed_range.closure_eq] at hcl
    exact hcl
  simpa [f] using hrange

private lemma localized_cover_point_specialization
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : Scheme.{u}) [IsAffine T] (g : T ⟶ X)
    (I : Ideal Γ(T, ⊤))
    (hI : I = RingHom.ker (pullback.fst g i).appTop.hom)
    (w : Spec (CommRingCat.of (localizationRing I 1))) :
    ∃ q : Spec (CommRingCat.of (localizationRing I 1)),
      Specializes w q ∧
      ∃ z : (pullback g i : Scheme.{u}),
        ((Spec.map (CommRingCat.ofHom
          (algebraMap Γ(T, ⊤) (localizationRing I 1))) ≫
          T.isoSpec.inv).base q) = (pullback.fst g i).base z := by
  let A := (Γ(T, ⊤)).carrier
  let M : Submonoid A := localizationSubmonoid I 1
  let B := Localization M
  let φ : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let p : PrimeSpectrum B := w
  obtain ⟨qB, hpq, hqI⟩ := localizedPoint_has_specialization I p
  let qA : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) qB
  have hqA : I ≤ qA.asIdeal := by simpa [qA] using hqI
  obtain ⟨z, hz⟩ := closed_fibre_point_of_kernel i T g qA (by simpa [hI] using hqA)
  have htop : (Spec (CommRingCat.of B)).instTopologicalSpaceCarrierCarrier =
      PrimeSpectrum.zariskiTopology := rfl
  have hpq' : @Specializes (Spec (CommRingCat.of B))
      (Spec (CommRingCat.of B)).instTopologicalSpaceCarrierCarrier w qB := by
    change @Specializes (PrimeSpectrum B)
      (Spec (CommRingCat.of B)).instTopologicalSpaceCarrierCarrier w qB
    have heq :
        (@Specializes (PrimeSpectrum B)
          (Spec (CommRingCat.of B)).instTopologicalSpaceCarrierCarrier w qB) =
        (@Specializes (PrimeSpectrum B) PrimeSpectrum.zariskiTopology w qB) :=
      congrArg (fun t : TopologicalSpace (PrimeSpectrum B) =>
        @Specializes (PrimeSpectrum B) t w qB) htop
    exact heq.mpr (by simpa [B, p] using hpq)
  have hpoint : (Spec.map φ ≫ T.isoSpec.inv).base qB = T.isoSpec.inv.base qA := by
    change T.isoSpec.inv.base ((Spec.map φ).base qB) = _
    rw [Spec.map_base]
    rfl
  refine ⟨qB, hpq', z, ?_⟩
  exact hpoint.trans hz.symm

private lemma kernel_le_of_point_in_closed_fibre
    {X Z T : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (g : T ⟶ X) [IsAffine T]
    (z : (pullback g i : Scheme.{u})) :
    RingHom.ker (pullback.fst g i).appTop.hom ≤
      (T.isoSpec.hom.base ((pullback.fst g i).base z)).asIdeal := by
  let f := pullback.fst g i
  let I : Ideal Γ(T, ⊤) := RingHom.ker f.appTop.hom
  let x := f.base z
  let p := T.isoSpec.hom.base x
  have hs : x ∈ f.ker.support := f.range_subset_ker_support ⟨z, rfl⟩
  rw [Scheme.ker_of_isAffine f] at hs
  have hz : x ∈ T.zeroLocus (I : Set Γ(T, ⊤)) := by
    change x ∈ (Scheme.IdealSheafData.ofIdealTop I).support at hs
    have hm := (Scheme.IdealSheafData.mem_support_iff
      (I := Scheme.IdealSheafData.ofIdealTop I) (x := x)).1 hs
    simpa using hm ⟨⊤, isAffineOpen_top T⟩
  have hp : p ∈ PrimeSpectrum.zeroLocus I := by
    have himage : T.isoSpec.hom.base x ∈
        T.isoSpec.hom.base '' T.zeroLocus (I : Set Γ(T, ⊤)) := ⟨x, hz, rfl⟩
    rw [T.isoSpec_image_zeroLocus] at himage
    exact himage
  change I ≤ p.asIdeal
  exact (PrimeSpectrum.mem_zeroLocus p I).mp hp

private lemma localized_affineCover
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {V : X.ProEt} [IsAffine V.left]
    (A : Scheme.AffineCover.{u + 1, u} @WeaklyEtale V.left) (hfinite : Finite A.I₀)
    (hV : ∀ x : V.left, ∃ z : (pullback V.hom i : Scheme.{u}),
      Specializes x ((pullback.fst V.hom i).base z)) :
    ∃ (B : Scheme.AffineCover.{u + 1, u} @WeaklyEtale V.left),
      Finite B.I₀ ∧
        (∀ k, ∃ a : A.I₀, ∃ l : Spec (B.X k) ⟶ Spec (A.X a),
          B.f k = l ≫ A.f a) ∧
        ∀ k (w : Spec (B.X k)),
        ∃ z : (pullback (B.f k ≫ V.hom) i : Scheme.{u}),
          Specializes w ((pullback.fst (B.f k ≫ V.hom) i).base z) := by
  classical
  let T (k : A.I₀) : Scheme := Spec (A.X k)
  let g (k : A.I₀) : T k ⟶ X := A.f k ≫ V.hom
  let I (k : A.I₀) : Ideal Γ(T k, ⊤) :=
    RingHom.ker (pullback.fst (g k) i).appTop.hom
  let M (k : A.I₀) : Submonoid (Γ(T k, ⊤)).carrier := localizationSubmonoid (I k) 1
  let B (k : A.I₀) := localizationRing (I k) 1
  let φ (k : A.I₀) : CommRingCat.of (Γ(T k, ⊤)).carrier ⟶
      CommRingCat.of (B k) := CommRingCat.ofHom (algebraMap _ _)
  let f (k : A.I₀) : Spec (CommRingCat.of (B k)) ⟶ V.left :=
    Spec.map (φ k) ≫ (T k).isoSpec.inv ≫ A.f k
  let localized : Scheme.AffineCover.{u + 1, u} @WeaklyEtale V.left := {
    I₀ := A.I₀
    X := fun k => CommRingCat.of (B k)
    f := f
    idx := fun x => A.idx ((pullback.fst V.hom i).base (Classical.choose (hV x)))
    covers := by
      intro x
      let z := Classical.choose (hV x)
      have hxz := Classical.choose_spec (hV x)
      let xZ := (pullback.fst V.hom i).base z
      let k := A.idx xZ
      change x ∈ Set.range (f k)
      obtain ⟨p, hp⟩ := A.covers xZ
      let : WeaklyEtale (A.f k) := A.map_prop k
      have : Flat (A.f k) := inferInstance
      let hgen : GeneralizingMap (A.f k).base := Flat.generalizingMap (A.f k)
      have hrel : x ⤳ (A.f k) p := by rw [hp]; exact hxz
      obtain ⟨p', hp', hmap⟩ := hgen hrel
      let gk := g k
      let y := (pullback.snd V.hom i).base z
      have hcompat : gk.base p = i.base y := by
        change V.hom.base ((A.f k).base p) = i.base y
        calc
          V.hom.base ((A.f k).base p) = V.hom.base xZ := congrArg V.hom.base hp
          _ = i.base y := by
            simpa [xZ, y] using congrArg (fun h : pullback V.hom i ⟶ X => h.base z)
              (pullback.condition)
      obtain ⟨zT, hfst, _⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := gk) (g := i) p y hcompat
      let S := T k
      let : IsAffine S := inferInstance
      let p₀ := S.isoSpec.hom.base p
      let p₁ := S.isoSpec.hom.base p'
      have hpI : I k ≤ p₀.asIdeal := by
        have hker := kernel_le_of_point_in_closed_fibre (i := i) (T := S) (g := gk) zT
        change I k ≤ (S.isoSpec.hom.base p).asIdeal
        simpa [I, gk, hfst] using hker
      have hspec : p₁ ⤳ p₀ := by
        simpa [p₁, p₀] using S.isoSpec.hom.base.hom.map_specializes hp'
      have hloc : p₁ ∈ Set.range (PrimeSpectrum.comap
          (algebraMap (Γ(S, ⊤)).carrier (B k))) := by
        rw [localization_comap_range]
        refine ⟨p₀, ⟨hpI, ?_⟩, hspec⟩
        intro hone
        exact p₀.isPrime.ne_top ((Ideal.eq_top_iff_one p₀.asIdeal).2 hone)
      obtain ⟨q, hq⟩ := hloc
      refine ⟨q, ?_⟩
      have hqmap : (Spec.map (φ k)).base q = p₁ := by
        change PrimeSpectrum.comap (algebraMap (Γ(S, ⊤)).carrier (B k)) q = _
        rw [hq]
      have hpoint : (Spec.map (φ k) ≫ S.isoSpec.inv).base q = p' := by
        change S.isoSpec.inv.base ((Spec.map (φ k)).base q) = p'
        rw [hqmap]
        exact Scheme.hom_inv_apply S.isoSpec p'
      change (A.f k).base ((Spec.map (φ k) ≫ S.isoSpec.inv).base q) = x
      rw [hpoint]
      exact hmap
    map_prop := by
      intro k
      let : WeaklyEtale (A.f k) := A.map_prop k
      let : Algebra (Γ(T k, ⊤)).carrier (B k) := (φ k).hom.toAlgebra
      let : IsLocalization (M k) (B k) := by
        rw [isLocalization_iff_isLocalizationMap]
        change (M k).IsLocalizationMap (φ k).hom
        exact (Localization.monoidOf (M k)).isLocalizationMap
      let : Algebra.WeaklyEtale (Γ(T k, ⊤)).carrier (B k) :=
        (@weaklyEtale_of_isLocalization_etale_filteredColimit.{u, u, u}
          (Γ(T k, ⊤)).carrier).1 (B k) (M k)
      have hSpecWeak : WeaklyEtale (Spec.map (φ k)) :=
        weaklyEtale_specMap_of_algebra (φ k) inferInstance
      let : WeaklyEtale (Spec.map (φ k)) := hSpecWeak
      have hcomp : WeaklyEtale (Spec.map (φ k) ≫ (T k).isoSpec.inv) := inferInstance
      let : WeaklyEtale (Spec.map (φ k) ≫ (T k).isoSpec.inv) := hcomp
      change WeaklyEtale ((Spec.map (φ k) ≫ (T k).isoSpec.inv) ≫ A.f k)
      exact inferInstance
  }
  refine ⟨localized, ?_, ?_, ?_⟩
  · exact hfinite
  · intro k
    exact ⟨k, Spec.map (φ k) ≫ (T k).isoSpec.inv, rfl⟩
  · intro k w
    let : IsAffine (T k) := inferInstance
    obtain ⟨q, hwq, zT, hzT⟩ := localized_cover_point_specialization
      (i := i) (T := T k) (g := g k) (I k) rfl w
    let y := (pullback.snd (g k) i).base zT
    have hcompat := congrArg (fun h : pullback (g k) i ⟶ X => h.base zT)
      (pullback.condition)
    change (g k).base ((pullback.fst (g k) i).base zT) = i.base y at hcompat
    have hxy : (f k ≫ V.hom).base q = i.base y := by
      have hbase : (f k ≫ V.hom).base q =
          (g k).base ((Spec.map (φ k) ≫ (T k).isoSpec.inv).base q) := by
        simp [f, g, Scheme.Hom.comp_base]
      rw [hbase, hzT]
      exact hcompat
    obtain ⟨zW, hfst, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f k ≫ V.hom) (g := i) q y hxy
    refine ⟨zW, ?_⟩
    change Specializes w ((pullback.fst (f k ≫ V.hom) i).base zW)
    rw [hfst]
    exact hwq

private lemma no_scheme_arrow_over_disjoint_fibre
    {U X Z : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hdisjoint : IsEmpty (pullback j i : Scheme.{u}))
    {T : U.ProEt} {W : X.ProEt} (g : W.left ⟶ T.left)
    (hg : g ≫ T.hom ≫ j = W.hom) (z : (pullback W.hom i : Scheme.{u})) : False := by
  let x := (pullback.fst W.hom i).base z
  let y := (pullback.snd W.hom i).base z
  have hcomp := congrArg (fun f : W.left ⟶ X => f.base x) hg
  have hxy : j.base (T.hom.base (g.base x)) = i.base y := by
    simpa [Scheme.Hom.comp_base, x, y] using hcomp.trans (by
        simpa [Scheme.Hom.comp_base, x, y] using
        congrArg (fun f : pullback W.hom i ⟶ X => f.base z)
          (pullback.condition))
  obtain ⟨w, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := j) (g := i) (T.hom.base (g.base x)) y hxy
  exact hdisjoint.false w

private lemma isEmpty_costructuredArrow_of_specializing_closed_fibre
    {U X Z : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hdisjoint : IsEmpty (pullback j i : Scheme.{u}))
    {W : X.ProEt} (hW : ∀ w : W.left, ∃ z : (pullback W.hom i : Scheme.{u}),
      Specializes w ((pullback.fst W.hom i).base z)) (hne : Nonempty W.left) :
    IsEmpty (CostructuredArrow (proetalePostcompose j).op (op W)) := by
  refine ⟨fun c => ?_⟩
  let T : U.ProEt := c.left.unop
  let gm : W ⟶ proetalePostcompose j |>.obj T := c.hom.unop
  let g : W.left ⟶ T.left := gm.left
  have hg : g ≫ T.hom ≫ j = W.hom := by
    have hw := gm.w
    change g ≫ ((proetalePostcompose j).obj T).hom = W.hom at hw
    simpa [proetalePostcompose, CategoryTheory.Over.map, MorphismProperty.Over.map,
      MorphismProperty.Comma.mapRight, CategoryTheory.Comma.mapRight,
      MorphismProperty.Comma.lift, MorphismProperty.Comma.forget] using hw
  obtain ⟨w⟩ := hne
  obtain ⟨z, _⟩ := hW w
  exact no_scheme_arrow_over_disjoint_fibre j i hdisjoint g hg z

private lemma isZero_leftKanExtension_obj_of_no_costructured_arrows
    {C : Type u₁} [Category.{v₁, u₁} C]
    {D : Type u₂} [Category.{v₂, u₂} D]
    (L : C ⥤ D) (F : C ⥤ AddCommGrpCat.{v})
    [Functor.HasLeftKanExtension L F] [Functor.HasPointwiseLeftKanExtension L F]
    (Y : D) (hY : IsEmpty (CostructuredArrow L Y)) :
    IsZero ((Functor.leftKanExtension L F).obj Y) := by
  let T := CostructuredArrow.proj L Y ⋙ F
  let : IsEmpty (CostructuredArrow L Y) := hY
  have hzero : IsZero (0 : AddCommGrpCat.{v}) := isZero_zero _
  let c0 : Cocone T := {
    pt := 0
    ι := {
      app := fun j => isEmptyElim (hY.false j)
      naturality := by
        intro j j' f
        exact isEmptyElim (hY.false j) } }
  have hc0 : IsColimit c0 := {
    desc := fun s => hzero.isInitial.to s.pt
    fac := by
      intro s j
      exact isEmptyElim (hY.false j)
    uniq := by
      intro s m hm
      exact hzero.isInitial.hom_ext m _ }
  have e : colimit T ≅ (0 : AddCommGrpCat.{v}) :=
    (colimit.isColimit T).coconePointUniqueUpToIso hc0
  have hc : IsZero (colimit T) := IsZero.of_iso hzero e
  exact IsZero.of_iso hc (Functor.leftKanExtensionObjIsoColimit L F Y)

private lemma isZero_sheafPullback_obj_of_refinably_no_costructured_arrows
    {C : Type u₁} [Category.{v₁, u₁} C]
    {D : Type u₂} [Category.{v₂, u₂} D]
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Functor.IsContinuous G J K]
    [HasWeakSheafify K AddCommGrpCat.{v}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [∀ (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}), Functor.HasLeftKanExtension G.op P]
    [∀ (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}), Functor.HasPointwiseLeftKanExtension G.op P]
    (F : Sheaf J AddCommGrpCat.{v}) {Y : D}
    (hRefine : ∀ (S : Sieve Y), S ∈ K Y →
      ∃ R : Presieve Y, Sieve.generate R ∈ K Y ∧ Sieve.generate R ≤ S ∧
        ∀ ⦃Z : D⦄ (f : Z ⟶ Y), R f →
          IsEmpty (CostructuredArrow G.op (op Z))) :
    IsZero (((Functor.sheafPullbackConstruction.sheafPullback G
      AddCommGrpCat.{v} J K).obj F).obj.obj (op Y)) := by
  let P := (Functor.lan G.op).obj F.obj
  let H := (presheafToSheaf K AddCommGrpCat.{v}).obj P
  let η : P ⟶ H.obj := (sheafificationAdjunction K AddCommGrpCat.{v}).unit.app P
  have : Presheaf.IsLocallySurjective K η := by
    change Presheaf.IsLocallySurjective K (CategoryTheory.toSheafify K P)
    exact CategoryTheory.GrothendieckTopology.instIsLocallySurjectiveToSheafify P
  have hsub : Subsingleton (ToType (H.obj.obj (op Y))) := by
    have hzero : ∀ x : ToType (H.obj.obj (op Y)), x = 0 := by
      intro x
      let S : Sieve Y := Presheaf.imageSieve η x
      have hS : S ∈ K Y := Presheaf.imageSieve_mem K η x
      obtain ⟨R, hR, hle, hNo⟩ := hRefine S hS
      have hsep := ((isSheaf_iff_isSheaf_of_type K
        (H.obj ⋙ forget AddCommGrpCat.{v})).1
          ((sheafCompose K (forget AddCommGrpCat.{v})).obj H).2).isSeparated
            (Sieve.generate R) hR
      apply hsep.ext
      intro Z f hf
      obtain ⟨Y', g, r, hr, hgr⟩ := hf
      have hrS : S r := (Sieve.generate_le_iff R S).mp hle Y' r hr
      obtain ⟨t, ht⟩ := hrS
      let : IsEmpty (CostructuredArrow G.op (op Y')) := hNo r hr
      have hz := isZero_leftKanExtension_obj_of_no_costructured_arrows
        G.op F.obj (op Y') (hNo r hr)
      let : Subsingleton (ToType (P.obj (op Y'))) :=
        AddCommGrpCat.isZero_iff_subsingleton.mp hz
      have ht0 : t = 0 := Subsingleton.elim _ _
      rw [ht0] at ht
      have hr0 : (H.obj.map r.op) x = 0 := by simpa using ht.symm
      have hf0 : (H.obj.map f.op) x = 0 := by
        have hmap := congrArg (H.obj.map g.op) hr0
        have hfcomp : f.op = r.op ≫ g.op := by rw [← hgr]; rfl
        rw [hfcomp, Functor.map_comp]
        simpa using hmap
      simpa using hf0
    exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  have hH : IsZero (H.obj.obj (op Y)) := AddCommGrpCat.isZero_iff_subsingleton.mpr hsub
  simpa [Functor.sheafPullbackConstruction.sheafPullback, P, H] using hH

private lemma exists_no_arrow_refinement_of_proetale_cover
    {U X Z : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hdisjoint : IsEmpty (pullback j i : Scheme.{u}))
    (V : X.ProEt) [IsAffine V.left]
    (hV : ∀ x : V.left, ∃ z : (pullback V.hom i : Scheme.{u}),
      Specializes x ((pullback.fst V.hom i).base z))
    (S : Sieve V)
    (R : Presieve V) (hR : R ∈ Scheme.ProEt.precoverage X V)
    (hRS : ∀ ⦃Y : X.ProEt⦄ (f : Y ⟶ V), R f → S f) :
    ∃ R' : Presieve V,
      Sieve.generate R' ∈ Scheme.ProEt.topology X V ∧
      Sieve.generate R' ≤ S ∧
      ∀ ⦃Y : X.ProEt⦄ (f : Y ⟶ V), R' f →
        IsEmpty (CostructuredArrow (proetalePostcompose j).op (op Y)) := by
  classical
  obtain ⟨Acover, hAeq, hAqc, A, aq, hAfin, haopen⟩ :=
    exists_finite_affine_refinement_of_ProEt_presieve R hR
  obtain ⟨B, hBfin, hBfact, hBW⟩ := localized_affineCover i A hAfin hV
  let : Finite B.I₀ := hBfin
  let J := {k : B.I₀ // Nonempty (Spec (B.X k))}
  let : Finite J := Finite.of_injective Subtype.val Subtype.val_injective
  let B' : Scheme.AffineCover @WeaklyEtale V.left := {
    I₀ := J
    X := fun k => B.X k.1
    f := fun k => B.f k.1
    idx := fun x => ⟨B.idx x, ⟨Classical.choose (B.covers x)⟩⟩
    covers := by
      intro x
      obtain ⟨w, hw⟩ := B.covers x
      exact ⟨w, hw⟩
    map_prop := fun k => B.map_prop k.1
  }
  let W (k : J) : X.ProEt := by
    let : WeaklyEtale (B'.f k) := B'.map_prop k
    exact Scheme.ProEt.mk (B'.f k ≫ V.hom)
  let gen (k : J) : W k ⟶ V := MorphismProperty.Over.homMk
    (P := @WeaklyEtale) (Q := ⊤) (B'.f k) (by rfl)
  let R' : Presieve V := Presieve.ofArrows W gen
  have hbase : Presieve.ofArrows (fun k : J => Spec (B'.X k))
      (fun k => B'.f k) ∈ Scheme.proetalePrecoverage V.left := by
    let : Finite B'.cover.I₀ := by
      change Finite J
      infer_instance
    let : ∀ k, IsAffine (B'.cover.X k) := by
      intro k
      exact isAffine_Spec (B'.X k)
    let : ∀ k, IsAffineHom (B'.cover.f k) := by
      intro k
      have : IsAffine (B'.cover.X k) := isAffine_Spec (B'.X k)
      have : IsAffine V.left := ‹IsAffine V.left›
      infer_instance
    let : ∀ k, QuasiCompact (B'.cover.f k) := by
      intro k
      infer_instance
    let : Scheme.JointlySurjective (Scheme.precoverage @WeaklyEtale) := by
      constructor
      intro T R hR x
      change R ∈ Scheme.jointlySurjectivePrecoverage T ∧ _ at hR
      rw [Scheme.jointlySurjectivePrecoverage,
        Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hR
      exact hR.1 x
    have : QuasiCompactCover B'.cover.toPreZeroHypercover := QuasiCompactCover.of_finite
    let C := B'.cover.ofQuasiCompactCover
    exact C.mem₀
  have hsmall : R' ∈ Scheme.ProEt.precoverage X V := by
    change R'.map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
      Scheme.proetalePrecoverage V.left
    rw [Presieve.map_ofArrows]
    have harrowEq : Presieve.ofArrows
      (fun k : J => (Scheme.ProEt.forget X ⋙ Over.forget X).obj (W k))
      (fun k => (Scheme.ProEt.forget X ⋙ Over.forget X).map (gen k)) =
      Presieve.ofArrows (fun k : J => Spec (B'.X k)) (fun k => B'.f k) := by
      congr 1
    rw [harrowEq]
    exact hbase
  have hgen : Sieve.generate R' ∈ Scheme.ProEt.topology X V := by
    rw [Scheme.ProEt.topology]
    exact Precoverage.generate_mem_toGrothendieck hsmall
  have hle : Sieve.generate R' ≤ S := by
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro k
    obtain ⟨a, l, hfac⟩ := hBfact k.1
    let Aobj : X.ProEt := by
      let : WeaklyEtale (A.f a) := A.map_prop a
      exact Scheme.ProEt.mk (A.f a ≫ V.hom)
    let uidx := aq.s₀ a
    let Uobj : X.ProEt := by
      let : WeaklyEtale (Acover.f uidx) := Acover.map_prop uidx
      exact Scheme.ProEt.mk (Acover.f uidx ≫ V.hom)
    have hqcomp : aq.h₀ a ≫ Acover.f uidx = A.f a := by
      simpa [uidx, Scheme.AffineCover.cover] using aq.w₀ a
    have hqcompV : aq.h₀ a ≫ (Acover.f uidx ≫ V.hom) = A.f a ≫ V.hom :=
      (Category.assoc (aq.h₀ a) (Acover.f uidx) V.hom).symm.trans
        (congrArg (fun f => f ≫ V.hom) hqcomp)
    let aToU : Aobj ⟶ Uobj := MorphismProperty.Over.homMk
      (P := @WeaklyEtale) (Q := ⊤) (aq.h₀ a) hqcompV
    let memU : R.map (Scheme.ProEt.forget X ⋙ Over.forget X) (Acover.f uidx) := by
      rw [← hAeq]
      exact Presieve.ofArrows.mk uidx
    have memPush : Presieve.functorPushforward
        (Scheme.ProEt.forget X ⋙ Over.forget X) R (Acover.f uidx) :=
      Presieve.map_le_functorPushforward (Scheme.ProEt.forget X ⋙ Over.forget X) R _ _ memU
    let liftData := Presieve.getFunctorPushforwardStructure memPush
    let T₀ := liftData.preobj
    let r := liftData.premap
    let g₀ := liftData.lift
    have hr : R r := liftData.cover
    have hfacU' : Acover.f uidx = g₀ ≫ r.left := liftData.fac
    let gToT : Uobj ⟶ T₀ := MorphismProperty.Over.homMk
      (P := @WeaklyEtale) (Q := ⊤) g₀ (by
        have hrw : r.left ≫ V.hom = T₀.hom := by simpa using r.w
        calc
          g₀ ≫ T₀.hom = g₀ ≫ (r.left ≫ V.hom) :=
            congrArg (fun f => g₀ ≫ f) hrw.symm
          _ = (g₀ ≫ r.left) ≫ V.hom := (Category.assoc g₀ r.left V.hom).symm
          _ = Acover.f uidx ≫ V.hom := (congrArg (fun f => f ≫ V.hom) hfacU').symm)
    have hrS : S r := hRS r hr
    have hUmem : S (gToT ≫ r) := S.downward_closed hrS gToT
    have hfac' : B'.f k = l ≫ A.f a := by simpa [B'] using hfac
    let bToA : W k ⟶ Aobj := MorphismProperty.Over.homMk
      (P := @WeaklyEtale) (Q := ⊤) l (by
        change l ≫ (A.f a ≫ V.hom) = B'.f k ≫ V.hom
        rw [hfac']
        simp [Category.assoc])
    have hgenEq : gen k = bToA ≫ aToU ≫ gToT ≫ r := by
      apply MorphismProperty.Comma.Hom.ext'
      apply CategoryTheory.Comma.hom_ext
      · change B'.f k = l ≫ aq.h₀ a ≫ g₀ ≫ r.left
        calc
          B'.f k = l ≫ A.f a := hfac'
          _ = l ≫ (aq.h₀ a ≫ Acover.f uidx) := congrArg (fun f => l ≫ f) hqcomp.symm
          _ = l ≫ aq.h₀ a ≫ Acover.f uidx := by simp
          _ = l ≫ aq.h₀ a ≫ g₀ ≫ r.left :=
            congrArg (fun f => l ≫ aq.h₀ a ≫ f) hfacU'
      · exact Subsingleton.elim _ _
    have hAinS : S (aToU ≫ gToT ≫ r) := S.downward_closed hUmem aToU
    have hBinS : S (bToA ≫ (aToU ≫ gToT ≫ r)) := S.downward_closed hAinS bToA
    simpa [hgenEq] using hBinS
  refine ⟨R', hgen, hle, ?_⟩
  intro Y f hf
  rcases hf with ⟨k⟩
  let : IsAffine (W k).left := by
    change IsAffine (Spec (B'.X k))
    infer_instance
  have hWk : ∀ w : (W k).left,
      ∃ z : (pullback (W k).hom i : Scheme.{u}),
        Specializes w ((pullback.fst (W k).hom i).base z) := by
    intro w
    change ∃ z : (pullback (B'.f k ≫ V.hom) i : Scheme.{u}),
      Specializes w ((pullback.fst (B'.f k ≫ V.hom) i).base z)
    exact hBW k.1 w
  exact isEmpty_costructuredArrow_of_specializing_closed_fibre j i hdisjoint
    hWk k.property

/-- Extension by zero vanishes on an affine pro-étale object whose points
specialize to a closed fibre disjoint from the weakly étale source. -/
@[stacks 09AG]
theorem isZero_extensionByZero_sections_of_specializes_to_closed
    {U X Z : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hdisjoint : IsEmpty (pullback j i : Scheme.{u}))
    (V : X.ProEt) [IsAffine V.left]
    (hV : ∀ x : V.left, ∃ z : (pullback V.hom i : Scheme.{u}),
      Specializes x ((pullback.fst V.hom i).base z))
    (F : Sheaf (Scheme.ProEt.topology U) AddCommGrpCat.{max (u + 1) v}) :
    IsZero (((Abelian.extensionByZero j).obj F).obj.obj (op V)) := by
  let G := proetalePostcompose j
  let := proetalePostcompose_isContinuous j
  let : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) v} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let : Scheme.proetalePrecoverage.HasIsos := by
    infer_instance
  let : Scheme.proetalePrecoverage.IsStableUnderComposition := by
    infer_instance
  let : Scheme.proetalePrecoverage.IsStableUnderBaseChange := by
    infer_instance
  let : (Scheme.ProEt.precoverage X).HasIsos := by
    unfold Scheme.ProEt.precoverage
    infer_instance
  let : (Scheme.ProEt.precoverage X).IsStableUnderComposition := by
    unfold Scheme.ProEt.precoverage
    infer_instance
  let : (Scheme.ProEt.precoverage X).IsStableUnderBaseChange := by
    unfold Scheme.ProEt.precoverage
    infer_instance
  let : (Scheme.ProEt.precoverage X).HasPullbacks := by infer_instance
  have hRefine : ∀ (S : Sieve V), S ∈ Scheme.ProEt.topology X V →
      ∃ R' : Presieve V,
        Sieve.generate R' ∈ Scheme.ProEt.topology X V ∧
        Sieve.generate R' ≤ S ∧
        ∀ ⦃Y : X.ProEt⦄ (f : Y ⟶ V), R' f →
          IsEmpty (CostructuredArrow G.op (op Y)) := by
    intro S hS
    have htop : S ∈ (Scheme.ProEt.precoverage X).toGrothendieck V := by
      simpa [Scheme.ProEt.topology] using hS
    rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at htop
    obtain ⟨R, hR, hRS⟩ := htop
    exact exists_no_arrow_refinement_of_proetale_cover j i hdisjoint V hV S R hR hRS
  have hpull : IsZero (((Functor.sheafPullbackConstruction.sheafPullback G
      AddCommGrpCat.{max (u + 1) v} (Scheme.ProEt.topology U)
      (Scheme.ProEt.topology X)).obj F).obj.obj (op V)) :=
    isZero_sheafPullback_obj_of_refinably_no_costructured_arrows
      (C := U.ProEt) (D := X.ProEt) (G := G)
      (J := Scheme.ProEt.topology U) (K := Scheme.ProEt.topology X)
      (F := F) (Y := V) hRefine
  have hAdj :
      Abelian.extensionByZero j ⊣
        G.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) := by
    change Abelian.extensionByZero j ⊣ Abelian.proetaleRestriction j
    exact Abelian.extensionByZero_adjunction j
  let hAdj₂ := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
    AddCommGrpCat.{max (u + 1) v} (Scheme.ProEt.topology U)
    (Scheme.ProEt.topology X)
  let e := Adjunction.leftAdjointUniq hAdj hAdj₂
  let eP := (sheafToPresheaf (Scheme.ProEt.topology X)
    AddCommGrpCat.{max (u + 1) v}).mapIso (e.app F)
  have hpoint : IsIso (eP.hom.app (op V)) := by infer_instance
  exact IsZero.of_iso hpull (asIso (eP.hom.app (op V)))

end AlgebraicGeometry.ProEtale

end
