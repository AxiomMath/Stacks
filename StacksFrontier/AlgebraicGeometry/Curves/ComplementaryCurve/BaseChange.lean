module

public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Coproduct
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.BaseChange
import all StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.RationalTail
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components

/-!
# The closure of the complement under base change and decomposition

Two operations on a closed subscheme `C` of a scheme `Y` meet when a curve over a field is
extended to a larger field: flat base change, and decomposition of `C` into open and closed
pieces. Flat base change of the closure of the complement ([Stacks, Tag 081I]) and the
categorical facts used to decompose a base change of a curve into a finite coproduct of closed
subschemes are those of
`StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.BaseChange`. This file adds the
decomposition on an arbitrary, not necessarily reduced, ambient scheme: for an open and closed
piece `D` of `C`, the intersection of `D` with the closure of its own complement is
`D ⊔ (closure of Y ∖ C)`, because the two complements agree near `D`.

## Main results

* `AlgebraicGeometry.intersectionWithComplementaryCurveIdeal_of_openImmersion_general`: the
  intersection with the closure of the complement of an open and closed piece, on an arbitrary
  scheme.
* `AlgebraicGeometry.intersectionWithComplementaryCurve_isPullback_general`: for an open and
  closed piece of a flat base change of an arbitrary scheme, that intersection is a base change.
* `AlgebraicGeometry.exists_iso_sigma_baseChange_of_geometricallyIntegral`: the base change of a
  geometrically integral one-dimensional closed subscheme of a curve, with separable field of
  global functions, is a finite disjoint union of integral irreducible components.

## References

* [Stacks Project, Tag 081I](https://stacks.math.columbia.edu/tag/081I)
* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **The ideal sheaf of a closed subscheme vanishes nowhere off its support.** On an affine open
disjoint from the support of `D`, the ideal of `D` is the unit ideal. -/
theorem ideal_eq_top_of_disjoint_support {Y : Scheme.{u}} (D : Y.IdealSheafData)
    (W : Y.affineOpens) (hW : Disjoint (D.support : Set Y) (W : Set Y)) : D.ideal W = ⊤ := by
  have h := (W.2.fromSpec_image_zeroLocus (D.ideal W : Set Γ(Y, W))).trans_subset
    (Set.subset_inter (Scheme.IdealSheafData.zeroLocus_inter_subset_supportSet D W)
      Set.inter_subset_right)
  have hempty : (D.supportSet ∩ (W : Set Y)) = ∅ := Set.disjoint_iff_inter_eq_empty.mp hW
  rw [hempty] at h
  exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
    (Set.image_eq_empty.mp (Set.subset_empty_iff.mp h))

/-- **Sections vanishing off a larger closed set.** If `V ⊓ W ≤ U`, then a section over the affine
open `W` vanishing on `U ⊓ W` also vanishes on `V ⊓ W`. -/
private theorem Scheme.Opens.ker_ι_ideal_le_of_inf_le {Y : Scheme.{u}} {U V : Y.Opens}
    [QuasiCompact U.ι] [QuasiCompact V.ι] (W : Y.affineOpens) (h : V ⊓ W ≤ U) :
    U.ι.ker.ideal W ≤ V.ι.ker.ideal W := by
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
  intro a ha
  simp only [RingHom.mem_ker, Scheme.Opens.ι_app] at ha ⊢
  have hO : V.ι ''ᵁ V.ι ⁻¹ᵁ (W : Y.Opens) ≤ U.ι ''ᵁ U.ι ⁻¹ᵁ (W : Y.Opens) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      Scheme.Opens.opensRange_ι]
    exact le_inf h inf_le_right
  have hfac : Y.presheaf.map (homOfLE (x := V.ι ''ᵁ V.ι ⁻¹ᵁ (W : Y.Opens))
        (Set.image_preimage_subset _ _)).op =
      Y.presheaf.map (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ (W : Y.Opens))
        (Set.image_preimage_subset _ _)).op ≫ Y.presheaf.map (homOfLE hO).op := by
    rw [← Functor.map_comp]
    rfl
  refine (congrArg (fun φ => φ.hom a) hfac).trans ?_
  simp only [CommRingCat.comp_apply]
  exact (congrArg (Y.presheaf.map (homOfLE hO).op).hom ha).trans (map_zero _)

/-- **The closure of the complement of an open and closed piece.** Let `C` and `D` be closed
subschemes of `Y` whose supports satisfy `supp C = supp D ∪ E` with `E` closed and disjoint from
`supp D`. Near `supp D` the complements of `C` and of `D` agree, and away from `supp D` the ideal
of `D` is the unit ideal, so `D ⊔ (closure of Y ∖ D) = D ⊔ (closure of Y ∖ C)`. -/
theorem intersectionWithComplementaryCurveIdeal_of_disjoint_union_general
    {Y : Scheme.{u}} (C D : Y.IdealSheafData)
    [QuasiCompact (Scheme.Opens.ι C.support.compl)]
    [QuasiCompact (Scheme.Opens.ι D.support.compl)]
    (E : TopologicalSpace.Closeds Y)
    (hC : (C.support : Set Y) = (D.support : Set Y) ∪ E)
    (hDE : Disjoint (D.support : Set Y) (E : Set Y)) :
    intersectionWithComplementaryCurveIdeal D =
      D ⊔ complementaryCurveIdeal C := by
  have hmem (x : Y) : x ∈ C.support.compl ↔ x ∉ D.support ∧ x ∉ E := by
    simp [TopologicalSpace.Closeds.compl, ← SetLike.mem_coe, hC]
  have hle : C.support.compl ≤ D.support.compl := fun x hx => ((hmem x).1 hx).1
  refine le_antisymm (sup_le_sup_left ?_ _) (sup_le le_sup_left ?_)
  · change (Scheme.Opens.ι D.support.compl).ker ≤ (Scheme.Opens.ι C.support.compl).ker
    rw [← Scheme.homOfLE_ι Y hle]
    exact Scheme.Hom.le_ker_comp _ _
  · let P : Y.affineOpens → Prop := fun W =>
      (W : Set Y) ⊆ (E : Set Y)ᶜ ∨ (W : Set Y) ⊆ (D.support : Set Y)ᶜ
    refine Scheme.IdealSheafData.le_of_iSup_eq_top (ι := {W // P W}) (fun W => W.1) ?_ ?_
    · refine top_le_iff.mp fun x _ => ?_
      have hx : x ∈ (E : Set Y)ᶜ ∪ (D.support : Set Y)ᶜ := by
        rw [← Set.compl_inter, Set.disjoint_iff_inter_eq_empty.mp hDE.symm, Set.compl_empty]
        trivial
      rcases hx with hx | hx
      · obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWE⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx
          E.isClosed.isOpen_compl
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, .inl hWE⟩, hxW⟩
      · obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWD⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx
          D.support.isClosed.isOpen_compl
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, .inr hWD⟩, hxW⟩
    · rintro ⟨W, hW | hW⟩
      · refine le_trans ?_ le_sup_right
        change ((Scheme.Opens.ι C.support.compl).ker).ideal W ≤
          ((Scheme.Opens.ι D.support.compl).ker).ideal W
        refine Scheme.Opens.ker_ι_ideal_le_of_inf_le W ?_
        rintro x ⟨hxD, hxW⟩
        exact (hmem x).2 ⟨hxD, fun h => hW hxW h⟩
      · refine le_trans ?_ le_sup_left
        exact le_top.trans_eq (ideal_eq_top_of_disjoint_support D W
          (Set.disjoint_left.mpr fun x hx hxW => hW hxW hx)).symm

/-- **The closure of the complement of an open and closed subscheme of a closed subscheme.** If
`D ⟶ C` is an open immersion over `Y` of closed subschemes, then
`D ⊔ (closure of Y ∖ D) = D ⊔ (closure of Y ∖ C)`. -/
theorem intersectionWithComplementaryCurveIdeal_of_openImmersion_general
    {Y : Scheme.{u}} (C D : Y.IdealSheafData)
    [QuasiCompact (Scheme.Opens.ι C.support.compl)]
    [QuasiCompact (Scheme.Opens.ι D.support.compl)]
    (j : D.subscheme ⟶ C.subscheme) [IsOpenImmersion j]
    (hj : j ≫ C.subschemeι = D.subschemeι) :
    intersectionWithComplementaryCurveIdeal D =
      D ⊔ complementaryCurveIdeal C := by
  let E : TopologicalSpace.Closeds Y :=
    ⟨C.subschemeι '' (Set.range j)ᶜ,
      C.subschemeι.isClosedEmbedding.isClosedMap _
        (j.isOpenEmbedding.isOpen_range.isClosed_compl)⟩
  have hD : (D.support : Set Y) = C.subschemeι '' Set.range j := by
    rw [← D.range_subschemeι, ← hj]
    change Set.range (C.subschemeι ∘ j) = _
    exact Set.range_comp _ _
  have hC : (C.support : Set Y) = (D.support : Set Y) ∪ E := by
    rw [hD, ← C.range_subschemeι]
    change Set.range C.subschemeι =
      C.subschemeι '' Set.range j ∪ C.subschemeι '' (Set.range j)ᶜ
    rw [← Set.image_union, Set.union_compl_self, Set.image_univ]
  have hDE : Disjoint (D.support : Set Y) (E : Set Y) := by
    rw [hD, Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    exact hy (C.subschemeι.isClosedEmbedding.injective hyx ▸ hx)
  exact intersectionWithComplementaryCurveIdeal_of_disjoint_union_general C D E hC hDE

/-- **The intersection with the closure of the complement of an open and closed piece of a flat
base change.** Let `p : Y ⟶ X` be flat, let `C` be a closed subscheme of `X` and let `D` be an open
and closed subscheme of `C ×_X Y`. Then the intersection of `D` with the closure of its complement
is the base change along `D ⟶ C` of the intersection of `C` with the closure of its complement. -/
theorem intersectionWithComplementaryCurve_isPullback_general
    {X Y : Scheme.{u}}
    (C : X.IdealSheafData) (D : Y.IdealSheafData)
    (p : Y ⟶ X) [Flat p]
    [QuasiCompact (Scheme.Opens.ι C.support.compl)]
    [QuasiCompact (Scheme.Opens.ι (C.comap p).support.compl)]
    [QuasiCompact (Scheme.Opens.ι D.support.compl)]
    (j : D.subscheme ⟶ (C.comap p).subscheme) [IsOpenImmersion j]
    (hj : j ≫ (C.comap p).subschemeι = D.subschemeι)
    (c : D.subscheme ⟶ C.subscheme)
    (hc : c ≫ C.subschemeι = D.subschemeι ≫ p) :
    let I := intersectionWithComplementaryCurveIdeal D
    let J := intersectionWithComplementaryCurveIdeal C
    ∃ r : I.subscheme ⟶ J.subscheme,
      IsPullback (Scheme.IdealSheafData.inclusion (le_sup_left : D ≤ I)) r c
        (Scheme.IdealSheafData.inclusion (le_sup_left : C ≤ J)) := by
  let I := intersectionWithComplementaryCurveIdeal D
  let J := intersectionWithComplementaryCurveIdeal C
  let iD := Scheme.IdealSheafData.inclusion (le_sup_left : D ≤ I)
  let iC := Scheme.IdealSheafData.inclusion (le_sup_left : C ≤ J)
  have hle : C.comap p ≤ D := by
    rw [← (C.comap p).ker_subschemeι, ← D.ker_subschemeι, ← hj]
    exact Scheme.Hom.le_ker_comp j (C.comap p).subschemeι
  have hI : I = D ⊔ J.comap p := by
    change intersectionWithComplementaryCurveIdeal D = _
    rw [intersectionWithComplementaryCurveIdeal_of_openImmersion_general (C.comap p) D j hj,
      ← intersectionWithComplementaryCurveIdeal_comap C p, ← sup_assoc, sup_eq_left.mpr hle]
  have hmap : J ≤ I.map p :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr (by rw [hI]; exact le_sup_right)
  let r := I.subschemeMap J p hmap
  refine ⟨r, isPullback_of_isClosedImmersion iD iC r c ?_ ?_⟩
  · apply (cancel_mono C.subschemeι).1
    calc
      (iD ≫ c) ≫ C.subschemeι = (iD ≫ D.subschemeι) ≫ p := by
        rw [Category.assoc, hc, Category.assoc]
      _ = I.subschemeι ≫ p := by rw [Scheme.IdealSheafData.inclusion_subschemeι]
      _ = r ≫ J.subschemeι := (Scheme.IdealSheafData.subschemeMap_subschemeι I J p hmap).symm
      _ = (r ≫ iC) ≫ C.subschemeι := by
        rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  · rw [ker_inclusion_eq_comap, ker_inclusion_eq_comap]
    have hzero : D.comap D.subschemeι = ⊥ := by
      change (pullback.fst D.subschemeι D.subschemeι).ker = ⊥
      exact Scheme.Hom.ker_eq_bot_of_isIso _
    change (J.comap C.subschemeι).comap c = I.comap D.subschemeι
    calc
      (J.comap C.subschemeι).comap c = J.comap (c ≫ C.subschemeι) :=
        (Scheme.IdealSheafData.comap_comp J c C.subschemeι).symm
      _ = J.comap (D.subschemeι ≫ p) := by rw [hc]
      _ = (J.comap p).comap D.subschemeι :=
        Scheme.IdealSheafData.comap_comp J D.subschemeι p
      _ = D.comap D.subschemeι ⊔ (J.comap p).comap D.subschemeι := by
        rw [hzero, bot_sup_eq]
      _ = (D ⊔ J.comap p).comap D.subschemeι :=
        (Scheme.IdealSheafData.comap_sup D (J.comap p) D.subschemeι).symm
      _ = I.comap D.subschemeι := congrArg (fun E => E.comap D.subschemeι) hI.symm

/-- **A nonempty closure of the complement has a nonempty complement.** If the closure of the
complement of `C` is nonempty, then so is the complement of the support of `C`. -/
private theorem nonempty_compl_support_of_nonempty_complementaryCurve {X : Scheme.{u}}
    (C : X.IdealSheafData) (hne : Nonempty (complementaryCurve C)) :
    ((C.support : Set X)ᶜ).Nonempty := by
  let U : X.Opens := C.support.compl
  let u : U.toScheme ⟶ X := U.ι
  by_contra hU
  have : IsEmpty U.toScheme := ⟨fun x => hU ⟨x.1, x.2⟩⟩
  have hdense : Dense (Set.range u.toImage.base) :=
    (IsDominant.denseRange : DenseRange u.toImage.base)
  have hrange : Set.range u.toImage.base = ∅ := Set.range_eq_empty _
  obtain ⟨z⟩ := hne
  simpa [hrange] using hdense z

/-- **The complement of a support pulls back to a nonempty set along a surjection.** -/
private theorem nonempty_compl_support_comap {X Y : Scheme.{u}} (p : Y ⟶ X) [Surjective p]
    (C : X.IdealSheafData) (h : ((C.support : Set X)ᶜ).Nonempty) :
    (((C.comap p).support : Set Y)ᶜ).Nonempty := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨y, hy⟩ := ‹Surjective p›.surj x
  refine ⟨y, ?_⟩
  change y ∉ (C.comap p).support
  rw [Scheme.IdealSheafData.support_comap]
  change p y ∉ (C.support : Set X)
  rwa [hy]

/-- **Decomposition of the base change of a geometrically integral closed subscheme.** Let `X` be
proper over a field `k` with `H⁰(X, 𝒪_X) = k` and of dimension one, let `C ⊆ X` be an integral
one-dimensional closed subscheme whose field of global functions `k'` is separable over `k` and
over which `C` is geometrically integral, and suppose the closure of the complement of `C` is
nonempty. For a field extension `K/k` write `K ⊗_k k' = ∏ᵢ Lᵢ`. Then `C_K ⊆ X_K` is the disjoint
union of closed subschemes `Dᵢ`, compatibly with the closed immersions, where `Dᵢ = C ×_{k'} Lᵢ`
is integral, an irreducible component of `X_K`, and has nonempty complement, and `Dᵢ` is open in
`C_K` over `C`. -/
theorem exists_iso_sigma_baseChange_of_geometricallyIntegral
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (C : X.IdealSheafData) [IsIntegral C.subscheme]
    (hCdim : topologicalKrullDim C.subscheme = 1) (hne : Nonempty (complementaryCurve C))
    (hsep :
      letI : Field Γ(C.subscheme, ⊤) :=
        (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
      letI : Algebra k Γ(C.subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫
          (C.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
      Algebra.IsSeparable k Γ(C.subscheme, ⊤))
    (hgeom :
      letI : Field Γ(C.subscheme, ⊤) :=
        (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
      GeometricallyIntegral C.subscheme.toSpecΓ) :
    letI : Field Γ(C.subscheme, ⊤) :=
      (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
    let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let Y := (pullback (X ↘ Spec (.of k)) g : Scheme.{u})
    let p : Y ⟶ X := pullback.fst (X ↘ Spec (.of k)) g
    ∃ (ι : Type u) (_ : Finite ι) (L : ι → Type u) (_ : ∀ i, Field (L i))
      (φ : ∀ i, CommRingCat.of Γ(C.subscheme, ⊤) ⟶ CommRingCat.of (L i))
      (D : ι → Y.IdealSheafData) (c : ∀ i, (D i).subscheme ⟶ C.subscheme)
      (q : ∀ i, (D i).subscheme ⟶ Spec (.of (L i)))
      (j : ∀ i, (D i).subscheme ⟶ (C.comap p).subscheme) (_ : ∀ i, IsOpenImmersion (j i))
      (e : (∐ fun i ↦ (D i).subscheme) ≅ (C.comap p).subscheme),
      e.hom ≫ (C.comap p).subschemeι = Sigma.desc (fun i ↦ (D i).subschemeι) ∧
      (∀ i, IsIntegral (D i).subscheme) ∧
      (∀ i, ((D i).support : Set Y) ∈ irreducibleComponents Y) ∧
      (∀ i, Nonempty (complementaryCurve (D i))) ∧
      (∀ i, IsPullback (c i) (q i) C.subscheme.toSpecΓ (Spec.map (φ i))) ∧
      (∀ i, c i ≫ C.subschemeι = (D i).subschemeι ≫ p) ∧
      (∀ i, j i ≫ (C.comap p).subschemeι = (D i).subschemeι) := by
  classical
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := pullback (X ↘ Spec (.of k)) g
  let p : Y ⟶ X := pullback.fst (X ↘ Spec (.of k)) g
  let hY := (IsPullback.of_hasPullback (X ↘ Spec (.of k)) g).flip
  let A := Γ(C.subscheme, ⊤)
  let : Field A := (isField_of_universallyClosed k
    (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
  let : Algebra k A :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (C.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
  have : Module.Finite k A :=
    RingHom.Finite.comp
      (finite_appTop_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k))))
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.finite
  have : Algebra.IsSeparable k A := hsep
  have : Algebra.FormallyEtale k A := Algebra.FormallyEtale.of_isSeparable k A
  have : Algebra.FiniteType k A := inferInstance
  have : Algebra.FinitePresentation k A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale k A := ⟨inferInstance, inferInstance⟩
  obtain ⟨ι, hι, L, hL, hKL, eA, hLfin⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K (K ⊗[k] A)).mp inferInstance
  have : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let (i : ι) : Field (L i) := hL i
  let (i : ι) : Algebra K (L i) := hKL i
  let f := C.subschemeι ≫ (X ↘ Spec (.of k))
  let α := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop
  let a : Spec (.of A) ⟶ Spec (.of k) := Spec.map α
  have hfa : C.subscheme.toSpecΓ ≫ a = f := by
    dsimp [a, α]
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  let T := pullback a g
  let q : T ⟶ Spec (.of A) := pullback.fst a g
  let r : T ⟶ Spec (.of K) := pullback.snd a g
  obtain ⟨eT⟩ := nonempty_sigmaSpec_iso_pullback k K A L eA
  let π (i : ι) : Spec (.of (L i)) ⟶ T :=
    Sigma.ι (fun i ↦ Spec (.of (L i))) i ≫ eT.hom
  have hπ : Sigma.desc π = eT.hom := Sigma.hom_ext _ _ fun i => Sigma.ι_comp_desc π i
  have : IsIso (Sigma.desc π) := hπ ▸ inferInstance
  let φ (i : ι) : CommRingCat.of A ⟶ CommRingCat.of (L i) :=
    Classical.choose (Spec.map_surjective (π i ≫ q))
  have hφ (i : ι) : Spec.map (φ i) = π i ≫ q :=
    Classical.choose_spec (Spec.map_surjective (π i ≫ q))
  let (i : ι) : Algebra A (L i) := (φ i).hom.toAlgebra
  let Z := pullback C.subscheme.toSpecΓ q
  let v : Z ⟶ C.subscheme := pullback.fst C.subscheme.toSpecΓ q
  let z : Z ⟶ T := pullback.snd C.subscheme.toSpecΓ q
  have htot : IsPullback (z ≫ r) v g f := by
    rw [← hfa]
    exact (IsPullback.of_hasPullback C.subscheme.toSpecΓ q).flip.paste_horiz
      (IsPullback.of_hasPullback a g).flip
  let j : Z ⟶ Y := hY.lift (z ≫ r) (v ≫ C.subschemeι)
    (by rw [htot.w, Category.assoc])
  have hj : IsPullback j v p C.subschemeι := htot.of_right' hY
  let eZ : Z ≅ (C.comap p).subscheme := hj.isoPullback ≪≫ (C.comapIso p).symm
  have heZ : eZ.hom ≫ (C.comap p).subschemeι = j := by simp [eZ]
  have : IsClosedImmersion j := by
    rw [← hj.isoPullback_hom_fst]
    infer_instance
  have : IsProper (Y ↘ Spec (.of K)) := by
    change IsProper (pullback.snd (X ↘ Spec (.of k)) g)
    infer_instance
  let W (i : ι) := pullback z (π i)
  let w (i : ι) : W i ⟶ Z := pullback.fst z (π i)
  let bL (i : ι) : W i ⟶ Spec (.of (L i)) := pullback.snd z (π i)
  have (i : ι) : IsOpenImmersion (π i) := by dsimp [π]; infer_instance
  have (i : ι) : IsOpenImmersion (w i) := by dsimp [w]; infer_instance
  have : IsIso (Sigma.desc w) := isIso_sigmaDesc_pullback_fst _ π z
  let e := asIso (Sigma.desc w) ≪≫ eZ
  obtain ⟨D, eD, b, heD, hb⟩ := exists_idealSheafData_of_coproduct_iso (C.comap p) W e
  have hd (i : ι) : (eD i).hom ≫ (D i).subschemeι = w i ≫ j := by
    rw [heD]
    simp [e, Category.assoc, heZ]
  have hYdim : topologicalKrullDim Y = 1 :=
    (topologicalKrullDim_baseChange k K p
      (Y ↘ Spec (.of K)) (X ↘ Spec (.of k)) hY.flip).trans hdim
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of K))
  have : GeometricallyIntegral C.subscheme.toSpecΓ := hgeom
  have hWi (i : ι) : IsPullback (w i ≫ v) (bL i) C.subscheme.toSpecΓ
      (Spec.map (φ i)) := by
    rw [hφ i]
    exact (IsPullback.of_hasPullback z (π i)).paste_horiz
      (IsPullback.of_hasPullback C.subscheme.toSpecΓ q)
  have hWi_integral (i : ι) : IsIntegral (W i) := by
    have : IsIntegral (pullback C.subscheme.toSpecΓ (Spec.map (φ i))) :=
      GeometricallyIntegral.isIntegral_of_subsingleton
        (pullback.snd C.subscheme.toSpecΓ (Spec.map (φ i)))
    exact IsIntegral.of_isIso (hWi i).isoPullback.inv
  have : IsProper C.subscheme.toSpecΓ := by
    have : IsProper (C.subscheme.toSpecΓ ≫ a) := hfa ▸ inferInstance
    exact IsProper.of_comp (f := C.subscheme.toSpecΓ) (g := a)
  have : IsIso ((Scheme.ΓSpecIso (.of A)).inv ≫ C.subscheme.toSpecΓ.appTop) := by
    dsimp [A]
    rw [Scheme.toSpecΓ_appTop]
    infer_instance
  have hWi_dim (i : ι) : topologicalKrullDim (W i) = 1 :=
    (topologicalKrullDim_baseChange A (L i) (w i ≫ v)
      (bL i) C.subscheme.toSpecΓ (hWi i)).trans hCdim
  have hD_integral (i : ι) : IsIntegral (D i).subscheme :=
    IsIntegral.of_isIso (eD i).hom
  have hD_dim (i : ι) : topologicalKrullDim (D i).subscheme = 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq (eD i).hom
      (eD i).hom.homeomorph.isHomeomorph]
    exact hWi_dim i
  have hSupport (i : ι) : ((D i).support : Set Y) ∈ irreducibleComponents Y := by
    have : IsIntegral (D i).subscheme := hD_integral i
    exact support_mem_irreducibleComponents_of_dimension_one
      (D i) hYdim.le (hD_dim i)
  have hDmap (i : ι) : (D i).subschemeι = (eD i).inv ≫ w i ≫ j :=
    (Iso.eq_inv_comp _).mpr (hd i)
  have hDsubset (i : ι) :
      ((D i).support : Set Y) ⊆ ((C.comap p).support : Set Y) := by
    rw [← (D i).range_subschemeι, ← (C.comap p).range_subschemeι]
    rintro y ⟨z, rfl⟩
    refine ⟨eZ.hom (w i ((eD i).inv z)), ?_⟩
    rw [hDmap i]
    exact congrArg (fun f : Z ⟶ Y => f (w i ((eD i).inv z))) heZ
  have hsurj : Surjective p := by
    have hg : Surjective g := ⟨fun _ => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
    exact MorphismProperty.of_isPullback hY hg
  have hD_complementaryCurve_nonempty (i : ι) : Nonempty (complementaryCurve (D i)) := by
    obtain ⟨y, hy⟩ := nonempty_compl_support_comap p C
      (nonempty_compl_support_of_nonempty_complementaryCurve C hne)
    exact ⟨(Scheme.Opens.ι (D i).support.compl).toImage ⟨y, fun hmem => hy (hDsubset i hmem)⟩⟩
  let cD (i : ι) : (D i).subscheme ⟶ C.subscheme :=
    (eD i).inv ≫ w i ≫ v
  have hcD (i : ι) : cD i ≫ C.subschemeι = (D i).subschemeι ≫ p := by
    calc
      cD i ≫ C.subschemeι = (eD i).inv ≫ w i ≫ (v ≫ C.subschemeι) := by
        simp [cD, Category.assoc]
      _ = (eD i).inv ≫ w i ≫ (j ≫ p) := by rw [← hj.w]
      _ = (D i).subschemeι ≫ p := by simp [Category.assoc, hDmap i]
  let fDbase (i : ι) : (D i).subscheme ⟶ Spec (.of (L i)) :=
    (eD i).inv ≫ bL i
  have hDbase (i : ι) : IsPullback (cD i) (fDbase i) C.subscheme.toSpecΓ
      (Spec.map (φ i)) :=
    (hWi i).of_iso (eD i) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [cD]) (by simp [fDbase])
      (by simp) (by simp)
  let jd (i : ι) := (eD i).inv ≫ w i ≫ eZ.hom
  have hjd (i : ι) : jd i ≫ (C.comap p).subschemeι = (D i).subschemeι := by
    simp [jd, Category.assoc, heZ, ← hd i]
  exact ⟨ι, hι, L, hL, φ, D, cD, fDbase, jd, fun i => by dsimp [jd]; infer_instance, b, hb,
    hD_integral, hSupport, hD_complementaryCurve_nonempty, hDbase, hcD, hjd⟩

end AlgebraicGeometry

end
