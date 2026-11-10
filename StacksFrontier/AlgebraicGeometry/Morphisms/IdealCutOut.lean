module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# The locally closed subscheme cut out by two ideals

For a scheme `X` and ideals `I, J` of its global sections, `V(I) ∩ D(J)` carries a natural
structure of locally closed subscheme: the open subscheme over `D(J) = ⋃_{f ∈ J} D(f)` of the
closed subscheme cut out by `I`. When `X` is affine, a morphism `g : T ⟶ X` from an affine
scheme factors through it exactly when `I` maps to zero and `J` generates the unit ideal in
`Γ(T, 𝒪_T)`.

## Main definitions

* `AlgebraicGeometry.Scheme.idealBasicOpen J` is the open `D(J)` of `X`.
* `AlgebraicGeometry.Scheme.cutOut I J` and `AlgebraicGeometry.Scheme.cutOutι I J` are the
  locally closed subscheme `V(I) ∩ D(J)` and its inclusion into `X`.

## Main results

* `AlgebraicGeometry.Scheme.exists_comp_cutOutι_iff_of_isAffine`: the factorization criterion
  over an affine scheme.
* `AlgebraicGeometry.Scheme.isClosedImmersion_cutOutι_top`: for `J = ⊤` the inclusion is a
  closed immersion.
* `AlgebraicGeometry.Scheme.locallyOfFinitePresentation_cutOutι` and
  `AlgebraicGeometry.Scheme.quasiCompact_cutOutι`: for finitely generated ideals over an affine
  scheme the inclusion is locally of finite presentation and quasi-compact.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The open `D(J) = ⋃_{f ∈ J} D(f)` of a scheme `X`, for an ideal `J` of `Γ(X, 𝒪_X)`: the
complement of the zero locus of `J`. -/
def idealBasicOpen (J : Ideal Γ(X, ⊤)) : X.Opens :=
  ⟨(X.zeroLocus (U := ⊤) (J : Set Γ(X, ⊤)))ᶜ, (X.zeroLocus_isClosed _).isOpen_compl⟩

/-- A point lies in `D(J)` exactly when it lies in `D(f)` for some `f ∈ J`. -/
theorem mem_idealBasicOpen {J : Ideal Γ(X, ⊤)} {x : X} :
    x ∈ X.idealBasicOpen J ↔ ∃ f ∈ J, x ∈ X.basicOpen f := by
  change x ∈ (X.zeroLocus (U := ⊤) (J : Set Γ(X, ⊤)))ᶜ ↔ _
  rw [Set.mem_compl_iff, mem_zeroLocus_iff]
  push Not
  rfl

/-- `D(⊤)` is the whole scheme. -/
theorem idealBasicOpen_top : X.idealBasicOpen (⊤ : Ideal Γ(X, ⊤)) = ⊤ := by
  ext x
  simp only [Opens.coe_top, Set.mem_univ, iff_true, SetLike.mem_coe]
  exact mem_idealBasicOpen.2 ⟨1, Submodule.mem_top, by simp⟩

/-- On an affine scheme, the ideal sheaves of two ideals of global sections compare as the
ideals do. -/
theorem ofIdealTop_le_ofIdealTop_iff [IsAffine X] (I K : Ideal Γ(X, ⊤)) :
    Scheme.IdealSheafData.ofIdealTop I ≤ Scheme.IdealSheafData.ofIdealTop K ↔ I ≤ K := by
  simpa using map_le_map_iff (Scheme.IdealSheafData.equivOfIsAffine (X := X)).symm (a := I) (b := K)

variable (I J : Ideal Γ(X, ⊤))

/-- The locally closed subscheme `V(I) ∩ D(J)` of `X`: the open subscheme over `D(J)` of the
closed subscheme cut out by `I`. -/
noncomputable abbrev cutOut : Scheme.{u} :=
  (Scheme.IdealSheafData.ofIdealTop I).subschemeι ⁻¹ᵁ X.idealBasicOpen J

/-- The inclusion of `V(I) ∩ D(J)` into `X`. -/
noncomputable def cutOutι : cutOut I J ⟶ X :=
  Scheme.Opens.ι _ ≫ (Scheme.IdealSheafData.ofIdealTop I).subschemeι

/-- The inclusion of `V(I) ∩ D(J)` is an immersion. -/
instance : IsImmersion (cutOutι I J) := by
  unfold cutOutι; infer_instance

/-- The image of `V(I) ∩ D(J)` lies in `D(J)`. -/
theorem range_cutOutι_subset : Set.range (cutOutι I J).base ⊆ X.idealBasicOpen J := by
  rintro _ ⟨x, rfl⟩
  exact x.2

/-- Over an affine `X`, a morphism `g` is a morphism into `V(I)` on the level of ideals iff `g`
kills `I` on global sections. -/
private theorem ker_subschemeι_le_ker_iff [IsAffine X] {T : Scheme.{u}} (g : T ⟶ X) :
    (Scheme.IdealSheafData.ofIdealTop I).subschemeι.ker ≤ g.ker ↔
      I ≤ RingHom.ker g.appTop.hom := by
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.ker_of_isAffine]
  exact ofIdealTop_le_ofIdealTop_iff _ _

/-- Over an affine `X`, a morphism that factors through `V(I) ∩ D(J)` kills `I` on global
sections. -/
theorem le_ker_appTop_of_comp_cutOutι [IsAffine X] {T : Scheme.{u}} {g : T ⟶ X} {h : T ⟶ cutOut I J}
    (hg : h ≫ cutOutι I J = g) : I ≤ RingHom.ker g.appTop.hom := by
  refine (ker_subschemeι_le_ker_iff I g).1 ?_
  rw [← hg, cutOutι, ← Category.assoc]
  exact Scheme.Hom.le_ker_comp _ _

/-- **Factorization through `V(I) ∩ D(J)`**, over an affine `X` and for an arbitrary source: a
morphism factors through the locally closed subscheme exactly when it kills `I` on global
sections and lands in `D(J)`. -/
theorem exists_comp_cutOutι_iff [IsAffine X] {T : Scheme.{u}} (g : T ⟶ X) :
    (∃ h, h ≫ cutOutι I J = g) ↔
      I ≤ RingHom.ker g.appTop.hom ∧ Set.range g.base ⊆ X.idealBasicOpen J := by
  refine ⟨fun ⟨h, hg⟩ => ⟨le_ker_appTop_of_comp_cutOutι I J hg, ?_⟩, fun ⟨hI, hJ⟩ => ?_⟩
  · rintro _ ⟨t, rfl⟩
    rw [← hg]
    exact range_cutOutι_subset I J ⟨h.base t, rfl⟩
  · set C := Scheme.IdealSheafData.ofIdealTop I
    set g' := IsClosedImmersion.lift C.subschemeι g ((ker_subschemeι_le_ker_iff I g).2 hI)
    have hg' : g' ≫ C.subschemeι = g := IsClosedImmersion.lift_fac _ _ _
    have hrange : Set.range g'.base ⊆
        Set.range (Scheme.Opens.ι (C.subschemeι ⁻¹ᵁ X.idealBasicOpen J)).base := by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι]
      change C.subschemeι.base (g'.base t) ∈ X.idealBasicOpen J
      rw [← Scheme.Hom.comp_apply, hg']
      exact hJ ⟨t, rfl⟩
    refine ⟨IsOpenImmersion.lift _ g' hrange, ?_⟩
    rw [cutOutι, ← Category.assoc, IsOpenImmersion.lift_fac, hg']

/-- Over an affine source, landing in `D(J)` is the condition that `J` generates the unit
ideal of the global sections of the source. -/
theorem range_subset_idealBasicOpen_iff {T : Scheme.{u}} [IsAffine T] (g : T ⟶ X) :
    Set.range g.base ⊆ X.idealBasicOpen J ↔ J.map g.appTop.hom = ⊤ := by
  rw [Ideal.map, ← (isAffineOpen_top T).self_le_iSup_basicOpen_iff]
  constructor
  · intro h t _
    obtain ⟨f, hfJ, hf⟩ := mem_idealBasicOpen.1 (h ⟨t, rfl⟩)
    have ht : t ∈ g ⁻¹ᵁ X.basicOpen f := hf
    rw [Scheme.preimage_basicOpen_top] at ht
    exact Opens.mem_iSup.2 ⟨⟨_, Set.mem_image_of_mem _ hfJ⟩, ht⟩
  · rintro h _ ⟨t, rfl⟩
    obtain ⟨⟨_, ⟨f, hfJ, rfl⟩⟩, ht⟩ := Opens.mem_iSup.1 (h (Set.mem_univ t))
    refine mem_idealBasicOpen.2 ⟨f, hfJ, ?_⟩
    change t ∈ g ⁻¹ᵁ X.basicOpen f
    rwa [Scheme.preimage_basicOpen_top]

/-- **Factorization through `V(I) ∩ D(J)` between affine schemes**: a morphism `g : T ⟶ X` of
affine schemes factors through the locally closed subscheme exactly when `I` maps to zero and
`J` generates the unit ideal in `Γ(T, 𝒪_T)`. -/
theorem exists_comp_cutOutι_iff_of_isAffine [IsAffine X] {T : Scheme.{u}} [IsAffine T]
    (g : T ⟶ X) :
    (∃ h, h ≫ cutOutι I J = g) ↔ I.map g.appTop.hom = ⊥ ∧ J.map g.appTop.hom = ⊤ := by
  rw [exists_comp_cutOutι_iff, range_subset_idealBasicOpen_iff, Ideal.map_eq_bot_iff_le_ker]

/-- For `J = ⊤` the locally closed subscheme is the closed subscheme `V(I)`. -/
theorem isClosedImmersion_cutOutι_top : IsClosedImmersion (cutOutι I ⊤) := by
  have hrange : Set.range (cutOutι I ⊤).base =
      Set.range (Scheme.IdealSheafData.ofIdealTop I).subschemeι.base := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rintro _ ⟨x, rfl⟩
      have hx : x ∈ (Scheme.IdealSheafData.ofIdealTop I).subschemeι ⁻¹ᵁ
          X.idealBasicOpen (⊤ : Ideal Γ(X, ⊤)) := by
        rw [idealBasicOpen_top]; trivial
      exact ⟨⟨x, hx⟩, rfl⟩
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rw [hrange]
  exact (Scheme.IdealSheafData.ofIdealTop I).subschemeι.isClosedEmbedding.isClosed_range

/-- Over an affine scheme, the closed subscheme cut out by a finitely generated ideal is
locally of finite presentation. -/
theorem locallyOfFinitePresentation_subschemeι_ofIdealTop [IsAffine X] (hI : I.FG) :
    LocallyOfFinitePresentation (Scheme.IdealSheafData.ofIdealTop I).subschemeι := by
  have h := Scheme.IdealSheafData.ker_subschemeι_app (Scheme.IdealSheafData.ofIdealTop I)
    ⟨⊤, isAffineOpen_top X⟩
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal] at h
  have : IsAffine (Scheme.IdealSheafData.ofIdealTop I).subscheme :=
    isAffine_of_isAffineHom (Scheme.IdealSheafData.ofIdealTop I).subschemeι
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  have hsurj : Function.Surjective (Scheme.IdealSheafData.ofIdealTop I).subschemeι.appTop :=
    (Scheme.IdealSheafData.ofIdealTop I).subschemeι.app_surjective ⊤ (isAffineOpen_top X)
  have hker : (RingHom.ker (Scheme.IdealSheafData.ofIdealTop I).subschemeι.appTop.hom).FG := by
    change (RingHom.ker ((Scheme.IdealSheafData.ofIdealTop I).subschemeι.app ⊤).hom).FG
    rw [h]
    exact hI.map _
  exact RingHom.FinitePresentation.of_surjective _ hsurj hker

/-- Over an affine scheme, `V(I) ∩ D(J)` is locally of finite presentation over `X` as soon as
`I` is finitely generated. -/
theorem locallyOfFinitePresentation_cutOutι [IsAffine X] (hI : I.FG) :
    LocallyOfFinitePresentation (cutOutι I J) := by
  have := locallyOfFinitePresentation_subschemeι_ofIdealTop I hI
  unfold cutOutι; infer_instance

/-- For a finitely generated ideal `J` of the global sections of an affine scheme, the open
`D(J)` is quasi-compact. -/
theorem isCompact_idealBasicOpen [IsAffine X] (hJ : J.FG) :
    IsCompact (X.idealBasicOpen J : Set X) := by
  obtain ⟨s, rfl⟩ := hJ
  have heq : (X.idealBasicOpen (Ideal.span (s : Set Γ(X, ⊤))) : Set X) =
      ⋃ f ∈ s, (X.basicOpen f : Set X) := by
    change (X.zeroLocus (U := ⊤) (Ideal.span (s : Set Γ(X, ⊤)) : Set Γ(X, ⊤)))ᶜ = _
    rw [zeroLocus_span, zeroLocus_def, Set.compl_iInter₂]
    simp
  rw [heq]
  exact s.isCompact_biUnion fun f _ => isCompact_basicOpen X isCompact_univ f

/-- Over an affine scheme, `V(I) ∩ D(J)` is quasi-compact over `X` as soon as `J` is finitely
generated. -/
theorem quasiCompact_cutOutι [IsAffine X] (hJ : J.FG) : QuasiCompact (cutOutι I J) := by
  rw [quasiCompact_iff_compactSpace]
  exact isCompact_iff_compactSpace.mp <| QuasiCompact.isCompact_preimage
    (f := (Scheme.IdealSheafData.ofIdealTop I).subschemeι)
    _ (X.idealBasicOpen J).isOpen (isCompact_idealBasicOpen J hJ)

end AlgebraicGeometry.Scheme

end
