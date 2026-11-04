module

public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.ResidueFieldMapIsIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.AbsoluteWeakNormalAffine
public import StacksFrontier.AlgebraicGeometry.Seminormalization.CandidateCategory

/-!
# The initial seminormalization candidate over an affine scheme

A seminormalization candidate over a scheme `X` is a universal homeomorphism onto `X` which
induces an isomorphism on every residue field. An initial object of the category of such
candidates is reduced, because the closed immersion of its reduction is again a candidate and
initiality forces that closed immersion to be an isomorphism.

When the base is affine the initial candidate is affine as well, and its ring of sections is
seminormal: adjoining a square-and-cube root produces another candidate — the square-cube
extension is a universal homeomorphism inducing isomorphisms on residue fields — so initiality
supplies the root. Conversely a candidate whose ring of sections is seminormal receives an
isomorphism from the initial candidate: the comparison map is injective because its source is
reduced, and it is surjective because a proper subring extension which is a universal
homeomorphism on spectra *and induces isomorphisms on residue fields* has a square-and-cube
special element, which seminormality forces to lie in the subring already. This last point is
where the seminormal case differs from the absolutely weakly normal one: the prime-power
alternative of Stacks Tag 0CNC is excluded by the residue field condition, so only the
square-and-cube alternative of Stacks Tag 0CNB survives.

## Main results

* `AlgebraicGeometry.exists_section_of_isInitial_seminormalizationCategory`: initiality turns a
  candidate over the initial candidate into a retraction.
* `AlgebraicGeometry.isReduced_of_isInitial_seminormalizationCategory`: an initial
  seminormalization candidate is reduced.
* `AlgebraicGeometry.isSeminormalRing_of_isInitial_seminormalizationCategory`: over an affine
  base the sections of the initial seminormalization candidate form a seminormal ring.
* `AlgebraicGeometry.isIso_of_isInitial_seminormalizationCategory`: over an affine base the
  canonical morphism from the initial seminormalization candidate to another candidate is an
  isomorphism as soon as the target has seminormal sections.

## Implementation notes

The ring-theoretic input shared with the absolutely weakly normal case — that the comparison
map is injective, and that the inclusion of the range of a ring map is again a universal
homeomorphism on spectra — is taken from
`StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.AbsoluteWeakNormalAffine`, as is the
criterion `AlgebraicGeometry.isSeminormalRing_of_sections` for the sections of an affine scheme
with enough sections of candidates.

Residue fields of a point of an affine scheme and of the corresponding point of the spectrum of
its sections are compared through `AlgebraicGeometry.Scheme.isoSpec`, whose naturality turns the
morphism of spectra of the comparison map into the comparison map itself conjugated by
isomorphisms. Each such transport is stated for *all* points at once before being used, so that
instance search never has to match a point of `Spec Γ(X, ⊤)` against a point of
`Spec (CommRingCat.of Γ(X, ⊤))`.

## References

* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
* [Stacks Project, Tag 0CNB](https://stacks.math.columbia.edu/tag/0CNB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {I : SeminormalizationCategory X}

/-- Initiality turns a seminormalization candidate over the source of the initial
seminormalization candidate into a retraction: the initial candidate maps back, and the
composite is the identity. -/
theorem exists_section_of_isInitial_seminormalizationCategory (hI : IsInitial I)
    {Z : Scheme.{u}} (h : Z ⟶ I.obj.left) (hh : UniversalHomeomorphism h)
    (hres : ∀ z : Z, IsIso (h.residueFieldMap z)) :
    ∃ s : I.obj.left ⟶ Z, s ≫ h = 𝟙 I.obj.left := by
  let T : SeminormalizationCategory X :=
    ⟨Over.mk (h ≫ I.obj.hom), IsSeminormalizationCandidate.comp I.property h hh hres⟩
  let k : T ⟶ I := ObjectProperty.homMk (Over.homMk h rfl)
  exact ⟨(hI.to T).hom.left,
    congrArg (fun m : I ⟶ I => m.hom.left) (hI.hom_ext (hI.to T ≫ k) (𝟙 I))⟩

/-- An initial object of the category of seminormalization candidates over a scheme is
reduced. -/
theorem isReduced_of_isInitial_seminormalizationCategory (hI : IsInitial I) :
    IsReduced I.obj.left := by
  obtain ⟨s, hs⟩ := exists_section_of_isInitial_seminormalizationCategory hI
    I.obj.left.reductionι (universalHomeomorphism_nilradical_subschemeι I.obj.left)
    fun z => (ConcreteCategory.isIso_iff_bijective _).mpr
      (I.obj.left.reductionι.bijective_residueFieldMap z)
  have hrs : I.obj.left.reductionι ≫ s = 𝟙 I.obj.left.reduction :=
    (cancel_mono I.obj.left.reductionι).mp (by
      rw [Category.assoc, hs, Category.comp_id, Category.id_comp])
  have : IsIso I.obj.left.reductionι := ⟨s, hrs, hs⟩
  exact isReduced_of_isOpenImmersion (inv I.obj.left.reductionι)

/-- **Stacks Project, Tag 0EUS.** Over an affine base the ring of sections of the initial
seminormalization candidate is seminormal. -/
theorem isSeminormalRing_of_isInitial_seminormalizationCategory [IsAffine X] (hI : IsInitial I) :
    IsSeminormalRing Γ(I.obj.left, ⊤) := by
  have : IsAffine I.obj.left := I.property.isAffine
  have : IsReduced I.obj.left := isReduced_of_isInitial_seminormalizationCategory hI
  exact isSeminormalRing_of_sections
    fun {Z} h hh hres => exists_section_of_isInitial_seminormalizationCategory hI h hh hres

/-- A ring map out of a seminormal ring whose morphism of spectra is a universal homeomorphism
inducing isomorphisms on all residue fields is bijective: injectivity is dominance, and an
element outside the image would be a square-and-cube special element of Stacks Tag 0CNB for the
image subring, hence already a square and a cube in the source. -/
private theorem bijective_of_universalHomeomorphism_of_isSeminormalRing
    {S R : Type u} [CommRing S] [CommRing R] [_root_.IsReduced R] (ψ : S →+* R)
    (hψ : UniversalHomeomorphism (Scheme.Spec.map (CommRingCat.ofHom ψ).op))
    (hres : ∀ x : Spec (CommRingCat.of R),
      IsIso ((Scheme.Spec.map (CommRingCat.ofHom ψ).op).residueFieldMap x))
    (hS : IsSeminormalRing S) : Function.Bijective ψ := by
  have : _root_.IsReduced S := seminormalRing_isReduced hS
  have hinj : Function.Injective ψ := injective_of_universalHomeomorphism_specMap ψ hψ
  refine ⟨hinj, ?_⟩
  have hCsub : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (ψ.range : Subring R).subtype).op) :=
    universalHomeomorphism_specMap_range_subtype ψ hinj hψ
  have hCres : ∀ x : Spec (CommRingCat.of R),
      IsIso ((Scheme.Spec.map
        (CommRingCat.ofHom (ψ.range : Subring R).subtype).op).residueFieldMap x) := by
    obtain ⟨e, hfactor⟩ := exists_specMap_range_subtype_iso ψ hinj
    have hsub : Scheme.Spec.map (CommRingCat.ofHom (ψ.range : Subring R).subtype).op =
        Scheme.Spec.map (CommRingCat.ofHom ψ).op ≫ e.inv := by
      rw [← hfactor, Category.assoc, e.hom_inv_id]
      simp
    intro x
    rw [hsub, Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' (residueFieldMap_isIso_of_isIso e.inv _) (hres x)
  intro b
  by_contra hb
  have hCtop : (ψ.range : Subring R) ≠ ⊤ := fun htop => hb (RingHom.range_eq_top.mp htop b)
  obtain ⟨c, hc, hc₂, hc₃⟩ :=
    exists_not_mem_and_sq_mem_and_cube_mem_of_universalHomeomorphism_of_residueFieldMap_isIso
      (ψ.range : Subring R) hCres hCtop
  obtain ⟨x, hx⟩ := RingHom.mem_range.mp hc₂
  obtain ⟨y, hy⟩ := RingHom.mem_range.mp hc₃
  have hxy : x ^ 3 = y ^ 2 := hinj <| by rw [map_pow, map_pow, hx, hy]; ring
  obtain ⟨a, ha, -⟩ := hS.existsUnique_of_cube_eq_square hxy
  refine hc (RingHom.mem_range.2 ⟨a, ?_⟩)
  refine Stacks.RingTheory.Seminormal.eq_of_sq_eq_of_cube_eq ?_ ?_
  · rw [← map_pow, ← ha.1, hx]
  · rw [← map_pow, ← ha.2, hy]

/-- **Stacks Project, Tag 0EUS.** Over an affine base the canonical morphism from the initial
seminormalization candidate to another candidate is an isomorphism as soon as the target has
seminormal sections. -/
theorem isIso_of_isInitial_seminormalizationCategory [IsAffine X] (hI : IsInitial I)
    (T : SeminormalizationCategory X) (hT : IsSeminormalRing Γ(T.obj.left, ⊤)) :
    IsIso ((hI.to T).hom.left) := by
  have : IsAffine I.obj.left := I.property.isAffine
  have : IsAffine T.obj.left := T.property.isAffine
  have : IsReduced I.obj.left := isReduced_of_isInitial_seminormalizationCategory hI
  have : _root_.IsReduced Γ(I.obj.left, ⊤) := inferInstance
  have hfU : UniversalHomeomorphism ((hI.to T).hom.left) :=
    SeminormalizationCategory.universalHomeomorphism_hom_left (hI.to T)
  have hfres : ∀ z, IsIso (((hI.to T).hom.left).residueFieldMap z) :=
    SeminormalizationCategory.isIso_residueFieldMap_hom_left (hI.to T)
  have hSpec : UniversalHomeomorphism (Spec.map ((hI.to T).hom.left).appTop) := by
    rw [universalHomeomorphism_iff] at hfU ⊢
    exact ((MorphismProperty.universally (topologically @IsHomeomorph)).arrow_mk_iso_iff
      (arrowIsoSpecΓOfIsAffine ((hI.to T).hom.left))).mp hfU
  have hfac : Spec.map ((hI.to T).hom.left).appTop =
      I.obj.left.isoSpec.inv ≫ (hI.to T).hom.left ≫ T.obj.left.isoSpec.hom := by
    rw [← Category.assoc, ← Scheme.isoSpec_inv_naturality, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hinvres : ∀ w : Spec Γ(I.obj.left, ⊤), IsIso (I.obj.left.isoSpec.inv.residueFieldMap w) :=
    fun w => inferInstance
  have hhomres : ∀ w : T.obj.left, IsIso (T.obj.left.isoSpec.hom.residueFieldMap w) :=
    fun w => inferInstance
  have hresSpec : ∀ w : Spec Γ(I.obj.left, ⊤),
      IsIso ((Spec.map ((hI.to T).hom.left).appTop).residueFieldMap w) := by
    intro w
    rw [hfac, Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' (IsIso.comp_isIso' (hhomres _) (hfres _)) (hinvres _)
  rw [← MorphismProperty.isomorphisms.iff,
    (MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (arrowIsoSpecΓOfIsAffine ((hI.to T).hom.left)),
    MorphismProperty.isomorphisms.iff, isIso_SpecMap_iff]
  refine bijective_of_universalHomeomorphism_of_isSeminormalRing
    ((hI.to T).hom.left).appTop.hom ?_ (fun x => hresSpec x) hT
  rw [CommRingCat.ofHom_hom]
  exact hSpec

end AlgebraicGeometry

end
