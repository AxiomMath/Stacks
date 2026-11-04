module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetUnion
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportProperties

/-!
# Proper support of an abelian sheaf on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type. An abelian sheaf on the small étale site of `X` has *support proper over `Y`* when its
support, which is a subset of the points of `X`, is closed and proper over `Y` in the sense of
Stacks 0CZD. This is the algebraic-space counterpart of `Stacks.Algebraization.HasProperSupport`
and the condition appearing throughout Stacks 0CZK.

Proper support propagates along containments of supports, because a closed subset of a closed
subset proper over the base is proper over the base (Stacks 0CZE) and a finite union of closed
subsets proper over the base is proper over the base (Stacks 0CZH). That is all clause (1) of
Stacks 0CZK needs, once the support of the sheaf in question is known to sit inside the union of
the two given supports and to be closed.

For a direct sum both facts are available with no further input: the support of a sheaf which
splits sectionwise into two summands is *exactly* the union of the supports of the summands, so
it is closed as soon as the two summands have closed support. The containment is read off the
sections, where the identity `τ = i₁ (p₁ τ) + i₂ (p₂ τ)` bounds the support of a section of the
sum by the supports of the two component sections; the reverse containment is the injectivity of
each inclusion on sections.

## Main definitions

* `AlgebraicGeometry.Space.HasProperSupport`: the support of an abelian sheaf on the small étale
  site of `X`, as a closed subset of the points of `X`, is proper over `Y`.

## Main results

* `AlgebraicGeometry.Space.hasProperSupport_of_subset` and
  `AlgebraicGeometry.Space.hasProperSupport_of_subset_union`: proper support passes to a sheaf
  with closed support contained in the support of one, or in the union of the supports of two,
  sheaves with proper support.
* `AlgebraicGeometry.Space.supportOfSheaf_eq_union_of_sectionwiseSplit`: the support of a
  sectionwise direct sum is the union of the supports of the two summands.
* `AlgebraicGeometry.Space.hasProperSupport_of_sectionwiseSplit`: **Stacks 0CZK**, the direct
  sum clause of part (1).

## Implementation notes

The support is `AlgebraicGeometry.Space.supportOfSheaf`, the support of Stacks 04KA, and the
topology on the point set is `AlgebraicGeometry.Space.pointTopology`, installed as a local
instance. Since the support of a module on an algebraic space is by definition the support of its
underlying abelian sheaf — this is how Stacks 07TZ is stated in
`AlgebraicGeometry.Space.isClosed_supportOfSheaf_of_isFiniteTypeOnSite` — stating everything for
abelian sheaves covers the modules of the source and asks for no quasi-coherence.

Closedness of the support is carried inside `HasProperSupport` as an existential witness rather
than as a separate hypothesis, as on the scheme side, because Stacks 0CZD is a condition on a
*closed* subset. For a module of finite type closedness is automatic by Stacks 07TZ; for a sheaf
produced by one of the remaining clauses of Stacks 0CZK part (1) it has to be supplied, and
establishing it from finite type of the given modules alone would be the finite type closure of
Properties of Spaces, Section 66.30 (Stacks 05VR), which no declaration in this repository
carries. The direct sum clause is free of that prerequisite precisely because for a direct sum
the containment of supports is an equality. The remaining clauses are in
`StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupportSerre`, which avoids the
prerequisite in the same way for an extension — there too the containment is an equality — and
for the image and the cokernel reduces to the quotient clause
`AlgebraicGeometry.Space.hasProperSupport_of_epi`, whose source is of finite type by
hypothesis.

A direct sum is presented by its two inclusions, its two projections and the three identities
they satisfy *on sections over each étale chart*, rather than as a categorical biproduct. The
identities on sections are what the proof consumes, and in this form the statement needs no
preadditive or biproduct instance on the category of abelian sheaves, and applies to a direct
sum of modules through the underlying abelian sheaves without any exactness input on the
forgetful functor.

## References

* [Stacks Project, Tag 0CZK](https://stacks.math.columbia.edu/tag/0CZK)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 0CZE](https://stacks.math.columbia.edu/tag/0CZE)
* [Stacks Project, Tag 0CZH](https://stacks.math.columbia.edu/tag/0CZH)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04KB](https://stacks.math.columbia.edu/tag/04KB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An abelian sheaf on the small étale site of `X` has *support proper over `Y`* when its
support is a closed subset of the points of `X` which is proper over `Y` in the sense of
Stacks 0CZD. -/
def HasProperSupport (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) : Prop :=
  ∃ hcl : IsClosed (supportOfSheaf B S hS X F),
    IsProperOver B S hS hX hY f hf (supportOfSheaf B S hS X F) hcl

/-- A sheaf whose support is closed and contained in the support of a sheaf with proper support
has itself proper support, by Stacks 0CZE. -/
theorem hasProperSupport_of_subset (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    {E F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}}
    (hEcl : IsClosed (supportOfSheaf B S hS X E))
    (hsub : supportOfSheaf B S hS X E ⊆ supportOfSheaf B S hS X F)
    (hF : HasProperSupport B S hS hX hY f hf F) :
    HasProperSupport B S hS hX hY f hf E := by
  obtain ⟨hFcl, hFproper⟩ := hF
  exact ⟨hEcl, isProperOver_of_subset B S hS hX hY f hf _ _ hEcl hFcl hsub hFproper⟩

/-- A sheaf whose support is closed and contained in the union of the supports of two sheaves
with proper support has itself proper support: the union of the two supports is proper over the
base by Stacks 0CZH, and the containment is Stacks 0CZE. -/
theorem hasProperSupport_of_subset_union (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    {E F G : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}}
    (hEcl : IsClosed (supportOfSheaf B S hS X E))
    (hsub : supportOfSheaf B S hS X E ⊆
      supportOfSheaf B S hS X F ∪ supportOfSheaf B S hS X G)
    (hF : HasProperSupport B S hS hX hY f hf F)
    (hG : HasProperSupport B S hS hX hY f hf G) :
    HasProperSupport B S hS hX hY f hf E := by
  obtain ⟨hFcl, hFproper⟩ := hF
  obtain ⟨hGcl, hGproper⟩ := hG
  let T : Bool → Set (points B S hS X) :=
    fun b => cond b (supportOfSheaf B S hS X F) (supportOfSheaf B S hS X G)
  have hT : ∀ b, IsClosed (T b) := Bool.rec hGcl hFcl
  have hTproper : ∀ b, IsProperOver B S hS hX hY f hf (T b) (hT b) := Bool.rec hGproper hFproper
  have hsub' : supportOfSheaf B S hS X E ⊆ ⋃ b, T b := by
    intro x hx
    rcases hsub hx with h | h
    · exact Set.mem_iUnion.2 ⟨true, h⟩
    · exact Set.mem_iUnion.2 ⟨false, h⟩
  exact ⟨hEcl, isProperOver_of_subset B S hS hX hY f hf _ _ hEcl
    (isClosed_iUnion_of_finite hT) hsub'
    (isProperOver_iUnion B S hS hX hY f hf T hT hTproper)⟩

/-- The support of an abelian sheaf which splits sectionwise as a direct sum of two abelian
sheaves is the union of the supports of the two summands.

A section of the sum is the sum of the images of its two components, so its support is contained
in the union of the supports of those components by Stacks 04KB, and the support of a sheaf is
the union of the images of the supports of its sections. Conversely each inclusion is injective
on sections, so neither summand's support exceeds the support of the sum. -/
theorem supportOfSheaf_eq_union_of_sectionwiseSplit (hX : IsAlgebraicSpace B S hS X)
    {E F G : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}}
    (i₁ : F ⟶ E) (i₂ : G ⟶ E) (p₁ : E ⟶ F) (p₂ : E ⟶ G)
    (hi₁ : ∀ (U : SmallEtale B S hS X) (σ : F.obj.obj (op U)),
      p₁.hom.app (op U) (i₁.hom.app (op U) σ) = σ)
    (hi₂ : ∀ (U : SmallEtale B S hS X) (σ : G.obj.obj (op U)),
      p₂.hom.app (op U) (i₂.hom.app (op U) σ) = σ)
    (htotal : ∀ (U : SmallEtale B S hS X) (τ : E.obj.obj (op U)),
      i₁.hom.app (op U) (p₁.hom.app (op U) τ) +
        i₂.hom.app (op U) (p₂.hom.app (op U) τ) = τ) :
    supportOfSheaf B S hS X E =
      supportOfSheaf B S hS X F ∪ supportOfSheaf B S hS X G := by
  have hmem : ∀ (H : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) U σ,
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U)) U.obj.hom ''
        supportOfSection B S hS X H U σ ⊆ supportOfSheaf B S hS X H := fun H U σ ↦ by
    rw [supportOfSheaf_eq_iUnion_image_supportOfSection B S hS X hX H]
    exact fun x hx ↦ Set.mem_iUnion₂.2 ⟨U, σ, hx⟩
  refine subset_antisymm ?_ ?_
  · rw [supportOfSheaf_eq_iUnion_image_supportOfSection B S hS X hX E]
    refine Set.iUnion₂_subset fun U τ ↦ ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ supportOfSection B S hS X E U
        (i₁.hom.app (op U) (p₁.hom.app (op U) τ) + i₂.hom.app (op U) (p₂.hom.app (op U) τ)) := by
      rwa [htotal U τ]
    rcases supportOfSection_add_subset B S hS X E U _ _ hy' with h | h
    · exact Or.inl (hmem F U _ ⟨y, supportOfSection_map_subset B S hS X i₁ U _ h, rfl⟩)
    · exact Or.inr (hmem G U _ ⟨y, supportOfSection_map_subset B S hS X i₂ U _ h, rfl⟩)
  · refine Set.union_subset
      (supportOfSheaf_subset_of_injective B S hS X hX i₁ fun U a b hab ↦ ?_)
      (supportOfSheaf_subset_of_injective B S hS X hX i₂ fun U a b hab ↦ ?_)
    · rw [← hi₁ U a, ← hi₁ U b, hab]
    · rw [← hi₂ U a, ← hi₂ U b, hab]

/-- A direct sum of two abelian sheaves on the small étale site of `X` whose supports are proper
over `Y` again has support proper over `Y`.

The support of the sum is the union of the two supports, so it is closed, and a finite union of
closed subsets proper over the base is proper over the base by Stacks 0CZH. This is the direct
sum clause of Stacks 0CZK part (1) at the level of abelian sheaves; the clause for modules is
`AlgebraicGeometry.Space.hasProperSupport_toSheaf_of_sectionwiseSplit`. -/
theorem hasProperSupport_of_sectionwiseSplit (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    {E F G : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}}
    (i₁ : F ⟶ E) (i₂ : G ⟶ E) (p₁ : E ⟶ F) (p₂ : E ⟶ G)
    (hi₁ : ∀ (U : SmallEtale B S hS X) (σ : F.obj.obj (op U)),
      p₁.hom.app (op U) (i₁.hom.app (op U) σ) = σ)
    (hi₂ : ∀ (U : SmallEtale B S hS X) (σ : G.obj.obj (op U)),
      p₂.hom.app (op U) (i₂.hom.app (op U) σ) = σ)
    (htotal : ∀ (U : SmallEtale B S hS X) (τ : E.obj.obj (op U)),
      i₁.hom.app (op U) (p₁.hom.app (op U) τ) +
        i₂.hom.app (op U) (p₂.hom.app (op U) τ) = τ)
    (hF : HasProperSupport B S hS hX hY f hf F)
    (hG : HasProperSupport B S hS hX hY f hf G) :
    HasProperSupport B S hS hX hY f hf E := by
  obtain ⟨hFcl, hFproper⟩ := hF
  obtain ⟨hGcl, hGproper⟩ := hG
  have heq := supportOfSheaf_eq_union_of_sectionwiseSplit B S hS hX i₁ i₂ p₁ p₂ hi₁ hi₂ htotal
  refine hasProperSupport_of_subset_union B S hS hX hY f hf ?_ heq.subset
    ⟨hFcl, hFproper⟩ ⟨hGcl, hGproper⟩
  rw [heq]
  exact hFcl.union hGcl

/-- **Stacks 0CZK, part (1), the direct sum clause.** A direct sum of two `𝒪_X`-modules whose
supports are proper over `Y` again has support proper over `Y`.

The support of a module is the support of its underlying abelian sheaf, and the two inclusions,
the two projections and the three identities they satisfy on sections carry over to the
underlying abelian sheaves unchanged, so this is
`AlgebraicGeometry.Space.hasProperSupport_of_sectionwiseSplit` read off the sections of the
modules. -/
@[stacks 0CZK "part (1), direct sums"]
theorem hasProperSupport_toSheaf_of_sectionwiseSplit (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    {P M N : Modules.{u, v} B S hS X hX}
    (i₁ : M ⟶ P) (i₂ : N ⟶ P) (p₁ : P ⟶ M) (p₂ : P ⟶ N)
    (hi₁ : ∀ (U : SmallEtale B S hS X) (σ : M.val.obj (op U)),
      p₁.val.app (op U) (i₁.val.app (op U) σ) = σ)
    (hi₂ : ∀ (U : SmallEtale B S hS X) (σ : N.val.obj (op U)),
      p₂.val.app (op U) (i₂.val.app (op U) σ) = σ)
    (htotal : ∀ (U : SmallEtale B S hS X) (τ : P.val.obj (op U)),
      i₁.val.app (op U) (p₁.val.app (op U) τ) +
        i₂.val.app (op U) (p₂.val.app (op U) τ) = τ)
    (hM : HasProperSupport B S hS hX hY f hf ((SheafOfModules.toSheaf _).obj M))
    (hN : HasProperSupport B S hS hX hY f hf ((SheafOfModules.toSheaf _).obj N)) :
    HasProperSupport B S hS hX hY f hf ((SheafOfModules.toSheaf _).obj P) :=
  hasProperSupport_of_sectionwiseSplit B S hS hX hY f hf
    ((SheafOfModules.toSheaf _).map i₁) ((SheafOfModules.toSheaf _).map i₂)
    ((SheafOfModules.toSheaf _).map p₁) ((SheafOfModules.toSheaf _).map p₂)
    hi₁ hi₂ htotal hM hN

end AlgebraicGeometry.Space

end
