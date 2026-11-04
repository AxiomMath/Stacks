module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcTopology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# The Zariski topology on `LC_qc` and the comparison morphisms

On the site `LC_qc` of Hausdorff, locally quasi-compact spaces there is a second topology: the
coverings of `X` are the qc coverings `{Xᵢ → X}` all of whose members are open immersions. This
is the site `LC_Zar`. A family of open immersions is a qc covering exactly when it is jointly
surjective, so `LC_Zar` is the topology of open coverings. Its coverings are qc coverings, so the
identity functor `LC_Zar → LC_qc` is continuous, and it defines a morphism of sites
`ε : LC_qc → LC_Zar`: the direct image of a qc sheaf is the same presheaf viewed as a Zariski
sheaf, and the inverse image of a Zariski sheaf is its qc sheafification, which is exact.

For an object `X`, the open subsets of `X` form the small site `X_Zar`. It has fibre products
(intersections) and a final object (`X` itself), and the functor `X_Zar → LC_Zar/X`,
`U ↦ (U → X)`, commutes with them; it is continuous and induces the morphism of topoi
`π_X : Sh(LC_Zar/X) → Sh(X_Zar)`, and `Sh(X_Zar)` is by definition the category `Sh(X)` of
sheaves on the space `X`.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcSiteComparisonMorphism`: the morphism of
  topoi `Sh(LC_qc) → Sh(LC_Zar)` of the morphism of sites `ε`.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.ofArrows_mem_zariskiPrecoverage_iff`: the
  coverings of `LC_Zar` are the coverings of `LC_qc` by open immersions.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.isContinuous_id_zariskiTopology_qc`: the
  identity functor `LC_Zar → LC_qc` is continuous.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcSiteInverseImage_preservesFiniteColimits`
  and `qcSiteInverseImage_preservesFiniteLimits`: the inverse image of `ε` is exact.
* `Stacks.Topology.opens_hasPullbacks_and_hasTerminal`: `X_Zar` has fibre products and a final
  object.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.opensToSlice_preservesFiniteLimits`: the
  functor `X_Zar → LC_Zar/X` commutes with finite limits.
* `Stacks.Topology.sheaf_opens_grothendieckTopology_eq`: `Sh(X_Zar) = Sh(X)`.

## Implementation notes

The underlying category of `LC_qc` has objects in `Type (u + 1)` and morphisms in `Type u`, so
it is not a small category and `CategoryTheory.Functor.IsMorphismOfSites` (which is stated for
small categories) does not apply to it verbatim. What Stacks 00X1 asks of the identity functor —
continuity, and exactness of the induced functor `u_s` on sheaves of sets — is stated here
directly: `u_s` is `qcSiteInverseImage`, i.e. qc sheafification of the underlying presheaf,
because the presheaf pullback along the identity functor is the identity.

## References

* [Stacks Project, Section 21.31 (Tag 09WY)](https://stacks.math.columbia.edu/tag/09WY)
* [Stacks Project, Tag 09X2](https://stacks.math.columbia.edu/tag/09X2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace Stacks.Topology

universe u w t

/-- **`X_Zar` has fibre products and a final object.** The category of open subsets of a
topological space has fibre products (intersections) and a final object (the whole space). -/
@[stacks 09WY "X_Zar has fibre products and a final object"]
theorem opens_hasPullbacks_and_hasTerminal (X : TopCat.{u}) :
    HasPullbacks (Opens X) ∧ HasTerminal (Opens X) :=
  ⟨inferInstance, inferInstance⟩

/-- **`Sh(X_Zar) = Sh(X)`.** The sheaves on the small site `X_Zar` of open subsets of `X` are by
definition the sheaves on the topological space `X`. -/
@[stacks 09WY "the equality Sh(X_Zar) = Sh(X)"]
theorem sheaf_opens_grothendieckTopology_eq (X : TopCat.{u}) (A : Type*) [Category* A] :
    Sheaf (Opens.grothendieckTopology X) A = TopCat.Sheaf A X :=
  rfl

namespace LocallyQuasiCompactZariskiSituation

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- **The coverings of `LC_Zar`.** A family of morphisms of `LC_qc` is a covering of `LC_Zar`
exactly when it is a covering of `LC_qc` all of whose members are open immersions. A family of
open immersions is a qc covering iff it is jointly surjective: a qc covering is jointly
surjective, and an open covering is a qc covering because the target is locally quasi-compact. -/
@[stacks 09WY "the site LC_Zar: the coverings of LC_qc by open immersions"]
theorem ofArrows_mem_zariskiPrecoverage_iff {ι : Type*} {T : S.category}
    {Y : ι → S.category} (f : ∀ i, Y i ⟶ T) :
    Presieve.ofArrows Y f ∈ S.zariskiPrecoverage T ↔
      Presieve.ofArrows Y f ∈ S.qcSite.pretopology T ∧
        ∀ i, IsOpenEmbedding (f i : (Y i).obj → T.obj) := by
  have hiff : Presieve.ofArrows Y f ∈ S.qcSite.pretopology T ↔
      IsQcCovering (fun i => (f i : (Y i).obj → T.obj)) :=
    S.qcSite.isCovering_iff_isQcCovering (X := T) ⟨ι, Y, f⟩
  rw [hiff]
  show _ ∧ _ ↔ _
  rw [Presieve.map_ofArrows, Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff,
    MorphismProperty.ofArrows_mem_precoverage]
  simp only [Functor.comp_obj, Functor.comp_map]
  constructor
  · rintro ⟨hsurj, hopen⟩
    have hopen' : ∀ i, IsOpenEmbedding (f i : (Y i).obj → T.obj) := fun i =>
      (TopCat.isOpenEmbedding_iff _).1 (hopen i)
    have _ : LocallyCompactSpace T.obj := inferInstanceAs (LocallyCompactSpace T.obj.obj)
    exact ⟨IsQcCovering.of_isOpenEmbedding hopen' hsurj, hopen'⟩
  · rintro ⟨hqc, hopen⟩
    refine ⟨fun x => ?_, fun i => (TopCat.isOpenEmbedding_iff _).2 (hopen i)⟩
    obtain ⟨s, K, -, hx⟩ := hqc x
    obtain ⟨_, ⟨i, rfl⟩, _, ⟨-, rfl⟩, y, -, hy⟩ := mem_of_mem_nhds hx
    exact ⟨i, y, hy⟩

/-- **The identity functor `LC_Zar → LC_qc` is continuous**, because every covering of `LC_Zar`
is a covering of `LC_qc`. -/
@[stacks 09WY "the identity functor LC_Zar → LC_qc is continuous"]
theorem isContinuous_id_zariskiTopology_qc :
    (𝟭 S.category).IsContinuous S.zariskiTopology S.qcSite.grothendieckTopology :=
  Functor.isContinuous_id_of_le _ _ S.zariskiTopology_le_qc

/-- The underlying category of `LC_qc` is essentially small in any universe containing the
universe of the spaces. -/
theorem essentiallySmall_category : EssentiallySmall.{max u t} S.category := by
  have h : EssentiallySmall.{u} S.category :=
    S.qcSite.boundedSubcategory.category_essentiallySmall
  rw [essentiallySmall_iff] at h ⊢
  exact ⟨small_lift.{u + 1, t, u} _ (hα := h.1), inferInstance⟩

/-- Presheaves of sets on `LC_qc` can be sheafified, for coefficients in any universe containing
the universe of the spaces. -/
instance hasSheafify_qcTopology : HasSheafify S.qcSite.grothendieckTopology (Type (max u t)) :=
  have := essentiallySmall_category.{u, w, t} S
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max u t} _ _

/-- Direct image of the morphism of sites `ε : LC_qc → LC_Zar`: a qc sheaf, viewed as a Zariski
sheaf. -/
def qcSiteDirectImage :
    Sheaf S.qcSite.grothendieckTopology (Type (max u t)) ⥤
      Sheaf S.zariskiTopology (Type (max u t)) :=
  ObjectProperty.ιOfLE fun _ hF ↦ hF.of_le S.zariskiTopology_le_qc

/-- The direct image of `ε` is pushforward along the identity functor `LC_Zar → LC_qc`. -/
theorem qcSiteDirectImage_eq :
    letI := S.isContinuous_id_zariskiTopology_qc
    qcSiteDirectImage.{u, w, t} S = (𝟭 S.category).sheafPushforwardContinuous
      (Type (max u t)) S.zariskiTopology S.qcSite.grothendieckTopology :=
  rfl

/-- Inverse image of the morphism of sites `ε : LC_qc → LC_Zar`: qc sheafification of the
underlying presheaf of a Zariski sheaf. -/
noncomputable def qcSiteInverseImage :
    Sheaf S.zariskiTopology (Type (max u t)) ⥤
      Sheaf S.qcSite.grothendieckTopology (Type (max u t)) :=
  sheafToPresheaf S.zariskiTopology (Type (max u t)) ⋙
    presheafToSheaf S.qcSite.grothendieckTopology (Type (max u t))

/-- The adjunction `ε⁻¹ ⊣ ε_*`. -/
noncomputable def qcSiteComparisonAdjunction :
    qcSiteInverseImage.{u, w, t} S ⊣ qcSiteDirectImage.{u, w, t} S :=
  (sheafificationAdjunction S.qcSite.grothendieckTopology (Type (max u t))).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf S.zariskiTopology (Type (max u t)))
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

/-- The inverse image of `ε` is left exact, since qc sheafification is. -/
instance qcSiteInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (qcSiteInverseImage.{u, w, t} S) :=
  comp_preservesFiniteLimits _ _

/-- The inverse image of `ε` is right exact, being a left adjoint. -/
instance qcSiteInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (qcSiteInverseImage.{u, w, t} S) :=
  have : (qcSiteInverseImage.{u, w, t} S).IsLeftAdjoint :=
    (qcSiteComparisonAdjunction.{u, w, t} S).isLeftAdjoint
  inferInstance

/-- **The morphism of sites `ε : LC_qc → LC_Zar`.** The identity functor `LC_Zar → LC_qc` is
continuous (`isContinuous_id_zariskiTopology_qc`) and its induced functor on sheaves of sets,
qc sheafification `qcSiteInverseImage`, is exact (`qcSiteInverseImage_preservesFiniteLimits`,
`qcSiteInverseImage_preservesFiniteColimits`); so it defines a morphism of sites, whose morphism
of topoi `Sh(LC_qc) → Sh(LC_Zar)` is this one. -/
@[stacks 09WY "the morphism of sites ε : LC_qc → LC_Zar"]
noncomputable def qcSiteComparisonMorphism :
    MorphismOfTopoi
      (Sheaf S.qcSite.grothendieckTopology (Type (max u t)))
      (Sheaf S.zariskiTopology (Type (max u t))) where
  pushforward := qcSiteDirectImage.{u, w, t} S
  inverseImage := qcSiteInverseImage.{u, w, t} S
  adj := qcSiteComparisonAdjunction.{u, w, t} S
  preservesFiniteLimits := inferInstance

/-- **The functor `X_Zar → LC_Zar/X` commutes with fibre products and the final object.** The
functor `U ↦ (U → X)` is representably flat, so it preserves all finite limits; in particular it
carries intersections of opens to fibre products and `X` to the final object `id : X → X`. -/
@[stacks 09WY "the functor X_Zar → LC_Zar/X commutes with fibre products and final object"]
theorem opensToSlice_preservesFiniteLimits (X : S.category) :
    PreservesFiniteLimits (S.opensToSlice X).1 :=
  have := S.opensToSlice_representablyFlat X
  preservesFiniteLimits_of_flat _

end LocallyQuasiCompactZariskiSituation

end Stacks.Topology
