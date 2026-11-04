module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveSheaves
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.BigSiteFpqcSheafCriterion
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Pullback
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.CoveringSieveMembership
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfASingletonUpToIso

/-!
# The Čech complex of a finite covering of a chosen big site and of its disjoint union

Let `S` be a scheme and let `B` be a chosen big `τ`-site over `S`. For a finite family
`{Uᵢ → U}` of morphisms of the site, the disjoint union `∐ Uᵢ` belongs to the site, and for an
abelian sheaf `F` on the site the Čech complex of `{Uᵢ → U}` is isomorphic to the Čech complex
of the one-member family `{∐ Uᵢ → U}`. This is [Stacks, Tag 03FI] (3) read on a chosen big
site, and it discharges the predicate `Stacks.Adequate.BigSite.CoproductCechComparison` under
which the library has been quoting it.

## Main results

* `AlgebraicGeometry.schemeSizeBelow_isClosedUnderFiniteCoproducts_of_aleph0_lt` — the schemes
  of size below an uncountable cardinal are closed under finite coproducts. No cofinality
  hypothesis is needed for a finite index type.
* `Stacks.Adequate.BigSite.finitaryExtensive_category` — the underlying category of a chosen
  big site is finitary extensive.
* `Stacks.Adequate.BigSite.extensiveTopology_le_topology` — finite disjoint unions cover their
  coproduct in the topology of a chosen big site, for each of the five topologies.
* `Stacks.Adequate.BigSite.preservesFiniteProducts_of_isSheaf` — a sheaf on a chosen big site
  carries finite coproducts of the site to products.
* `Stacks.Adequate.BigSite.coproductCechComparison` — **[Stacks, Tag 03FI] (3)** on a chosen big
  site: `Stacks.Adequate.BigSite.CoproductCechComparison` holds for every `𝒪`-module.

## Implementation notes

What the library carried of [Stacks, Tag 03FI] (3) is
`AlgebraicGeometry.isIso_cechComplexMap_coproductRefinement_over`, for an abelian sheaf on a
topology on *all* schemes over `S`, and the general
`Stacks.CechSite.isIso_cechComplexMap_of_preservesFiniteProducts` for a presheaf preserving
finite products on a finitary extensive category. The second applies on the site itself once
the site is finitary extensive and its sheaves preserve finite products, which is what is
proved here: the cutoff category of schemes is closed under finite coproducts and fibre
products, so the forgetful functor to schemes preserves both and reflects isomorphisms, and a
finite disjoint union in the site is carried to a disjoint union of schemes, whose inclusions
are open immersions and jointly surjective, hence a covering family for each of the five
topologies by `AlgebraicGeometry.sieve₀_mem_overTopology_of_coveringMorphismProperty`.

The predicate `Stacks.Adequate.BigSite.CoproductCechComparison` names the one-member family by
an arbitrary morphism `f : Y ⟶ X` of the site whose image in the schemes over `S` is the morphism
from the disjoint union of the image of the family. Such a `Y` is a coproduct of the family *in
the site*, the canonical functor to the schemes over `S` being fully faithful, so its
one-member family is isomorphic over `X` to that of the coproduct formed in the site, and
`Stacks.CechSite.isIso_cechComplexMap_singleton` compares the two.

## References

* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal

universe w u m

namespace AlgebraicGeometry

/-- **The schemes of size below an uncountable cardinal are closed under finite coproducts.**
The size of a finite coproduct is at most the larger of `ℵ₀` and the sizes of its summands, by
`AlgebraicGeometry.schemeSize_coproduct_le`. Unlike the countable case, Stacks 000R (2), no
hypothesis on the cofinality of the cardinal is needed. -/
public theorem schemeSizeBelow_isClosedUnderFiniteCoproducts_of_aleph0_lt {κ : Cardinal.{u}}
    (hκ : ℵ₀ < κ) : (schemeSizeBelow κ).IsClosedUnderFiniteCoproducts := by
  classical
  refine ObjectProperty.IsClosedUnderFiniteCoproducts.of_isClosedUnderColimitsOfShape.{u} ?_
  intro J _
  have := Fintype.ofFinite J
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro X ⟨F, hF⟩
  show (colimit F).size < κ
  rw [Scheme.size_congr (HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := F)))]
  refine (schemeSize_coproduct_le (fun j : J ↦ F.obj ⟨j⟩)
    (ℵ₀ ⊔ Finset.univ.sup fun j : J ↦ (F.obj ⟨j⟩).size) le_sup_left
    ((Cardinal.lt_aleph0_of_finite J).le.trans le_sup_left)
    fun j ↦ (Finset.le_sup (f := fun j : J ↦ (F.obj ⟨j⟩).size) (Finset.mem_univ j)).trans
      le_sup_right).trans_lt ?_
  exact sup_lt_iff.2 ⟨hκ, (Finset.sup_lt_iff (lt_of_le_of_lt bot_le (aleph0_pos.trans hκ))).2
    fun j _ ↦ hF ⟨j⟩⟩

end AlgebraicGeometry

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-- The forgetful functor from a chosen big site to schemes. -/
private abbrev BigSite.toScheme (B : BigSite τ S) : B.category ⥤ Scheme.{u} :=
  Over.forget (⟨S, B.base_mem⟩ : SchemeBelow B.cutoff) ⋙ schemeBelowInclusion B.cutoff

private theorem BigSite.isClosedUnderFiniteCoproducts (B : BigSite τ S) :
    (schemeSizeBelow B.cutoff).IsClosedUnderFiniteCoproducts :=
  schemeSizeBelow_isClosedUnderFiniteCoproducts_of_aleph0_lt B.aleph0_lt_cutoff

/-- The underlying category of a chosen big site has finite coproducts. -/
public theorem BigSite.hasFiniteCoproducts_category (B : BigSite τ S) :
    HasFiniteCoproducts B.category := by
  have := B.isClosedUnderFiniteCoproducts
  exact inferInstanceAs (HasFiniteCoproducts (Over (⟨S, B.base_mem⟩ : SchemeBelow B.cutoff)))

/-- The forgetful functor from a chosen big site to schemes preserves finite coproducts. -/
private theorem BigSite.preservesFiniteCoproducts_toScheme (B : BigSite τ S) (J : Type)
    [Finite J] : PreservesColimitsOfShape (Discrete J) B.toScheme := by
  have := B.isClosedUnderFiniteCoproducts
  have : HasFiniteCoproducts (SchemeBelow B.cutoff) := inferInstance
  infer_instance

/-- **The underlying category of a chosen big site is finitary extensive.** The forgetful functor
to schemes preserves fibre products and finite coproducts, the cutoff category being closed
under both, and it reflects isomorphisms; schemes form a finitary extensive category. -/
public theorem BigSite.finitaryExtensive_category (B : BigSite τ S) :
    FinitaryExtensive B.category := by
  have := B.hasFiniteCoproducts_category
  have := B.preservesFiniteCoproducts_toScheme WalkingPair
  have : PreservesLimitsOfShape WalkingCospan B.toScheme :=
    BigSite.preservesPullbacks_toOver_comp_forget B
  exact finitaryExtensive_of_preserves_and_reflects_isomorphism B.toScheme

/-- The injections of a finite coproduct cofan of schemes are open immersions and jointly
surjective. -/
private theorem isOpenImmersion_and_surjective_of_isColimit {α : Type} [Finite α]
    {Y : α → Scheme.{u}} (c : Cofan Y) (hc : IsColimit c) :
    (∀ a, IsOpenImmersion (c.inj a)) ∧ ∀ x : c.pt, ∃ a, x ∈ Set.range (c.inj a) := by
  let e : ∐ Y ≅ c.pt := (colimit.isColimit (Discrete.functor Y)).coconePointUniqueUpToIso hc
  have he : ∀ a, Sigma.ι Y a ≫ e.hom = c.inj a := fun a ↦
    (colimit.isColimit (Discrete.functor Y)).comp_coconePointUniqueUpToIso_hom hc ⟨a⟩
  refine ⟨fun a ↦ ?_, fun x ↦ ?_⟩
  · rw [← he a]
    infer_instance
  · obtain ⟨⟨a⟩, y, hy⟩ :=
      Concrete.isColimit_exists_rep _ (isColimitOfPreserves Scheme.forgetToTop hc) x
    exact ⟨a, y, hy⟩

/-- **Finite disjoint unions cover their coproduct in a chosen big site.** The extensive
topology on the underlying category of a chosen big site is coarser than the topology of the
site, for each of the five topologies: the injections of a finite coproduct are carried to open
immersions which are jointly surjective, hence to a covering family. -/
public theorem BigSite.extensiveTopology_le_topology (B : BigSite τ S) :
    letI := B.finitaryExtensive_category
    extensiveTopology B.category ≤ B.topology := by
  let := B.finitaryExtensive_category
  intro X R hR
  obtain ⟨α, hα, Y, π, ⟨hc⟩, hπ⟩ :=
    (extensiveTopology.mem_sieves_iff_contains_colimit_cofan R).mp hR
  let E : PreZeroHypercover.{0} X := ⟨α, Y, π⟩
  have hE : E.sieve₀ ≤ R := by
    rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
    rintro _ _ ⟨a⟩
    exact hπ a
  refine B.topology.superset_covering hE ?_
  have := B.preservesFiniteCoproducts_toScheme α
  obtain ⟨hopen, hsurj⟩ := isOpenImmersion_and_surjective_of_isColimit _
    (isColimitCofanMkObjOfIsColimit B.toScheme Y π hc)
  obtain ⟨𝒮, hS, rfl⟩ := B.exists_eq_ofAmbient
  exact sieve₀_mem_overTopology_of_coveringMorphismProperty τ 𝒮 S hS E
    (fun a ↦ isOpenImmersion_le_coveringMorphismProperty τ _ (hopen a)) hsurj

/-- **A sheaf on a chosen big site carries finite coproducts to products.** It is a sheaf for
the extensive topology, which is coarser than the topology of the site. -/
public theorem BigSite.preservesFiniteProducts_of_isSheaf (B : BigSite τ S) {A : Type*}
    [Category* A] (F : B.categoryᵒᵖ ⥤ A) (hF : Presheaf.IsSheaf B.topology F) :
    PreservesFiniteProducts F := by
  let := B.finitaryExtensive_category
  exact (Presheaf.isSheaf_iff_preservesFiniteProducts F).mp
    (Presheaf.IsSheaf.of_le B.extensiveTopology_le_topology hF)

/-- Two equal families with a common target have isomorphic members over the target. -/
private theorem exists_iso_of_eq {D : Type*} [Category* D] {T : D}
    {E E' : PreZeroHypercover.{w} T} (h : E = E') (i : E.I₀) :
    ∃ (j : E'.I₀) (e : E.X i ≅ E'.X j), e.hom ≫ E'.f j = E.f i := by
  subst h
  exact ⟨i, Iso.refl _, Category.id_comp _⟩

/-- A morphism `f : Y ⟶ X` of a chosen big site whose image in the schemes over `S` is the
morphism from the disjoint union of the image of a finite family `E` is isomorphic over `X` to
the morphism from the coproduct of `E` formed in the site. -/
private theorem nonempty_overIso_sigmaDesc (B : BigSite τ S) {X : B.category}
    (E : PreZeroHypercover.{0} X) [Finite E.I₀] {Y : B.category} (f : Y ⟶ X)
    (hf : (PreZeroHypercover.singleton.{0} f).map B.toOver =
      PreZeroHypercover.singleton.{0} (Sigma.desc (E.map B.toOver).f)) :
    letI := B.hasFiniteCoproducts_category
    Nonempty (Over.mk f ≅ Over.mk (Sigma.desc E.f)) := by
  let := B.hasFiniteCoproducts_category
  obtain ⟨_, e, he⟩ := exists_iso_of_eq hf PUnit.unit
  change B.toOver.obj Y ≅ ∐ (E.map B.toOver).X at e
  change e.hom ≫ Sigma.desc (E.map B.toOver).f = B.toOver.map f at he
  let ff := B.fullyFaithfulToOver
  let ι : ∀ i, E.X i ⟶ Y := fun i ↦ ff.preimage (Sigma.ι (E.map B.toOver).X i ≫ e.inv)
  have hι : ∀ i, B.toOver.map (ι i) = Sigma.ι (E.map B.toOver).X i ≫ e.inv := fun i ↦
    ff.map_preimage _
  have hmap : IsColimit (Cofan.mk (B.toOver.obj Y) fun i ↦ B.toOver.map (ι i) :
      Cofan fun i ↦ B.toOver.obj (E.X i)) :=
    IsColimit.ofIsoColimit (coproductIsCoproduct (E.map B.toOver).X)
      (Cofan.ext e.symm fun i ↦ (hι i).symm)
  have hc : IsColimit (Cofan.mk Y ι) := isColimitOfIsColimitCofanMkObj B.toOver E.X ι hmap
  let θ : Y ≅ ∐ E.X := hc.coconePointUniqueUpToIso (colimit.isColimit (Discrete.functor E.X))
  have hθ : ∀ i, ι i ≫ θ.hom = Sigma.ι E.X i := fun i ↦
    hc.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (Discrete.functor E.X)) ⟨i⟩
  refine ⟨Over.isoMk θ ?_⟩
  show θ.hom ≫ Sigma.desc E.f = f
  refine Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_
  show ι i ≫ θ.hom ≫ Sigma.desc E.f = ι i ≫ f
  rw [reassoc_of% (hθ i), Sigma.ι_desc]
  apply ff.map_injective
  have h2 : (Sigma.ι (E.map B.toOver).X i ≫ e.inv) ≫ B.toOver.map f = B.toOver.map (E.f i) :=
    (Category.assoc _ _ _).trans <|
      (congrArg (Sigma.ι (E.map B.toOver).X i ≫ ·)
        ((congrArg (e.inv ≫ ·) he.symm).trans (Iso.inv_hom_id_assoc e _))).trans
      (Sigma.ι_desc (E.map B.toOver).f i)
  rw [Functor.map_comp, hι]
  exact h2.symm

/-- **[Stacks, Tag 03FI] (3) on a chosen big site.** For an `𝒪`-module `F` on a chosen big
`τ`-site over `S`, a finite family `E` of morphisms of the site and a morphism `f` of the site
whose image in the schemes over `S` is the morphism from the disjoint union of the image of
`E`, the Čech cohomology of `E` with coefficients in the abelian sheaf underlying `F` is the
Čech cohomology of the one-member family `{f}`, in every degree. This discharges
`Stacks.Adequate.BigSite.CoproductCechComparison`. -/
@[stacks 03FI "part (3), on a chosen big site over a scheme: the Čech complex of a finite
family and of the one-member family of the morphism from its disjoint union agree, for an
abelian sheaf on the site"]
public theorem BigSite.coproductCechComparison (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf) :
    B.CoproductCechComparison.{u, m} F := by
  intro X E hfin Y f hf n
  let : HasFiniteLimits B.category := B.hasFiniteLimits_category
  let := B.finitaryExtensive_category
  let P : B.categoryᵒᵖ ⥤ AddCommGrpCat.{max u m} :=
    ((SheafOfModules.toSheaf B.structureSheaf).obj F).obj
  have : PreservesFiniteProducts P :=
    B.preservesFiniteProducts_of_isSheaf P
      ((SheafOfModules.toSheaf B.structureSheaf).obj F).property
  obtain ⟨ε⟩ := nonempty_overIso_sigmaDesc B E f hf
  have h₁ := Stacks.CechSite.isIso_cechComplexMap_of_preservesFiniteProducts E P
  have h₂ := Stacks.CechSite.isIso_cechComplexMap_singleton.{0} f (Sigma.desc E.f) ε P
  exact ⟨(HomologicalComplex.homologyFunctor _ _ n).mapIso
      (asIso (Stacks.CechSite.cechComplexMap E _
        (Stacks.CechSite.coproductRefinement E) P)).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (asIso (Stacks.CechSite.cechComplexMap _ _
        (Stacks.CechSite.singletonHomOver.{0} f (Sigma.desc E.f) ε) P))⟩

end Stacks.Adequate

end
