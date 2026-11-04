module

public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings

/-!
# Representability on the big fppf site of a scheme

A sheaf on the big fppf category over `S` admitting a jointly surjective family of relatively
representable open immersions from representable presheaves is representable, provided the
representing scheme can be glued inside the site.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.mk`: a scheme over `S` contained in the big fppf site, as an
  object of the big fppf category over `S`.
* `AlgebraicGeometry.BigFppfOver.homMk`: a scheme morphism over `S`, as a morphism of the big
  fppf category over `S`.
* `AlgebraicGeometry.HasZariskiGluing`: every fppf sheaf over `S` with a Zariski covering by
  representable open subfunctors is the presheaf represented by a scheme glued from the charts.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_of_openCover`: a scheme with an open covering by
  schemes contained in a big fppf site, indexed by a type smaller than the cofinality of the
  cutoff, is itself contained in the site.
* `AlgebraicGeometry.BigFppfSite.ofArrows_mem_topology_of_isOpenImmersion` and
  `AlgebraicGeometry.BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion`: a jointly
  surjective family of open immersions generates a covering sieve of the fppf topology of the
  big fppf site and of its slice over `S` respectively.
* `AlgebraicGeometry.isRepresentable_of_zariskiCover`: assuming
  `AlgebraicGeometry.HasZariskiGluing`, an fppf sheaf over `S` with a Zariski covering by
  representable open subfunctors, indexed by a type smaller than the cofinality of the cutoff,
  is representable.

## References

* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 02YY](https://stacks.math.columbia.edu/tag/02YY)
* [Stacks Project, Tag 03WX](https://stacks.math.columbia.edu/tag/03WX)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-! ### The size cutoff: a glued scheme stays in the site -/

/-- The open cover of `Y` given by a jointly surjective family of open immersions. -/
private def openCoverOfJointlySurjective {Y : Scheme.{u}} {ι : Type v} {X : ι → Scheme.{u}}
    (g : ∀ i, X i ⟶ Y) [∀ i, IsOpenImmersion (g i)]
    (hcov : ∀ y : Y, ∃ i, y ∈ Set.range (g i)) : Y.OpenCover.{v} where
  I₀ := ι
  X := X
  f := g
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨hcov, fun i => inferInstance⟩

/-- The size of the target of a jointly surjective family of open immersions is bounded by the
maximum of the cardinality of the index type and the supremum of the sizes of the sources. -/
private lemma size_le_of_jointly_surjective {Y : Scheme.{u}} {ι : Type u} [Nonempty ι]
    {X : ι → Scheme.{u}} (g : ∀ i, X i ⟶ Y) [∀ i, IsOpenImmersion (g i)]
    (hcov : ∀ y : Y, ∃ i, y ∈ Set.range (g i)) :
    Y.size ≤ max #ι (⨆ i, (X i).size) := by
  refine (Scheme.size_le_of_iSup_eq_top (fun i => (g i).opensRange)
    (openCoverOfJointlySurjective g hcov).iSup_opensRange).trans
    (max_le (le_max_left _ _) (ciSup_le' fun i => ?_))
  rw [← Scheme.size_congr (g i).isoOpensRange]
  exact (le_ciSup Cardinal.bddAbove_of_small i).trans (le_max_right _ _)

/-- An open subscheme of a scheme contained in a big fppf site is again contained in it. -/
theorem BigFppfSite.contains_coe_opens (B : BigFppfSite.{u}) {X : Scheme.{u}}
    (hX : B.Contains X) (U : X.Opens) : B.Contains (↑U : Scheme.{u}) :=
  (Scheme.size_coe_opens_le X U).trans_lt hX

/-- The source of an open immersion into a scheme contained in a big fppf site is contained
in that site. -/
theorem BigFppfSite.contains_of_isOpenImmersion (B : BigFppfSite.{u}) {U X : Scheme.{u}}
    (f : U ⟶ X) [IsOpenImmersion f] (hX : B.Contains X) : B.Contains U :=
  Scheme.size_lt_of_isOpenImmersion f hX

/-- A scheme covered by the images of open immersions from schemes contained in a big fppf
site is itself contained in that site, provided the index type is smaller than the
cofinality of the site's cutoff. -/
theorem BigFppfSite.contains_of_openCover (B : BigFppfSite.{u}) {Y : Scheme.{u}}
    {ι : Type u} [Nonempty ι] (hι : #ι < B.cutoff.ord.cof) {X : ι → Scheme.{u}}
    (g : ∀ i, X i ⟶ Y) [∀ i, IsOpenImmersion (g i)]
    (hcov : ∀ y : Y, ∃ i, y ∈ Set.range (g i)) (hX : ∀ i, B.Contains (X i)) :
    B.Contains Y :=
  (size_le_of_jointly_surjective g hcov).trans_lt
    (max_lt (hι.trans_le (Ordinal.cof_ord_le _)) (Cardinal.iSup_lt_of_lt_cof_ord hι hX))

/-- A scheme covered by the images of open immersions from schemes of uniformly bounded
size is contained in a big fppf site as soon as the bound and the cardinality of the index
type are below the site's cutoff. -/
theorem BigFppfSite.contains_of_openCover_of_size_le (B : BigFppfSite.{u})
    {Y : Scheme.{u}} {ι : Type u} [Nonempty ι] {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hι : #ι ≤ μ) {X : ι → Scheme.{u}} (g : ∀ i, X i ⟶ Y)
    [∀ i, IsOpenImmersion (g i)] (hcov : ∀ y : Y, ∃ i, y ∈ Set.range (g i))
    (hX : ∀ i, (X i).size ≤ μ) : B.Contains Y :=
  (size_le_of_jointly_surjective g hcov).trans_lt
    (max_lt (hι.trans_lt hμ) ((ciSup_le' hX).trans_lt hμ))

/-! ### The topology: a Zariski covering is an fppf covering -/

/-- A jointly surjective family of open immersions in the underlying category of a big fppf
site generates a covering sieve of its fppf topology. -/
theorem BigFppfSite.ofArrows_mem_topology_of_isOpenImmersion (B : BigFppfSite.{u})
    {T : B.Schemes} {ι : Type v} {X : ι → B.Schemes} (f : ∀ i, X i ⟶ T)
    (hf : ∀ i, IsOpenImmersion (B.inclusion.map (f i)))
    (hcov : ∀ x : B.inclusion.obj T, ∃ i, x ∈ Set.range (B.inclusion.map (f i))) :
    Sieve.ofArrows X f ∈ B.topology T := by
  have := hf
  let U := openCoverOfJointlySurjective (fun i => B.inclusion.map (f i)) hcov
  obtain ⟨V, hV, htaut⟩ := exists_isCovering_tautologicallyEquivalent_openCover B T U
  refine B.topology.superset_covering ?_ (Precoverage.generate_mem_toGrothendieck ⟨V, rfl, hV⟩)
  rw [Sieve.generate_le_iff]
  rintro Z g ⟨j⟩
  obtain ⟨β, hβ⟩ := htaut.2
  obtain ⟨e, he⟩ := hβ j
  refine ⟨X (β j), B.inclusion.preimage
    (show B.inclusion.obj (V.X j) ⟶ B.inclusion.obj (X (β j)) from e.hom), f (β j), ⟨β j⟩,
    B.inclusion.map_injective ?_⟩
  rw [Functor.map_comp, B.inclusion.map_preimage]
  exact he

/-- A jointly surjective family of open immersions in the big fppf category over `S`
generates a covering sieve of `AlgebraicGeometry.BigFppfOver.topology`. -/
theorem BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {T : BigFppfOver B S hS} {ι : Type v}
    {X : ι → BigFppfOver B S hS} (f : ∀ i, X i ⟶ T)
    (hf : ∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (f i)))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj T,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (f i))) :
    Sieve.ofArrows X f ∈ BigFppfOver.topology B S hS T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact B.ofArrows_mem_topology_of_isOpenImmersion (fun i => (f i).left) hf hcov

/-! ### The slice: objects and morphisms of the site are schemes and morphisms over `S` -/

section Slice

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A scheme contained in a big fppf site, together with a morphism to `S`, regarded as an
object of the big fppf category over `S`. -/
def BigFppfOver.mk {Y : Scheme.{u}} (hY : B.Contains Y) (p : Y ⟶ S) : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (X := B.obj hY) (Y := B.obj hS) p)

/-- The underlying scheme of `BigFppfOver.mk B S hS hY p` is `Y`. -/
lemma BigFppfOver.toScheme_obj_mk {Y : Scheme.{u}} (hY : B.Contains Y) (p : Y ⟶ S) :
    (BigFppfOver.toScheme B S hS).obj (BigFppfOver.mk B S hS hY p) = Y :=
  rfl

/-- A scheme morphism over `S` into a scheme contained in a big fppf site, regarded as a
morphism of the big fppf category over `S`. -/
def BigFppfOver.homMk {Y : Scheme.{u}} (hY : B.Contains Y) (p : Y ⟶ S)
    {T : BigFppfOver B S hS} (h : (BigFppfOver.toScheme B S hS).obj T ⟶ Y)
    (w : h ≫ p = B.inclusion.map T.hom) : T ⟶ BigFppfOver.mk B S hS hY p :=
  Over.homMk (ObjectProperty.homMk h) (by apply ObjectProperty.hom_ext; exact w)

/-- The underlying scheme morphism of `BigFppfOver.homMk B S hS hY p h w` is `h`. -/
lemma BigFppfOver.toScheme_map_homMk {Y : Scheme.{u}} (hY : B.Contains Y) (p : Y ⟶ S)
    {T : BigFppfOver B S hS} (h : (BigFppfOver.toScheme B S hS).obj T ⟶ Y)
    (w : h ≫ p = B.inclusion.map T.hom) :
    (BigFppfOver.toScheme B S hS).map (BigFppfOver.homMk B S hS hY p h w) = h :=
  rfl

/-- A morphism of the big fppf category over `S` is determined by the underlying morphism
of schemes. -/
theorem BigFppfOver.map_toScheme_injective {T T' : BigFppfOver B S hS} :
    Function.Injective fun a : T ⟶ T' => (BigFppfOver.toScheme B S hS).map a :=
  fun _ _ h => (BigFppfOver.toScheme B S hS).map_injective h

end Slice

/-! ### Representability of sheaves with a Zariski covering by representables -/

section Representability

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every sheaf `F` for the fppf topology of the big fppf category over `S` with a Zariski
covering by representable open subfunctors — relatively representable open immersions
`f i : yoneda.obj (X i) ⟶ F` whose coproduct maps locally onto `F` — is glued from the `X i`:
there are a scheme `Y` over `S` and open immersions `g i` from the charts into `Y`, compatible
with the structure morphisms and jointly covering `Y`, such that whenever `Y` is contained in
the site, `F` is isomorphic to the presheaf `Y` represents. -/
def HasZariskiGluing : Prop :=
  ∀ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) F →
    ∀ {ι : Type u} (X : ι → BigFppfOver B S hS) (f : ∀ i, yoneda.obj (X i) ⟶ F),
      (∀ i, Space.IsOpenImmersion B S hS (f i)) →
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f) →
      ∃ (Y : Scheme.{u}) (p : Y ⟶ S)
        (g : ∀ i, (BigFppfOver.toScheme B S hS).obj (X i) ⟶ Y),
        (∀ i, IsOpenImmersion (g i)) ∧
        (∀ i, g i ≫ p = B.inclusion.map (X i).hom) ∧
        (∀ y : Y, ∃ i, y ∈ Set.range (g i)) ∧
        ∀ hY : B.Contains Y, Nonempty (F ≅ yoneda.obj (BigFppfOver.mk B S hS hY p))

/-- Assuming `AlgebraicGeometry.HasZariskiGluing`, a sheaf `F` for the fppf topology of the
big fppf category over `S` which admits a Zariski covering by representable open subfunctors,
indexed by a type smaller than the cofinality of the site's cutoff, is representable. -/
theorem isRepresentable_of_zariskiCover (hglue : HasZariskiGluing B S hS)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {ι : Type u} [Nonempty ι] (hι : #ι < B.cutoff.ord.cof)
    (X : ι → BigFppfOver B S hS) (f : ∀ i, yoneda.obj (X i) ⟶ F)
    (hf : ∀ i, Space.IsOpenImmersion B S hS (f i))
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f)) :
    F.IsRepresentable := by
  obtain ⟨Y, p, g, hg, -, hcov, hiso⟩ := hglue F hF X f hf hsurj
  have := hg
  exact Functor.IsRepresentable.mk'
    (hiso (B.contains_of_openCover hι g hcov fun i => (X i).left.property)).some.symm

end Representability

end AlgebraicGeometry

end
