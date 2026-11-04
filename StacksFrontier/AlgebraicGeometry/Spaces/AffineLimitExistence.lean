module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleDescent

/-!
# The limit of an inverse system of algebraic spaces with affine transitions

A cofiltered inverse system of algebraic spaces over a scheme `S` whose transition morphisms
are affine has an algebraic-space limit, provided the index category is small enough for the
big fppf site: its object type and all of its morphism types have cardinality below the
cofinality of the site's size cutoff. This is the existence assertion of Stacks 07SF; its two
numbered parts are in `StacksFrontier/AlgebraicGeometry/Spaces/ApproximationSteps.lean`.

## Main results

* `AlgebraicGeometry.Space.relativelyRepresentable_limitπ`: every projection from the limit
  is relatively representable.
* `AlgebraicGeometry.Space.isAlgebraicSpace_limit`: the limit is an algebraic space over `S`.
* `AlgebraicGeometry.Scheme.size_le_of_isLimit_of_isAffine`: a limit of affine schemes of
  size at most `μ`, indexed by a category with `#J` objects, has size at most
  `max ℵ₀ (#J * μ)`.
* `AlgebraicGeometry.Space.relativelyRepresentable_limitπ_of_mono` and
  `AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_mono`: the same two conclusions from a
  cofinality-free cardinality hypothesis, at the cost of asking the transition morphisms to
  be monomorphisms.

## Implementation notes

*Why the obvious route is circular.* The three conditions of Stacks 025Y for `limit D` reduce
to relative representability of one projection `limit.π D i₀`: the sheaf condition is
`AlgebraicGeometry.Space.isSheaf_limit`, and the other two follow from Stacks 02WY,
`AlgebraicGeometry.IsAlgebraicSpace.of_relativelyRepresentable`. Affineness of the projection
is already available as `AlgebraicGeometry.Space.isAffineHom_limitπ`, but the implication
(2) ⇒ (1) of Stacks 03WG which turns it into relative representability —
`AlgebraicGeometry.Space.presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace` — needs the
*source* to be an algebraic space, which is what is being proved.

*The route taken.* Stacks 03WG is applied instead to the transition morphisms `D.map f`, where
algebraicity of both ends is a hypothesis. Over a test object `Z` and a morphism
`g : yoneda.obj Z ⟶ D.obj i₀` this represents each base change `D k ×_{D i₀} yoneda.obj Z`,
`k` ranging over the slice `Over i₀`, by an object of the site whose projection to `Z` is an
affine morphism of schemes. Representing objects being given only up to isomorphism, the
system of them is produced by lifting the system of base changes through the fully faithful
Yoneda embedding with `CategoryTheory.Functor.essImage.liftFunctor`, and the projections to
`Z` are assembled into a natural transformation to the constant functor, which is what makes
them a natural family. The limit of the lifted system then exists as a *scheme*, by
`AlgebraicGeometry.CofilteredLimit.hasLimit_of_isAffineHom_of_isCofiltered`, and
`AlgebraicGeometry.Space.isLimitPullbackLimitOverPost` identifies the presheaf it represents
with the base change of `limit.π D i₀` along `g`.

*The size bookkeeping.* What remains is that the limit scheme lies in the size-bounded site.
It is covered by the preimages of the affine opens of `Z` under the projection to `Z`, and by
Mathlib's `AlgebraicGeometry.isLimitOpensCone` each such preimage is the limit of the
corresponding preimages at the stages, which are affine because the stage projections are
affine morphisms. Those preimages are open subschemes of the stages, so a *single* bound —
the supremum `ν` of the sizes of the stages — serves for all of them, uniformly in the affine
open. That uniformity is the point: the affine opens of `Z` number fewer than the cutoff but
not necessarily fewer than its cofinality, so a bound depending on the affine open could not
be summed. Each preimage therefore has size at most `max ℵ₀ (#(Over k₀) * ν)`, where `k₀` is
the terminal object of `Over i₀`, and `ν` and `#(Over k₀)` are below the cutoff by the two
cardinality hypotheses on the index category, using that the cofinality of a cardinal is
regular.

## References

* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 02WY](https://stacks.math.columbia.edu/tag/02WY)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

/-! ### An explicit size bound for a limit of affine schemes -/

/-- A uniform size bound for a limit of affine schemes: if every stage has size at most `μ`,
the limit has size at most `max ℵ₀ (#J * μ)`.

This is `AlgebraicGeometry.Scheme.size_lt_of_isLimit_of_isAffine` with the bound exhibited
instead of being compared to a cutoff, which is what makes it usable for a family of limits
indexed by a type too large for the cofinality of that cutoff. -/
theorem Scheme.size_le_of_isLimit_of_isAffine {J : Type u} [Category.{u} J] [IsCofiltered J]
    (V : J ⥤ Scheme.{u}) (hV : ∀ j, IsAffine (V.obj j)) {μ : Cardinal.{u}}
    (hsize : ∀ j, (V.obj j).size ≤ μ) {c : Cone V} (hc : IsLimit c) :
    c.pt.size ≤ max ℵ₀ (#J * μ) := by
  have hpt : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have hΓ : ∀ j, #Γ(V.obj j, ⊤) ≤ μ := by
    intro j
    have := hV j
    refine le_trans ?_ (hsize j)
    rw [Scheme.size_of_isAffine (V.obj j)]
    exact le_max_right _ _
  have h₁ : #Γ(c.pt, ⊤) ≤ #(Σ j : J, Γ(V.obj j, ⊤)) := by
    refine Cardinal.mk_le_of_surjective (f := fun p : Σ j : J, Γ(V.obj j, ⊤) =>
      show Γ(c.pt, ⊤) from (c.π.app p.1).appTop p.2) ?_
    intro x
    obtain ⟨j, y, hy⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit V c hc x
    exact ⟨⟨j, y⟩, hy⟩
  have h₂ : #(Σ j : J, Γ(V.obj j, ⊤)) ≤ #J * μ := by
    rw [Cardinal.mk_sigma]
    exact (Cardinal.sum_le_mk_mul_iSup _).trans (mul_le_mul_right (ciSup_le' hΓ) _)
  rw [Scheme.size_of_isAffine c.pt]
  exact max_le_max le_rfl (h₁.trans h₂)

/-! ### The size of a slice of an index category -/

section SliceSize

variable {J : Type u} [Category.{u} J]

/-- The morphisms of a slice of a category inject into the morphisms of the category. -/
private theorem mk_slice_hom_le {i : J} (a b : Over i) : #(a ⟶ b) ≤ #(a.left ⟶ b.left) :=
  Cardinal.mk_le_of_injective (f := fun φ : a ⟶ b => φ.left)
    fun _ _ h => Over.OverMorphism.ext h

/-- With the index category small against the cofinality of the cutoff, the slice of the slice
over `i₀` is below the cutoff, and so is any supremum of sizes of site objects over the slice. -/
private theorem mk_over_slice_lt_cutoff_of_lt_cof (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hSize : #J < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : J, #(i ⟶ j) < B.cutoff.ord.cof) (i₀ : J) :
    #(Over (Over.mk (𝟙 i₀) : Over i₀)) < B.cutoff ∧
      ∀ W : Over i₀ → BigFppfOver B S hS,
        (⨆ k : Over i₀, ((BigFppfOver.toScheme B S hS).obj (W k)).size) < B.cutoff := by
  have hJ : #(Over i₀) < B.cutoff.ord.cof :=
    mk_over_lt B.aleph0_lt_cutoff_cof hSize hHomSize i₀
  have hJ' : #(Over (Over.mk (𝟙 i₀) : Over i₀)) < B.cutoff.ord.cof :=
    mk_over_lt B.aleph0_lt_cutoff_cof hJ
      (fun a b => (mk_slice_hom_le a b).trans_lt (hHomSize a.left b.left)) _
  exact ⟨hJ'.trans_le (Ordinal.cof_ord_le _),
    fun W => Cardinal.iSup_lt_of_lt_cof_ord hJ fun k => (W k).left.property⟩

/-- With few objects and morphisms in the index category, the slice of the slice over `i₀` is
below the cutoff. -/
private theorem mk_over_slice_lt_cutoff (B : BigFppfSite.{u}) {ν : Cardinal.{u}}
    (hSize : #J < B.cutoff) (hν : ν < B.cutoff) (hHomSize : ∀ i j : J, #(i ⟶ j) ≤ ν) (i₀ : J) :
    #(Over (Over.mk (𝟙 i₀) : Over i₀)) < B.cutoff :=
  mk_over_lt_of_mk_hom_le B.aleph0_lt_cutoff
    (mk_over_lt_of_mk_hom_le B.aleph0_lt_cutoff hSize hν hHomSize i₀) hν
    (fun a b => (mk_slice_hom_le a b).trans (hHomSize a.left b.left)) _

end SliceSize

/-! ### Limits in the big fppf site from containment of the limit scheme -/

section SiteDiagram

variable {J : Type u} [Category.{u} J] [IsCofiltered J]
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The size-bounded subcategory of schemes creates the limit of the diagram of schemes
underlying a diagram in the big fppf site of `S`, as soon as that limit exists and is
contained in the site. -/
@[instance_reducible]
private noncomputable def createsLimitInclusionOfContains (V : J ⥤ BigFppfOver B S hS)
    (hlim : HasLimit (underlyingDiagram V))
    (hsize : B.Contains (limit (underlyingDiagram V))) :
    CreatesLimit (V ⋙ BigFppfOver.forget B S hS) B.inclusion :=
  have _ : HasLimit (underlyingDiagram V) := hlim
  Limits.createsLimitFullSubcategoryInclusion _ hsize

/-- A cofiltered inverse system in the big fppf site of `S` whose underlying diagram of
schemes has a limit contained in the site has a limit in the site.

This is `AlgebraicGeometry.BigFppfOver.hasLimit_of_isAffine` with affineness of the stages
replaced by the two consequences of it which that proof uses: existence of the limit of the
underlying schemes, and its containment in the site. -/
private theorem hasLimit_of_contains (V : J ⥤ BigFppfOver B S hS)
    (hlim : HasLimit (underlyingDiagram V))
    (hsize : B.Contains (limit (underlyingDiagram V))) : HasLimit V := by
  have hconn : IsConnected J := IsCofiltered.isConnected J
  have _ : HasLimit (underlyingDiagram V) := hlim
  have _ := createsLimitInclusionOfContains V hlim hsize
  have : HasLimit (V ⋙ BigFppfOver.forget B S hS) := hasLimit_of_created _ B.inclusion
  exact hasLimit_of_created V (Over.forget (B.obj hS))

end SiteDiagram

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Limits

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **The size argument of the existence assertion of Stacks 07SF, isolated from the
construction it serves.** Let `W` be a lift, through the Yoneda embedding of the big fppf site
of `S`, of the diagram of base changes to a test object `Z` of the stages over `i₀` of a
cofiltered inverse system of algebraic spaces with affine transition morphisms. Then the
diagram of schemes underlying `W` has a limit, and that limit lies in the site if the slice of
the slice over `i₀` is small and the representing objects are bounded, or if the transition
morphisms are monomorphisms.

The stages of `W` carry a natural family of affine morphisms to `Z`, read off the isomorphism
with the diagram of base changes: the first conclusion is then Stacks 01YX for that family, and
the second is the cardinal argument described in the implementation notes of this file. The
family is built here, once, because the statement of Stacks 07SF over the chapter's standing
convention needs the first conclusion and not the second, while the statement over smallness
of the system needs both. -/
private theorem hasLimit_underlyingDiagram_and_limitInSite
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) (i₀ : I)
    (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ D.obj i₀)
    (W : Over i₀ ⥤ BigFppfOver B S hS)
    (hiso : W ⋙ yoneda ≅ (Over.post (X := i₀) D ⋙ Over.pullback g) ⋙
      Over.forget (yoneda.obj Z)) :
    HasLimit (underlyingDiagram W) ∧
      (#(Over (Over.mk (𝟙 i₀) : Over i₀)) < B.cutoff →
        (∀ (W' : Over i₀ → BigFppfOver B S hS) (q : ∀ k, W' k ⟶ Z),
          (∀ k : Over i₀, ∃ p : yoneda.obj (W' k) ⟶ D.obj k.left,
            IsPullback p (yoneda.map (q k)) (D.map k.hom) g) →
          (⨆ k : Over i₀, ((BigFppfOver.toScheme B S hS).obj (W' k)).size) < B.cutoff) →
        BigFppfOver.LimitInSite W) ∧
      ((∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (D.map f)) → BigFppfOver.LimitInSite W) := by
  -- Stacks 03WG, (2) ⇒ (1) for the transition morphisms: both ends are algebraic spaces
  have hrep : ∀ k : Over i₀, (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (D.map k.hom) := fun k =>
    (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS
      (hD k.left) (hD i₀) (hAffine k.hom)).2
  -- the diagram of base changes of the stages over `i₀` along `g`
  set E := (Over.post (X := i₀) D ⋙ Over.pullback g) ⋙ Over.forget (yoneda.obj Z)
  -- the structure morphisms of the diagram of base changes to the test object
  set πE : ∀ k : Over i₀, E.obj k ⟶ yoneda.obj Z :=
    fun k => ((Over.post (X := i₀) D ⋙ Over.pullback g).obj k).hom
  have hπEnat : ∀ {k l : Over i₀} (f : k ⟶ l), E.map f ≫ πE l = πE k := fun f =>
    Over.w ((Over.post (X := i₀) D ⋙ Over.pullback g).map f)
  -- they assemble into a natural transformation to the constant test object
  set σ : W ⋙ yoneda ⟶ (Functor.const (Over i₀)).obj (yoneda.obj Z) :=
    { app := fun k => hiso.hom.app k ≫ πE k
      naturality := fun k l f => by
        have h₁ : (W ⋙ yoneda).map f ≫ hiso.hom.app l = hiso.hom.app k ≫ E.map f :=
          hiso.hom.naturality f
        simp only [Functor.const_obj_map]
        rw [← Category.assoc, h₁, Category.assoc, hπEnat f]
        simp }
  -- the structure morphisms of the lifted system to the test object
  set ρ' : ∀ k : Over i₀, W.obj k ⟶ Z := fun k => yoneda.preimage (σ.app k)
  have hmapσ : ∀ k : Over i₀, yoneda.map (ρ' k) = σ.app k := fun k => yoneda.map_preimage _
  have hρ'nat : ∀ {k l : Over i₀} (f : k ⟶ l), W.map f ≫ ρ' l = ρ' k := by
    intro k l f
    refine yoneda.map_injective ?_
    have h := σ.naturality f
    simp only [Functor.const_obj_map, Functor.comp_map] at h
    rw [Functor.map_comp, hmapσ, hmapσ]
    exact h
  -- each stage of the lifted system represents the base change of its own stage of `D`
  set jk : ∀ k : Over i₀, yoneda.obj (W.obj k) ≅ Limits.pullback (D.map k.hom) g :=
    fun k => hiso.app k
  have hsnd : ∀ k : Over i₀, yoneda.map (ρ' k)
      = (jk k).hom ≫ Limits.pullback.snd (D.map k.hom) g := fun k => hmapσ k
  have hsq : ∀ k : Over i₀,
      IsPullback ((jk k).hom ≫ Limits.pullback.fst (D.map k.hom) g)
        (yoneda.map (ρ' k)) (D.map k.hom) g := fun k =>
    IsPullback.of_iso_pullback ⟨by rw [hsnd k]; simp [Limits.pullback.condition]⟩ (jk k) rfl
      (hsnd k).symm
  -- the underlying diagram of schemes, with its affine family of morphisms to the test object
  set Rd := underlyingDiagram W
  have hRdmap : ∀ {k l : Over i₀} (f : k ⟶ l),
      Rd.map f = (BigFppfOver.toScheme B S hS).map (W.map f) := fun _ => rfl
  set ρ : ∀ k : Over i₀, Rd.obj k ⟶ (BigFppfOver.toScheme B S hS).obj Z :=
    fun k => (BigFppfOver.toScheme B S hS).map (ρ' k)
  have hρnat : ∀ {k l : Over i₀} (f : k ⟶ l), Rd.map f ≫ ρ l = ρ k := by
    intro k l f
    show Rd.map f ≫ (BigFppfOver.toScheme B S hS).map (ρ' l)
      = (BigFppfOver.toScheme B S hS).map (ρ' k)
    rw [hRdmap f, ← Functor.map_comp, hρ'nat f]
  have hρaff : ∀ k : Over i₀, _root_.AlgebraicGeometry.IsAffineHom (ρ k) := fun k =>
    (hrep k).property g _ _ (hsq k)
  have hlimRd : HasLimit Rd := CofilteredLimit.hasLimit_of_isAffineHom_of_isCofiltered ρ hρnat
  set k₀ : Over i₀ := Over.mk (𝟙 i₀)
  have hlim : (limit Rd).size < B.cutoff → BigFppfOver.LimitInSite W := fun h c hc => by
    show c.pt.size < B.cutoff
    rwa [show c.pt.size = (limit Rd).size from
      Scheme.size_congr (hc.conePointUniqueUpToIso (limit.isLimit Rd))]
  refine ⟨hlimRd, fun hk₀ hν => hlim ?_, fun hmono => hlim ?_⟩
  · -- the limit scheme is covered by the preimages of the affine opens of the test object,
    -- and each of those is an affine limit of stages of bounded size
    set ν : Cardinal.{u} := ⨆ k : Over i₀, (Rd.obj k).size
    have hνlt : ν < B.cutoff :=
      hν (fun k => W.obj k) (fun k => ρ' k) fun k =>
        ⟨(jk k).hom ≫ Limits.pullback.fst (D.map k.hom) g, hsq k⟩
    have hpreim : ∀ U : ((BigFppfOver.toScheme B S hS).obj Z).affineOpens,
        (↑((limit.cone Rd).π.app k₀ ⁻¹ᵁ (ρ k₀ ⁻¹ᵁ U.1)) : Scheme.{u}).size
          ≤ max ℵ₀ (#(Over k₀) * ν) := by
      intro U
      have hstage : ∀ j : Over k₀, Rd.map j.hom ⁻¹ᵁ (ρ k₀ ⁻¹ᵁ U.1) = ρ j.left ⁻¹ᵁ U.1 := by
        intro j
        rw [← Scheme.Hom.comp_preimage, hρnat j.hom]
      have haff : ∀ j : Over k₀, IsAffine ((opensDiagram Rd k₀ (ρ k₀ ⁻¹ᵁ U.1)).obj j) := by
        intro j
        show IsAffineOpen (Rd.map j.hom ⁻¹ᵁ (ρ k₀ ⁻¹ᵁ U.1))
        rw [hstage j]
        exact U.2.preimage (ρ j.left)
      have hsize : ∀ j : Over k₀,
          ((opensDiagram Rd k₀ (ρ k₀ ⁻¹ᵁ U.1)).obj j).size ≤ ν := by
        intro j
        refine le_trans (Scheme.size_coe_opens_le (Rd.obj j.left)
          (Rd.map j.hom ⁻¹ᵁ (ρ k₀ ⁻¹ᵁ U.1))) ?_
        exact le_ciSup Cardinal.bddAbove_of_small j.left
      have hlim := Scheme.size_le_of_isLimit_of_isAffine _ haff hsize
        (isLimitOpensCone Rd (limit.cone Rd) (limit.isLimit Rd) k₀ (ρ k₀ ⁻¹ᵁ U.1))
      rwa [opensCone_pt] at hlim
    have hcov : (⨆ U : ((BigFppfOver.toScheme B S hS).obj Z).affineOpens,
        (limit.cone Rd).π.app k₀ ⁻¹ᵁ (ρ k₀ ⁻¹ᵁ U.1)) = ⊤ := by
      refine eq_top_iff.2 fun x _ => ?_
      have hx : (ρ k₀).base (((limit.cone Rd).π.app k₀).base x)
          ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj Z).Opens) := trivial
      rw [← iSup_affineOpens_eq_top] at hx
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩
    have _ : Nonempty ((BigFppfOver.toScheme B S hS).obj Z).affineOpens :=
      ⟨⟨⊥, isAffineOpen_bot _⟩⟩
    have hbound := Scheme.size_le_of_iSup_eq_top
      (fun U : ((BigFppfOver.toScheme B S hS).obj Z).affineOpens =>
        (limit.cone Rd).π.app k₀ ⁻¹ᵁ (ρ k₀ ⁻¹ᵁ U.1)) hcov
    refine lt_of_le_of_lt hbound (max_lt
      (((BigFppfOver.toScheme B S hS).obj Z).mk_affineOpens_le_size.trans_lt Z.left.property)
      ((ciSup_le' hpreim).trans_lt ?_))
    exact max_lt B.aleph0_lt_cutoff (Cardinal.mul_lt_of_lt B.aleph0_lt_cutoff.le hk₀ hνlt)
  · -- the limit scheme is a subobject of the test object, so one bound serves for it
    have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
      comp_preservesLimitsOfShape _ _
    have hmonoρ : ∀ k : Over i₀, Mono (ρ k) := by
      intro k
      have _ : Mono (D.map k.hom) := hmono k.hom
      have hpb : Mono (Limits.pullback.snd (D.map k.hom) g) := inferInstance
      have hy : Mono (yoneda.map (ρ' k)) := by
        rw [hsnd k]; exact mono_comp _ _
      have _ : Mono (ρ' k) := (yoneda (C := BigFppfOver B S hS)).mono_of_mono_map hy
      exact inferInstance
    have hmonolim : Mono ((limit.cone Rd).π.app k₀ ≫ ρ k₀) :=
      CofilteredLimit.mono_π_app_comp ρ hρnat hmonoρ (limit.isLimit Rd) k₀
    exact Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit
      ((limit.cone Rd).π.app k₀ ≫ ρ k₀) Z.left.property

/-- The projection from the limit is relatively representable as soon as the limit of every
lifted diagram of base changes lies in the site. -/
private theorem relativelyRepresentable_limitπ_of_limitInSite_aux (i₀ : I)
    (hconv : ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ D.obj i₀)
      (W : Over i₀ ⥤ BigFppfOver B S hS),
      (W ⋙ yoneda ≅ (Over.post (X := i₀) D ⋙ Over.pullback g) ⋙
        Over.forget (yoneda.obj Z)) → BigFppfOver.LimitInSite W)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) :
    yoneda.relativelyRepresentable (limit.π D i₀) := by
  intro Z g
  -- Stacks 03WG, (2) ⇒ (1) for the transition morphisms: both ends are algebraic spaces
  have hrep : ∀ k : Over i₀, (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (D.map k.hom) := fun k =>
    (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS
      (hD k.left) (hD i₀) (hAffine k.hom)).2
  -- the diagram of base changes of the stages over `i₀` along `g`
  set E := (Over.post (X := i₀) D ⋙ Over.pullback g) ⋙ Over.forget (yoneda.obj Z)
  have hbase := isLimitPullbackLimitOverPost B S hS D i₀ g
  have hess : ∀ k : Over i₀, (yoneda (C := BigFppfOver B S hS)).essImage (E.obj k) := fun k =>
    ⟨(hrep k).rep.pullback g, ⟨((hrep k).rep.isPullback g).isoPullback⟩⟩
  set W := Functor.essImage.liftFunctor E (yoneda (C := BigFppfOver B S hS)) hess
  have hiso : W ⋙ yoneda ≅ E :=
    Functor.essImage.liftFunctorCompIso E (yoneda (C := BigFppfOver B S hS)) hess
  have hlimRd : HasLimit (underlyingDiagram W) :=
    (hasLimit_underlyingDiagram_and_limitInSite B S hS D hD hAffine i₀ Z g W hiso).1
  have hcontain : B.Contains (limit (underlyingDiagram W)) :=
    hconv Z g W hiso (limit.cone (underlyingDiagram W)) (limit.isLimit (underlyingDiagram W))
  -- the limit therefore exists in the site, and Yoneda carries it to the base change
  have _ : HasLimit W := hasLimit_of_contains W hlimRd hcontain
  have hyoneda : IsLimit ((Cone.postcompose hiso.hom).obj (yoneda.mapCone (limit.cone W))) :=
    (IsLimit.postcomposeHomEquiv hiso (yoneda.mapCone (limit.cone W))).symm
      (isLimitOfPreserves yoneda (limit.isLimit W))
  have e : yoneda.obj (limit W) ≅ Limits.pullback (limit.π D i₀) g :=
    hyoneda.conePointUniqueUpToIso hbase
  refine ⟨limit W, yoneda.preimage (e.hom ≫ Limits.pullback.snd _ _),
    e.hom ≫ Limits.pullback.fst _ _, ?_⟩
  exact IsPullback.of_iso_pullback
    ⟨by rw [Functor.map_preimage]; simp [Limits.pullback.condition]⟩ e rfl
    (by rw [Functor.map_preimage])

/-- The limit is an algebraic space as soon as all its projections to the stages are relatively
representable. -/
private theorem isAlgebraicSpace_limit_of_relativelyRepresentable
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (h : ∀ i₀ : I, yoneda.relativelyRepresentable (limit.π D i₀)) :
    IsAlgebraicSpace B S hS (limit D) := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  exact IsAlgebraicSpace.of_relativelyRepresentable
    (isSheaf_limit B S hS D fun i => (hD i).isSheaf) (hD i₀) (h i₀)

/-- The common core of the two forms of relative representability of a projection from the
inverse limit below. The whole cardinality bookkeeping of the route enters through its last
two hypotheses: the slices of the slice over `i₀` are small enough for the site, and the
representing objects of the base changes of the stages over `i₀` along any one test morphism
have sizes with a supremum below the cutoff.

That second hypothesis is the irreducible one. It is a statement about an arbitrary family of
site objects which represent those base changes, because the representing objects are
produced by `CategoryTheory.Functor.essImage.liftFunctor` and so are not under the caller's
control. The two forms below discharge it in the two possible ways: from the regularity of
`cf(B.cutoff)` and the containment of every single representing object in the site, or from a
uniform bound on all of them at once. -/
private theorem relativelyRepresentable_limitπ_core
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) (i₀ : I)
    (hk₀ : #(Over (Over.mk (𝟙 i₀) : Over i₀)) < B.cutoff)
    (hν : ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ D.obj i₀)
      (W : Over i₀ → BigFppfOver B S hS) (q : ∀ k : Over i₀, W k ⟶ Z),
      (∀ k : Over i₀, ∃ p : yoneda.obj (W k) ⟶ D.obj k.left,
        IsPullback p (yoneda.map (q k)) (D.map k.hom) g) →
      (⨆ k : Over i₀, ((BigFppfOver.toScheme B S hS).obj (W k)).size) < B.cutoff) :
    yoneda.relativelyRepresentable (limit.π D i₀) :=
  relativelyRepresentable_limitπ_of_limitInSite_aux B S hS D i₀
    (fun Z g W hiso =>
      (hasLimit_underlyingDiagram_and_limitInSite B S hS D hD hAffine i₀ Z g W hiso).2.1 hk₀
        (hν Z g))
    hD hAffine

/-- Every projection from the inverse limit of a cofiltered inverse system of algebraic
spaces with affine transition morphisms is relatively representable, provided the index
category has fewer objects and fewer morphisms than the cofinality of the site's size cutoff.

That cofinality is what bounds the supremum of the sizes of the representing objects of the
base changes of the stages: each of them lies in the site, and fewer than `cf(B.cutoff)` of
them are being collected. -/
theorem relativelyRepresentable_limitπ (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) (i₀ : I) :
    yoneda.relativelyRepresentable (limit.π D i₀) :=
  have h := mk_over_slice_lt_cutoff_of_lt_cof B S hS hSize hHomSize i₀
  relativelyRepresentable_limitπ_core B S hS D hD hAffine i₀ h.1 fun _ _ W _ _ => h.2 W

/-- **Every projection from the inverse limit is relatively representable, with no
cofinality hypothesis.** The index category is only asked to have fewer objects than the
site's size cutoff, and all of its morphism types bounded by one cardinal below the cutoff;
in exchange the transition morphisms of the system are asked to be monomorphisms.

The trade is the one of `AlgebraicGeometry.Scheme.size_le_of_mono`: a base change of a
monomorphism is a monomorphism, so each representing object of a base change of a stage along
a test morphism `yoneda Z ⟶ D i₀` is the source of a monomorphism of schemes into `Z`, and
`max (2 ^ #Z) (size Z)` therefore bounds *all* of them at once. A supremum of a family
bounded by one cardinal below the cutoff is below the cutoff whatever the size of the family,
so the regularity of `cf(B.cutoff)` is not used anywhere.

This is incomparable with `AlgebraicGeometry.Space.relativelyRepresentable_limitπ`: neither
cardinality hypothesis implies the other, and this one restricts the system in addition. -/
theorem relativelyRepresentable_limitπ_of_mono {ν : Cardinal.{u}} (hSize : #I < B.cutoff)
    (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hMono : ∀ {i j : I} (f : i ⟶ j), Mono (D.map f)) (i₀ : I) :
    yoneda.relativelyRepresentable (limit.π D i₀) :=
  relativelyRepresentable_limitπ_core B S hS D hD hAffine i₀
    (mk_over_slice_lt_cutoff B hSize hν hHomSize i₀) (by
    intro Z g W q hpb
    refine (ciSup_le' fun k => ?_).trans_lt (monoSizeBound_lt_cutoff B S hS Z)
    obtain ⟨p, hp⟩ := hpb k
    exact size_le_monoSizeBound_of_mono B S hS (yoneda.map (q k))
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hp (hMono k.hom)))

/-- **Every projection from the inverse limit is relatively representable, for a system with
uniformly bounded base changes.** The index category is only asked to have fewer objects than
the site's size cutoff, and all of its morphism types bounded by one cardinal below the cutoff;
in exchange the base changes of the stages along any one test morphism are asked to be bounded
by one cardinal below the cutoff (`AlgebraicGeometry.Space.BaseChangeSizeBounded`).

This contains `AlgebraicGeometry.Space.relativelyRepresentable_limitπ_of_mono`, monomorphic
transitions giving such a bound by `AlgebraicGeometry.Space.baseChangeSizeBounded_of_mono`, and
it covers systems whose transitions are not monomorphisms, such as inverse systems of affine
étale neighbourhoods. -/
theorem relativelyRepresentable_limitπ_of_baseChangeSizeBounded {ν : Cardinal.{u}}
    (hSize : #I < B.cutoff) (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hB : BaseChangeSizeBounded B S hS D) (i₀ : I) :
    yoneda.relativelyRepresentable (limit.π D i₀) :=
  relativelyRepresentable_limitπ_core B S hS D hD hAffine i₀
    (mk_over_slice_lt_cutoff B hSize hν hHomSize i₀) (by
    intro Z g W q hpb
    obtain ⟨μ, hμ, hbound⟩ := hB i₀ Z g
    refine (ciSup_le' fun k => ?_).trans_lt hμ
    obtain ⟨p, hp⟩ := hpb k
    exact hbound k (W k) p (yoneda.map (q k)) hp)

/-- **The inverse limit is an algebraic space, for a system with uniformly bounded base
changes.** This is `AlgebraicGeometry.Space.isAlgebraicSpace_limit` with the cardinality bound
on the index category traded for a bound by the cutoff itself together with
`AlgebraicGeometry.Space.BaseChangeSizeBounded`, through
`AlgebraicGeometry.Space.relativelyRepresentable_limitπ_of_baseChangeSizeBounded`. -/
theorem isAlgebraicSpace_limit_of_baseChangeSizeBounded {ν : Cardinal.{u}}
    (hSize : #I < B.cutoff) (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hB : BaseChangeSizeBounded B S hS D) :
    IsAlgebraicSpace B S hS (limit D) :=
  isAlgebraicSpace_limit_of_relativelyRepresentable B S hS D hD fun i₀ =>
    relativelyRepresentable_limitπ_of_baseChangeSizeBounded B S hS D hSize hν hHomSize hD
      hAffine hB i₀

omit [IsCofiltered I] in
/-- **Uniformly bounded base changes pass to a subsystem.** Let `η : E ⟶ D` be a morphism of
inverse systems of presheaves with monomorphic components, `D` a system of algebraic spaces
with affine transitions whose base changes are uniformly bounded. Then the base changes of `E`
are uniformly bounded: a base change `E k ×_{E i₀} yoneda Z` maps monomorphically to the
corresponding base change of `D`, which is representable by an object of size at most `μ`, so
`max (2 ^ 2 ^ μ) μ` bounds it. -/
theorem baseChangeSizeBounded_of_natTrans_mono {E : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (η : E ⟶ D) (hη : ∀ i, Mono (η.app i)) (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hB : BaseChangeSizeBounded B S hS D) : BaseChangeSizeBounded B S hS E := by
  intro i₀ Z g
  obtain ⟨μ, hμ, hbound⟩ := hB i₀ Z (g ≫ η.app i₀)
  have h2 : (2 : Cardinal.{u}) ^ μ < B.cutoff := B.cutoff_isStrongPrelimit hμ
  have h22 : (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ μ < B.cutoff :=
    B.cutoff_isStrongPrelimit h2
  refine ⟨max ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ μ) μ, max_lt h22 hμ,
    fun k W p q hpq ↦ ?_⟩
  -- the corresponding base change of `D`, represented by an object of the site
  have hrep : yoneda.relativelyRepresentable (D.map k.hom) :=
    (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS
      (hD k.left) (hD i₀) (hAffine k.hom)).1
  let W' := hrep.pullback (g ≫ η.app i₀)
  have hW' : IsPullback (hrep.fst (g ≫ η.app i₀)) (yoneda.map (hrep.snd (g ≫ η.app i₀)))
      (D.map k.hom) (g ≫ η.app i₀) := hrep.isPullback (g ≫ η.app i₀)
  have hcomm : (p ≫ η.app k.left) ≫ D.map k.hom = q ≫ g ≫ η.app i₀ := by
    rw [Category.assoc, ← η.naturality, ← Category.assoc, hpq.w, Category.assoc]
  let m : yoneda.obj W ⟶ yoneda.obj W' := hW'.lift (p ≫ η.app k.left) q hcomm
  have hm : Mono m := by
    refine ⟨fun a b hab ↦ hpq.hom_ext ?_ ?_⟩
    · have h1 : a ≫ m ≫ hrep.fst (g ≫ η.app i₀) = b ≫ m ≫ hrep.fst (g ≫ η.app i₀) := by
        rw [← Category.assoc, hab, Category.assoc]
      simp only [m, IsPullback.lift_fst] at h1
      simpa only [← Category.assoc] using (cancel_mono (η.app k.left)).1
        (by simpa only [Category.assoc] using h1)
    · have h2 : a ≫ m ≫ yoneda.map (hrep.snd (g ≫ η.app i₀)) =
          b ≫ m ≫ yoneda.map (hrep.snd (g ≫ η.app i₀)) := by
        rw [← Category.assoc, hab, Category.assoc]
      simpa only [m, IsPullback.lift_snd] using h2
  have hW'size : ((BigFppfOver.toScheme B S hS).obj W').size ≤ μ :=
    hbound k W' _ _ hW'
  refine (size_le_monoSizeBound_of_mono B S hS m hm).trans (max_le_max ?_ hW'size)
  exact Cardinal.power_le_power_left two_ne_zero
    ((Scheme.mk_le_two_pow_size _).trans (Cardinal.power_le_power_left two_ne_zero hW'size))

omit [IsCofiltered I] in
/-- **The base change of a system of uniformly bounded objects of the site has uniformly bounded
base changes.** Let `T : I ⥤ BigFppfOver B S hS` be a system of objects of size at most `μ`,
and let `D` be a system of presheaves whose transition squares over the transitions
`yoneda (T i) ⟶ yoneda (T j)` are cartesian, for projections `π i : D i ⟶ yoneda (T i)`. Then
every base change `D k ×_{D i₀} yoneda Z` is `T k ×_{T i₀} Z`, of size at most `max μ (size Z)`.

This is the case of the base changes `X_{Tᵢ} = Tᵢ ×_Y X` of an inverse system of test schemes
`Tᵢ` over the target of a morphism `X ⟶ Y`, such as an inverse system of affine étale
neighbourhoods of a geometric point: its transitions are not monomorphisms, but its stages are
all étale over one of them and so of bounded size. -/
theorem baseChangeSizeBounded_of_isPullback (T : I ⥤ BigFppfOver B S hS)
    (π : ∀ i, D.obj i ⟶ yoneda.obj (T.obj i))
    (hsq : ∀ {i j : I} (f : i ⟶ j), IsPullback (D.map f) (π i) (π j) (yoneda.map (T.map f)))
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hT : ∀ i, ((BigFppfOver.toScheme B S hS).obj (T.obj i)).size ≤ μ) :
    BaseChangeSizeBounded B S hS D := by
  intro i₀ Z g
  refine ⟨max μ ((BigFppfOver.toScheme B S hS).obj Z).size, max_lt hμ Z.left.property,
    fun k W p q hpq ↦ ?_⟩
  -- `W` is the fibre product of `T k` and `Z` over `T i₀`
  have hW : IsPullback (p ≫ π k.left) q (yoneda.map (T.map k.hom)) (g ≫ π i₀) :=
    hpq.paste_horiz (hsq k.hom).flip
  have hW' : IsPullback (yoneda.map (yoneda.preimage (p ≫ π k.left)))
      (yoneda.map (yoneda.preimage q)) (yoneda.map (T.map k.hom))
      (yoneda.map (yoneda.preimage (g ≫ π i₀))) := by
    simpa only [Functor.map_preimage] using hW
  have hsite : IsPullback (yoneda.preimage (p ≫ π k.left)) (yoneda.preimage q) (T.map k.hom)
      (yoneda.preimage (g ≫ π i₀)) := IsPullback.of_map_of_faithful yoneda hW'
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    dsimp only [BigFppfOver.toScheme]
    infer_instance
  rw [Scheme.size_congr (hsite.map (BigFppfOver.toScheme B S hS)).isoPullback]
  exact (Scheme.size_pullback_le _ _).trans (max_le_max (hT k.left) le_rfl)

/-- **Stacks 07SF, existence.** The inverse limit of a cofiltered inverse system of algebraic
spaces over `S` with affine transition morphisms is an algebraic space over `S`, provided the
index category is small enough for the site: its object type and all of its morphism types
have cardinality below the cofinality of the site's size cutoff.

The limit is a sheaf by `AlgebraicGeometry.Space.isSheaf_limit`, and the remaining two
conditions of Stacks 025Y follow from Stacks 02WY applied to the projection to any one stage,
which is relatively representable by
`AlgebraicGeometry.Space.relativelyRepresentable_limitπ`. -/
@[stacks 07SF "existence"]
theorem isAlgebraicSpace_limit (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) :
    IsAlgebraicSpace B S hS (limit D) :=
  isAlgebraicSpace_limit_of_relativelyRepresentable B S hS D hD fun i₀ =>
    relativelyRepresentable_limitπ B S hS D hSize hHomSize hD hAffine i₀

/-- **The inverse limit is an algebraic space, with no cofinality hypothesis.** This is
`AlgebraicGeometry.Space.isAlgebraicSpace_limit` with the cardinality bound on the index
category traded for a bound by the cutoff itself together with monomorphic transition
morphisms, through
`AlgebraicGeometry.Space.relativelyRepresentable_limitπ_of_mono`. The two hypotheses are
incomparable, and `@[stacks 07SF]` stays on the form carrying the source's own one. -/
theorem isAlgebraicSpace_limit_of_mono {ν : Cardinal.{u}} (hSize : #I < B.cutoff)
    (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hMono : ∀ {i j : I} (f : i ⟶ j), Mono (D.map f)) :
    IsAlgebraicSpace B S hS (limit D) :=
  isAlgebraicSpace_limit_of_relativelyRepresentable B S hS D hD fun i₀ =>
    relativelyRepresentable_limitπ_of_mono B S hS D hSize hν hHomSize hD hAffine hMono i₀

end Limits

end Space

end AlgebraicGeometry

namespace AlgebraicGeometry

/-! ### An explicit size bound for a limit of affine schemes -/

/-! ### The size of a slice of an index category -/

section SliceSize

variable {J : Type u} [Category.{u} J]

end SliceSize

/-! ### Limits in the big fppf site from containment of the limit scheme -/

section SiteDiagram

variable {J : Type u} [Category.{u} J] [IsCofiltered J]
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

end SiteDiagram

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Limits

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks 07SF, relative representability of the projections under the chapter's standing
convention.** Every projection from the inverse limit of a cofiltered inverse system of
algebraic spaces with affine transition morphisms is relatively representable, as soon as every
limit of a diagram of base changes that the proof forms lies in the big fppf site.

This is `AlgebraicGeometry.Space.relativelyRepresentable_limitπ_of_isSiteSmall` with the condition
on the
index replaced by the convention of Section 70.2, that every ring considered has its spectrum
in the site, read for the schemes this proof forms: the limits of the diagrams of base changes,
to a test object `Z` of the site, of the stages over one stage `i₀`. That is
`AlgebraicGeometry.BigFppfOver.LimitInSite` of a lift of such a diagram through the Yoneda
embedding. Smallness of the system implies it, by the cardinal argument described in the
implementation notes of this file, and is strictly stronger. -/
theorem relativelyRepresentable_limitπ_of_limitInSite (i₀ : I)
    (hconv : ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ D.obj i₀)
      (W : Over i₀ ⥤ BigFppfOver B S hS),
      (W ⋙ yoneda ≅ (Over.post (X := i₀) D ⋙ Over.pullback g) ⋙
        Over.forget (yoneda.obj Z)) → BigFppfOver.LimitInSite W)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) :
    yoneda.relativelyRepresentable (limit.π D i₀) :=
  relativelyRepresentable_limitπ_of_limitInSite_aux B S hS D i₀ hconv hD hAffine

/-- Every projection from the inverse limit of a cofiltered inverse system of algebraic
spaces with affine transition morphisms is relatively representable. -/
theorem relativelyRepresentable_limitπ_of_isSiteSmall (hb : IsSiteSmall B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) (i₀ : I) :
    yoneda.relativelyRepresentable (limit.π D i₀) :=
  relativelyRepresentable_limitπ_of_limitInSite B S hS D i₀
    (fun Z g W hiso => by
      have h := hasLimit_underlyingDiagram_and_limitInSite B S hS D hD hAffine i₀ Z g W hiso
      rcases hb with ⟨hSize, hHomSize⟩ | hmono
      · have h' := mk_over_slice_lt_cutoff_of_lt_cof B S hS hSize hHomSize i₀
        exact h.2.1 h'.1 fun W' _ _ => h'.2 W'
      · exact h.2.2 hmono)
    hD hAffine

/-- **Stacks 07SF, existence.** The inverse limit of a cofiltered inverse system of algebraic
spaces over `S` with affine transition morphisms is an algebraic space over `S`, provided the
system is small for the site: either its index category is small compared with the cofinality
of the site's size cutoff, its object type and all of its morphism types, or its transition
morphisms are monomorphisms. See `AlgebraicGeometry.Space.IsSiteSmall`.

The limit is a sheaf by `AlgebraicGeometry.Space.isSheaf_limit`, and the remaining two
conditions of Stacks 025Y follow from Stacks 02WY applied to the projection to any one stage,
which is relatively representable by
`AlgebraicGeometry.Space.relativelyRepresentable_limitπ_of_isSiteSmall`. -/
@[stacks 07SF "existence"]
theorem isAlgebraicSpace_limit_of_isSiteSmall (hb : IsSiteSmall B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) :
    IsAlgebraicSpace B S hS (limit D) :=
  isAlgebraicSpace_limit_of_relativelyRepresentable B S hS D hD fun i₀ =>
    relativelyRepresentable_limitπ_of_isSiteSmall B S hS D hb hD hAffine i₀

/-- **Stacks 07SF, existence, under the chapter's standing convention.** The inverse limit of a
cofiltered inverse system of algebraic spaces over `S` with affine transition morphisms is an
algebraic space over `S`.

This is the faithful statement of the tag. The source states no condition on the index: it
assumes only the convention of Section 70.2 that every ring considered has its spectrum in the
big fppf site, which for this proof says that each limit of a diagram of base changes, to a
test object of the site, of the stages over one stage lies in the site. That is
`AlgebraicGeometry.BigFppfOver.LimitInSite` of a lift of such a diagram through the Yoneda
embedding. The proof is the one of `AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_isSiteSmall`,
which
proves the same conclusion from the strictly stronger `AlgebraicGeometry.Space.IsSiteSmall`,
with the appeal to smallness replaced by the convention at the stage, test object and point in
hand. -/
@[stacks 07SF "existence"]
theorem isAlgebraicSpace_limit_of_limitInSite
    (hconv : ∀ (i : I) (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ D.obj i)
      (W : Over i ⥤ BigFppfOver B S hS),
      (W ⋙ yoneda ≅ (Over.post (X := i) D ⋙ Over.pullback g) ⋙
        Over.forget (yoneda.obj Z)) → BigFppfOver.LimitInSite W)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) :
    IsAlgebraicSpace B S hS (limit D) :=
  isAlgebraicSpace_limit_of_relativelyRepresentable B S hS D hD fun i₀ =>
    relativelyRepresentable_limitπ_of_limitInSite B S hS D i₀ (hconv i₀) hD hAffine

end Limits

end Space

end AlgebraicGeometry

end
