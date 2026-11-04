module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientKernelPair0265

/-!
# The relation of an étale equivalence relation on an affine object belongs to the site

A big fppf site is a full subcategory of schemes cut out by a size cutoff, so a construction
only stays inside it once the sizes are controlled. For an étale equivalence relation `j` from
`R` to `U ×_S U` with `U` an object of the site whose underlying scheme is affine, the scheme
`R` is *not* given as an object of the site: a pre-relation binds `R` as an arbitrary
`S`-scheme. This file shows that it is nevertheless an object of the site, and packages `R`
together with its two étale surjective maps to `U` as data inside the site.

The bound does not come from the étale maps `R ⟶ U`. It comes from monicity of `j`, which is
automatic for an equivalence relation, together with affineness of `U`: the composite of
`j` with the comparison from the fibre product over `S` to the absolute product is a
monomorphism into an affine scheme, and
`AlgebraicGeometry.BigFppfSite.contains_of_mono_of_isSeparated`
bounds the size of the source of a monomorphism whose target is separated and in the site.

## Main definitions

* `Stacks.Groupoids.PreRelation.siteObj` is the relation scheme as an object of the big fppf
  site over `S`, and `Stacks.Groupoids.PreRelation.siteSource` and
  `Stacks.Groupoids.PreRelation.siteTarget` are its source and target maps there.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_of_mono_of_isSeparated`: the source of a monomorphism
  whose target is separated and belongs to a big fppf site belongs to that site.
* `Stacks.Groupoids.PreRelation.contains_left_of_mono` and
  `Stacks.Groupoids.PreRelation.contains_left_of_isEtaleEquivalenceRelation`: the relation
  scheme of a monomorphic pre-relation on an affine object of a big fppf site belongs to that
  site, with monicity discharged from the internal equivalence-relation structure in the
  second form.
* `Stacks.Groupoids.PreRelation.surjective_source_left` and
  `Stacks.Groupoids.PreRelation.surjective_target_left`: the two maps of an equivalence
  relation are surjective, being split epimorphisms.
* `Stacks.Groupoids.PreRelation.map_siteSource` and
  `Stacks.Groupoids.PreRelation.map_siteTarget` identify the maps in the site with the source
  and target maps of the pre-relation, and
  `Stacks.Groupoids.PreRelation.etale_map_siteSource`,
  `Stacks.Groupoids.PreRelation.surjective_map_siteSource` and their target analogues record
  that they are étale and surjective.

## Implementation notes

`AlgebraicGeometry.Scheme.size_le_of_mono_quasiCompact`, the first case of 04VA, is applied
to the restrictions `V ⟶ Y` of the monomorphism to the affine opens `V` of its source rather
than to the monomorphism itself: those restrictions are quasi-compact because an affine
scheme maps affinely to a separated scheme, whereas the monomorphism itself carries no
finiteness hypothesis. The case of 04VA for a monomorphism locally of finite type is
therefore not needed, and neither is any finiteness property of `j`. The number of affine
opens of the source is bounded separately, by injectivity of the image map on affine opens.

The absolute product used for the target is the fibre product over the terminal scheme, not
over `S`: `U ×_S U` need not be affine for general `S`, while `U ×_{Spec ℤ} U` is affine as
soon as `U` is, and the comparison `U ×_S U ⟶ U ×_{Spec ℤ} U` is an immersion, hence a
monomorphism, for free.

## Relation to Stacks 0265

Tag 0265 says that the quotient of an affine scheme by an étale equivalence relation is an
algebraic space with the quotient map out of `U` as an étale surjective atlas. Its proof works
with the morphisms `R ⟶ U` *inside* the site and base changes along them, so it needs `R` as an
object of the site; a pre-relation does not provide that, and
`Stacks.Groupoids.PreRelation.siteObj` is what supplies it, the size cutoff being checked here
rather than assumed. Together with the kernel-pair description of the quotient projection
(`Stacks.Groupoids.isPullback_toQuotientPresheaf_of_isEquivalenceRelation`) and its local
surjectivity (`Stacks.Groupoids.isLocallySurjective_toQuotientSheaf`), the inputs that remain
for 0265 are the two descent results its own proof cites: tag 02W5, attaching a descent datum
to a sheaf along a covering, and tag 02W8, effectivity of such a datum for a separated locally
quasi-finite morphism.

## References

* [Stacks Project, Tag 04VA](https://stacks.math.columbia.edu/tag/04VA)
* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

/-- **The source of a monomorphism into a separated scheme of a big fppf site again belongs to
that site.** No finiteness hypothesis on the monomorphism is needed: its restrictions to the
affine opens of the source are quasi-compact, because an affine scheme maps affinely to a
separated scheme, so the first case of 04VA bounds the size of each affine open of the source
by the size of the target; and the affine opens of the source inject into the subsets of the
target, which the strong prelimit property of the cutoff bounds.

`AlgebraicGeometry.BigFppfSite.contains_of_mono` reaches the same conclusion with no
separatedness hypothesis at all, by reading the bound of Stacks 000R (8) off the strong
prelimit property of the cutoff directly. -/
theorem BigFppfSite.contains_of_mono_of_isSeparated (B : BigFppfSite.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [Mono f] [Scheme.IsSeparated Y] (hY : B.Contains Y) : B.Contains X := by
  classical
  have ha : #X.affineOpens ≤ 2 ^ #Y := by
    have hinj : Function.Injective (fun V : X.affineOpens ↦ f '' (V.1.1 : Set X)) := by
      intro V W h
      exact Subtype.ext (SetLike.coe_injective (Set.image_injective.mpr f.injective h))
    simpa only [mk_set] using mk_le_of_injective hinj
  have hpoints : #Y < B.cutoff :=
    (Scheme.mk_le_two_pow_size Y).trans_lt (B.cutoff_isStrongPrelimit hY)
  have hidx : #X.affineOpens < B.cutoff :=
    ha.trans_lt (B.cutoff_isStrongPrelimit hpoints)
  have hlocal (V : X.affineOpens) : (V.1 : Scheme.{u}).size ≤ Y.size := by
    have : IsAffine (V.1 : Scheme.{u}) := V.2
    exact Scheme.size_le_of_mono_quasiCompact (V.1.ι ≫ f)
  have : Nonempty X.affineOpens := ⟨⟨⊥, isAffineOpen_bot X⟩⟩
  exact (Scheme.size_le_of_iSup_eq_top (fun V : X.affineOpens ↦ V.1)
    (iSup_affineOpens_eq_top X)).trans_lt (max_lt hidx ((ciSup_le' hlocal).trans_lt hY))

end AlgebraicGeometry

namespace Stacks.Groupoids.PreRelation

variable {S : Scheme.{u}}

/-- **The relation scheme of a monomorphic pre-relation on an affine object of a big fppf site
belongs to that site.** The pre-relation is composed with the comparison from the fibre
product over `S` to the absolute product, which is an immersion and so a monomorphism; the
absolute product of an affine scheme with itself is affine, hence separated, and lies in the
site because the cutoff is closed under fibre products. -/
theorem contains_left_of_mono (B : BigFppfSite.{u}) {R U : Over S} (j : PreRelation R U)
    [Mono j] [IsAffine U.left] (hU : B.Contains U.left) : B.Contains R.left := by
  have hmono : Mono j.left := Functor.map_mono (Over.forget S) j
  set k := (Over.prodLeftIsoPullback U U).hom ≫
    pullback.mapDesc U.hom U.hom (terminal.from S) with hk
  have hkmono : Mono k := by rw [hk]; infer_instance
  have haff : IsAffineHom (U.hom ≫ terminal.from S) := inferInstance
  have : IsAffine (pullback (U.hom ≫ terminal.from S) (U.hom ≫ terminal.from S)) :=
    inferInstance
  exact B.contains_of_mono_of_isSeparated (j.left ≫ k) (Scheme.size_pullback_lt _ _ hU hU)

/-- **The relation scheme of an étale equivalence relation on an affine object of a big fppf
site belongs to that site.** Monicity is not an extra hypothesis: it follows from the internal
equivalence-relation structure, whose source and target maps are jointly monic. -/
theorem contains_left_of_isEtaleEquivalenceRelation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] {R : Over S}
    (j : PreRelation R ((Over.post B.inclusion).obj U)) [IsEtaleEquivalenceRelation j] :
    B.Contains R.left := by
  have : IsAffine ((Over.post B.inclusion).obj U).left :=
    ‹IsAffine ((BigFppfOver.toScheme B S hS).obj U)›
  have := mono_of_isEquivalenceRelation j
  exact contains_left_of_mono B j U.left.property

variable {R U : Over S} (j : PreRelation R U)

/-- The source map of an internal equivalence relation is a split epimorphism, split by the
reflexivity section. -/
theorem isSplitEpi_source [IsEquivalenceRelation j.target j.source] : IsSplitEpi j.source := by
  obtain ⟨e⟩ :=
    IsEquivalenceRelation.nonempty_equivalenceRelation (p₁ := j.target) (p₂ := j.source)
  exact ⟨⟨e.r, e.reflexivity₂⟩⟩

/-- The target map of an internal equivalence relation is a split epimorphism, split by the
reflexivity section. -/
theorem isSplitEpi_target [IsEquivalenceRelation j.target j.source] : IsSplitEpi j.target := by
  obtain ⟨e⟩ :=
    IsEquivalenceRelation.nonempty_equivalenceRelation (p₁ := j.target) (p₂ := j.source)
  exact ⟨⟨e.r, e.reflexivity₁⟩⟩

/-- A split epimorphism of schemes over `S` is surjective on points. -/
private theorem surjective_left_of_isSplitEpi {f : R ⟶ U} (h : IsSplitEpi f) :
    Surjective f.left := by
  obtain ⟨⟨r, hr⟩⟩ := h
  have hr' : r.left ≫ f.left = 𝟙 U.left := congrArg Over.Hom.left hr
  have : Surjective (r.left ≫ f.left) := by rw [hr']; infer_instance
  exact Surjective.of_comp r.left f.left

/-- **The source map of an internal equivalence relation is surjective on points.** It is a
split epimorphism, and a retraction of a map of schemes is surjective because it is so after
composing with the section. -/
theorem surjective_source_left [IsEquivalenceRelation j.target j.source] :
    Surjective j.source.left :=
  surjective_left_of_isSplitEpi (isSplitEpi_source j)

/-- **The target map of an internal equivalence relation is surjective on points.** -/
theorem surjective_target_left [IsEquivalenceRelation j.target j.source] :
    Surjective j.target.left :=
  surjective_left_of_isSplitEpi (isSplitEpi_target j)

section Site

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] {R : Over S}
  (j : PreRelation R ((Over.post B.inclusion).obj U)) [IsEtaleEquivalenceRelation j]

/-- The relation scheme of an étale equivalence relation on an affine object of a big fppf
site, as an object of that site over `S`. -/
def siteObj : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk
    (X := B.obj (contains_left_of_isEtaleEquivalenceRelation B S hS U j))
    (Y := B.obj hS) R.hom)

/-- The image of `siteObj` under the inclusion of the site into schemes over `S` is `R`. -/
@[simp]
theorem post_obj_siteObj : (Over.post B.inclusion).obj (siteObj B S hS U j) = R := rfl

/-- The source map of an étale equivalence relation, as a morphism of the big fppf site. -/
noncomputable def siteSource : siteObj B S hS U j ⟶ U :=
  (Over.post B.inclusion).preimage j.source

/-- The target map of an étale equivalence relation, as a morphism of the big fppf site. -/
noncomputable def siteTarget : siteObj B S hS U j ⟶ U :=
  (Over.post B.inclusion).preimage j.target

/-- The image of `siteSource` in schemes over `S` is the source map of `j`. -/
theorem map_siteSource :
    (Over.post B.inclusion).map (siteSource B S hS U j) = j.source :=
  (Over.post B.inclusion).map_preimage _

/-- The image of `siteTarget` in schemes over `S` is the target map of `j`. -/
theorem map_siteTarget :
    (Over.post B.inclusion).map (siteTarget B S hS U j) = j.target :=
  (Over.post B.inclusion).map_preimage _

/-- **The source map of an étale equivalence relation is étale as a morphism of the big fppf
site.** -/
theorem etale_map_siteSource :
    Etale ((BigFppfOver.toScheme B S hS).map (siteSource B S hS U j)) := by
  have h : IsEtaleEquivalenceRelation j := inferInstance
  show Etale ((Over.post B.inclusion).map (siteSource B S hS U j)).left
  rw [map_siteSource]
  exact h.etale_source

/-- **The target map of an étale equivalence relation is étale as a morphism of the big fppf
site.** -/
theorem etale_map_siteTarget :
    Etale ((BigFppfOver.toScheme B S hS).map (siteTarget B S hS U j)) := by
  have h : IsEtaleEquivalenceRelation j := inferInstance
  show Etale ((Over.post B.inclusion).map (siteTarget B S hS U j)).left
  rw [map_siteTarget]
  exact h.etale_target

/-- **The source map of an étale equivalence relation is surjective as a morphism of the big
fppf site.** -/
theorem surjective_map_siteSource :
    Surjective ((BigFppfOver.toScheme B S hS).map (siteSource B S hS U j)) := by
  show Surjective ((Over.post B.inclusion).map (siteSource B S hS U j)).left
  rw [map_siteSource]
  exact surjective_source_left j

/-- **The target map of an étale equivalence relation is surjective as a morphism of the big
fppf site.** -/
theorem surjective_map_siteTarget :
    Surjective ((BigFppfOver.toScheme B S hS).map (siteTarget B S hS U j)) := by
  show Surjective ((Over.post B.inclusion).map (siteTarget B S hS U j)).left
  rw [map_siteTarget]
  exact surjective_target_left j

end Site

end Stacks.Groupoids.PreRelation

end
