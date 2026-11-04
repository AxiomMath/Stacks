module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.EtaleLocalStructure.ClosedImmersionOpens
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.FiniteProjection
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.GenericProjection
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.Basic

/-!
# Projecting a closed subvariety isomorphically near a nonsingular point

Let `V` be a finite-dimensional vector space over an algebraically closed field and let
`Z ⊆ X ⊆ 𝐏(V)` be closed subvarieties with `Z ≠ X ≠ 𝐏(V)`. For a point `x` of `Z` which is
nonsingular on `X` and a general closed point `p` of `𝐏(V)`, the projection `r_p` restricts on
`Z` to an isomorphism onto its image over an open neighbourhood of `r_p(x)`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_isClosedImmersion_projection_restrict`:
  a linear projection which is finite on a closed subscheme, unramified at a closed point `x` of
  it and injective on the fibre through `x` is a closed immersion over an open neighbourhood of
  the image of `x`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_unramifiedAt_fibre_inter_range_eq`:
  for a general centre the projection is defined on `X`, unramified at a closed point `z` of `Z`
  nonsingular on `X`, and its fibre through `z` meets `Z` only in `z`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_projection_restrict`:
  Tag 0H8A.

## Implementation notes

**The conclusion.** "The morphism `r_p|_Z : Z → r_p(Z)` is an isomorphism over an open
neighbourhood of `r_p(x)`" is read as: there is an open `N ∋ r_p(x)` of `𝐏(W_p)` such that the
restriction of `r_p|_Z` over `N` is a closed immersion, hence an isomorphism onto its image
there. This is the form in which the source's own citation, Tag 04DG, is available as
`AlgebraicGeometry.exists_open_restrict_isClosedImmersion_of_finite_unramified_fiber_eq_singleton`.

**The proof.** The source's proof is two steps. The first chooses the open `U` "as in the proof
of Tag 0B1Q", so that for a closed point `p ∈ U` the projection `r_p|_X` is unramified at `x` and
`r_p^{-1}(r_p(x)) ∩ Z = {x}`; this is
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_unramifiedAt_fibre_inter_range_eq`.
Unramifiedness comes from the core of Tag 0B1Q, a centre off `X` and off the linear subspace cut
out by the conormal space of `X` at `x`, which is proper in every codimension because `X ≠ 𝐏(V)`
forces `dim X < dim 𝐏(V)`, and
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_isFinite_unramifiedAt_projection_restrict`
is the resulting statement. The singleton fibre comes from the secant-cone lemma
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_nonempty_forall_eq_of_isIrreducible`,
which applies because `Z ≠ X` forces `dim Z < dim X`, so `dim Z ≤ dim 𝐏(V) - 2`. The second
step concludes for `Z` from finiteness (Tag 0B1P), unramifiedness at `x` and the singleton fibre
by Tag 04DG, after the two clauses descend from `X` to `Z` along the closed immersion `Z ⟶ X`.

**Unramified at a point.** Tag 04DG is formalized for a globally unramified morphism, while the
source only has unramifiedness at `x`. The gap is closed here: the locus of unramifiedness is open
(Tag 0475), the complement of an open neighbourhood of `x` inside it has closed image under the
finite `r_p|_Z`, and that image misses `r_p(x)` precisely because the fibre through `x` is `{x}`;
over the complement of the image the morphism is finite and unramified.

**Residue fields.** Tag 04DG also asks that the residue field extension at `x` be purely
inseparable. Over an algebraically closed field this is automatic at a closed point:
`AlgebraicGeometry.isIso_residueFieldMap_of_isClosed` makes the extension an isomorphism.

**Arbitrary points.** The argument runs at a closed point, where the cotangent space of `𝐏(V)` is
the hyperplane of degree-one forms vanishing there. An arbitrary point `x` of `Z` nonsingular on
`X` specializes to a closed point of `Z` still nonsingular on `X`, the regular locus of `X` being
open and the closed points of `Z` dense in every locally closed subset; the conclusion is about an
open neighbourhood of the image, so it passes from the specialization back to `x`.

## References

* [Stacks Project, Tag 0H8A](https://stacks.math.columbia.edu/tag/0H8A)
* [Stacks Project, Tag 0B1P](https://stacks.math.columbia.edu/tag/0B1P)
* [Stacks Project, Tag 0B1Q](https://stacks.math.columbia.edu/tag/0B1Q)
* [Stacks Project, Tag 04DG](https://stacks.math.columbia.edu/tag/04DG)
* [Stacks Project, Tag 0475](https://stacks.math.columbia.edu/tag/0475)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

/-- A field extension whose structure map is surjective is purely inseparable. -/
private theorem isPurelyInseparable_of_toAlgebra_surjective {F E : Type*} [Field F] [Field E]
    (φ : F →+* E) (h : Function.Surjective φ) :
    letI := φ.toAlgebra
    IsPurelyInseparable F E := by
  let _inst := φ.toAlgebra
  rw [isPurelyInseparable_iff]
  intro y
  obtain ⟨z, rfl⟩ := h y
  exact ⟨isIntegral_algebraMap, fun _ => ⟨z, rfl⟩⟩

/-- **Tag 04DG with an isomorphism of residue fields in place of pure inseparability.** A finite
unramified morphism whose fibre over the image of a point is that single point and whose
residue-field homomorphism there is an isomorphism is a closed immersion over an open
neighbourhood of the image. -/
private theorem exists_isOpen_isClosedImmersion_morphismRestrict_of_isIso_residueFieldMap
    {W S : Scheme.{u}} (f : W ⟶ S) [IsFinite f] [Unramified f] (x : W)
    (hfib : f ⁻¹' {f x} = {x}) (hiso : IsIso (f.residueFieldMap x)) :
    ∃ N : S.Opens, f x ∈ N ∧ IsClosedImmersion (f ∣_ N) := by
  have _i := hiso
  exact exists_open_restrict_isClosedImmersion_of_finite_unramified_fiber_eq_singleton
    f (f x) x hfib (isPurelyInseparable_of_toAlgebra_surjective _
      (ConcreteCategory.bijective_of_isIso _).surjective)

/-- A finite morphism which is unramified over an open neighbourhood `W₀` of a point whose fibre
is that single point is finite and unramified over an open neighbourhood of the image of the
point: the complement of `W₀` is closed, its image is closed because the morphism is finite, and
that image misses the image of the point because the fibre there is a singleton. -/
private theorem exists_isOpen_isFinite_unramified_morphismRestrict
    {W S : Scheme.{u}} (f : W ⟶ S) [IsFinite f] (x : W) (hfib : f ⁻¹' {f x} = {x})
    {W₀ : W.Opens} (hxW₀ : x ∈ W₀) (hW₀ : Unramified (W₀.ι ≫ f)) :
    ∃ N : S.Opens, f x ∈ N ∧ IsFinite (f ∣_ N) ∧ Unramified (f ∣_ N) := by
  have hzls : IsZariskiLocalAtSource (@Unramified.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := _)
  have himg : IsClosed (f '' (W₀ : Set W)ᶜ) := f.isClosedMap _ W₀.2.isClosed_compl
  have hnotmem : f x ∉ f '' (W₀ : Set W)ᶜ := by
    rintro ⟨z, hz, hzeq⟩
    have hzx : z ∈ f ⁻¹' {f x} := hzeq
    rw [hfib, Set.mem_singleton_iff] at hzx
    exact hz (hzx ▸ hxW₀)
  refine ⟨⟨_, himg.isOpen_compl⟩, hnotmem, inferInstance, ?_⟩
  have hle : f ⁻¹ᵁ (⟨_, himg.isOpen_compl⟩ : S.Opens) ≤ W₀ := by
    intro z hz
    by_contra hzn
    exact hz ⟨z, hzn, rfl⟩
  have hcomp : Unramified ((f ⁻¹ᵁ (⟨_, himg.isOpen_compl⟩ : S.Opens)).ι ≫ f) := by
    rw [← Scheme.homOfLE_ι (X := W) hle, Category.assoc]
    exact IsZariskiLocalAtSource.comp (P := @Unramified) hW₀ (W.homOfLE hle)
  rw [← morphismRestrict_ι f (⟨_, himg.isOpen_compl⟩ : S.Opens)] at hcomp
  have _i := hcomp
  exact unramified_of_comp (f ∣_ (⟨_, himg.isOpen_compl⟩ : S.Opens))
    (Scheme.Opens.ι (⟨_, himg.isOpen_compl⟩ : S.Opens))

/-- **A finite morphism over an algebraically closed field which is unramified near a closed
point with singleton fibre is a closed immersion near the image of that point.** This is Tag 04DG
with unramifiedness only near the point: over the complement of the image of the complement of
the neighbourhood the morphism is finite and unramified, and the residue-field extension at a
closed point over an algebraically closed field is an isomorphism. -/
private theorem exists_isOpen_isClosedImmersion_morphismRestrict
    {K : Type u} [Field K] [IsAlgClosed K] {W S : Scheme.{u}} (f : W ⟶ S)
    (q : S ⟶ Spec (.of K)) [IsFinite f] [LocallyOfFiniteType (f ≫ q)] (x : W)
    (hx : IsClosed ({x} : Set W)) (hfib : f ⁻¹' {f x} = {x})
    {W₀ : W.Opens} (hxW₀ : x ∈ W₀) (hW₀ : Unramified (W₀.ι ≫ f)) :
    ∃ N : S.Opens, f x ∈ N ∧ IsClosedImmersion (f ∣_ N) := by
  obtain ⟨N₀, hxN₀, hfinN, hunrN⟩ :=
    exists_isOpen_isFinite_unramified_morphismRestrict f x hfib hxW₀ hW₀
  have hxpre : x ∈ f ⁻¹ᵁ N₀ := hxN₀
  have hbase : (((f ∣_ N₀) (⟨x, hxpre⟩ : (f ⁻¹ᵁ N₀ : W.Opens))).1) = f x :=
    morphismRestrict_base_coe f N₀ ⟨x, hxpre⟩
  -- The fibre condition transfers to the restriction over `N₀`.
  have hfib' : (f ∣_ N₀) ⁻¹' {(f ∣_ N₀) (⟨x, hxpre⟩ : (f ⁻¹ᵁ N₀ : W.Opens))} =
      {(⟨x, hxpre⟩ : (f ⁻¹ᵁ N₀ : W.Opens))} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun hy => Subtype.ext ?_, fun hy => by rw [hy]⟩
    have hy' : f y.1 = f x := by
      rw [← morphismRestrict_base_coe f N₀ y, ← hbase]
      exact congrArg Subtype.val hy
    have hmem : y.1 ∈ f ⁻¹' {f x} := hy'
    rwa [hfib, Set.mem_singleton_iff] at hmem
  -- The point above `x` is closed, and the restriction is locally of finite type over `K`.
  have hx' : IsClosed ({(⟨x, hxpre⟩ : (f ⁻¹ᵁ N₀ : W.Opens))} :
      Set (f ⁻¹ᵁ N₀ : W.Opens)) := by
    have hpre : ({(⟨x, hxpre⟩ : (f ⁻¹ᵁ N₀ : W.Opens))} : Set (f ⁻¹ᵁ N₀ : W.Opens)) =
        (f ⁻¹ᵁ N₀ : W.Opens).ι ⁻¹' {x} := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun hy => by rw [hy]; rfl, fun hy => Subtype.ext hy⟩
    rw [hpre]
    exact IsClosed.preimage (Scheme.Hom.continuous _) hx
  have hLFT : LocallyOfFiniteType ((f ∣_ N₀) ≫ (N₀.ι ≫ q)) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    infer_instance
  have hiso : IsIso ((f ∣_ N₀).residueFieldMap (⟨x, hxpre⟩ : (f ⁻¹ᵁ N₀ : W.Opens))) :=
    isIso_residueFieldMap_of_isClosed _ (N₀.ι ≫ q) _ hx'
  obtain ⟨N₁, hN₁mem, hN₁⟩ :=
    exists_isOpen_isClosedImmersion_morphismRestrict_of_isIso_residueFieldMap
      (f ∣_ N₀) (⟨x, hxpre⟩ : (f ⁻¹ᵁ N₀ : W.Opens)) hfib' hiso
  exact ⟨N₀.ι ''ᵁ N₁, ⟨_, hN₁mem, hbase⟩, (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (morphismRestrictRestrict f N₀ N₁)).mp hN₁⟩

/-- If a closed immersion `iZ` factors as `e ≫ iX` with `iX` a closed immersion, so is `e`. -/
private theorem isClosedImmersion_of_comp_eq {Z X Y : Scheme.{u}} (e : Z ⟶ X) (iX : X ⟶ Y)
    [IsClosedImmersion iX] {iZ : Z ⟶ Y} [IsClosedImmersion iZ] (he : e ≫ iX = iZ) :
    IsClosedImmersion e := by
  subst he
  exact IsClosedImmersion.of_comp e iX

/-- A closed immersion which is not an isomorphism into an irreducible reduced Noetherian scheme
of dimension `n` lowers the dimension below `n`. -/
private theorem topologicalKrullDim_lt_natCast_of_isClosedImmersion {Y W : Scheme.{u}}
    (f : Y ⟶ W) [IsClosedImmersion f] [IsReduced W] [IrreducibleSpace W] [NoetherianSpace W]
    (hf : ¬ IsIso f) {n : ℕ} (hn : topologicalKrullDim W = n) :
    topologicalKrullDim Y < (n : WithBot ℕ∞) := by
  rw [← hn]
  refine IsClosedImmersion.topologicalKrullDim_lt f hf ?_
  rw [hn]
  change ((n : ℕ∞) : WithBot ℕ∞) ≠ ((⊤ : ℕ∞) : WithBot ℕ∞)
  exact fun h => ENat.natCast_ne_top n (WithBot.coe_inj.mp h)

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

/-- The projection is finite on a closed subscheme of its domain of definition and is a morphism
over the ground field: the two inputs to the local analysis of `r_W|_Z` at a point. -/
private theorem isFinite_and_locallyOfFiniteType_projection [FiniteDimensional k V]
    [Nontrivial V] {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion i]
    (W : Submodule k V) (j : Z ⟶ (projectionDomain k V W).toScheme)
    (hj : j ≫ (projectionDomain k V W).ι = i) :
    IsFinite (j ≫ projection k V W) ∧ LocallyOfFiniteType ((j ≫ projection k V W) ≫
      projectiveSpaceOfModuleToSpec k ↥W) := by
  refine ⟨isFinite_projection_of_isClosedImmersion i W j hj, ?_⟩
  have hstruct : (j ≫ projection k V W) ≫ projectiveSpaceOfModuleToSpec k ↥W =
      i ≫ projectiveSpaceOfModuleToSpec k V := by
    rw [Category.assoc, projection_comp_toSpec, ← Category.assoc, hj]
  rw [hstruct]
  infer_instance

/-- The local step of Tag 0H8A, with unramifiedness supplied on an open neighbourhood of the
point rather than at the point itself. -/
private theorem exists_isOpen_isClosedImmersion_projection_restrict_of_unramified_ι_comp
    [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V] {Z : Scheme.{u}}
    (i : Z ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion i] (W : Submodule k V)
    (j : Z ⟶ (projectionDomain k V W).toScheme) (hj : j ≫ (projectionDomain k V W).ι = i)
    (x : Z) (hx : IsClosed ({x} : Set Z))
    (hfib : (j ≫ projection k V W) ⁻¹' {(j ≫ projection k V W) x} = {x})
    {Z₀ : Z.Opens} (hxZ₀ : x ∈ Z₀) (hZ₀ : Unramified (Z₀.ι ≫ (j ≫ projection k V W))) :
    ∃ N : (projectiveSpaceOfModule k ↥W).Opens, (j ≫ projection k V W) x ∈ N ∧
      IsClosedImmersion ((j ≫ projection k V W) ∣_ N) := by
  obtain ⟨hfin, hLFT⟩ := isFinite_and_locallyOfFiniteType_projection i W j hj
  exact exists_isOpen_isClosedImmersion_morphismRestrict (j ≫ projection k V W)
    (projectiveSpaceOfModuleToSpec k ↥W) x hx hfib hxZ₀ hZ₀

/-- **The local step of Tag 0H8A.** Let `i : Z ⟶ 𝐏(V)` be a closed immersion factoring through
the domain of definition of the projection away from the linear subspace cut out by a submodule
`W ≤ V`, and let `x` be a closed point of `Z` at which the resulting morphism `r_W|_Z` is
unramified and whose fibre through `x` is `{x}`. Then `r_W|_Z` is a closed immersion over an open
neighbourhood of the image of `x`, hence an isomorphism onto its image there. -/
public theorem exists_isOpen_isClosedImmersion_projection_restrict [IsAlgClosed k]
    [FiniteDimensional k V] [Nontrivial V] {Z : Scheme.{u}}
    (i : Z ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion i] (W : Submodule k V)
    (j : Z ⟶ (projectionDomain k V W).toScheme) (hj : j ≫ (projectionDomain k V W).ι = i)
    (x : Z) (hx : IsClosed ({x} : Set Z))
    (hfib : (j ≫ projection k V W) ⁻¹' {(j ≫ projection k V W) x} = {x})
    (hunr : UnramifiedAt (j ≫ projection k V W) x) :
    ∃ N : (projectiveSpaceOfModule k ↥W).Opens, (j ≫ projection k V W) x ∈ N ∧
      IsClosedImmersion ((j ≫ projection k V W) ∣_ N) := by
  refine exists_isOpen_isClosedImmersion_projection_restrict_of_unramified_ι_comp i W j hj x hx
    hfib (Z₀ := ⟨_, isOpen_setOf_unramifiedAt (j ≫ projection k V W)⟩) hunr ?_
  exact unramified_ι_comp_of_forall_unramifiedAt (j ≫ projection k V W) _ fun _ hy => hy

/-- **The local step of Tag 0H8A, from the ambient subvariety.** Let `Z ⊆ X ⊆ 𝐏(V)` be closed
subschemes, let `jX` lift the inclusion of `X` through the domain of definition of `r_W`, and let
`x` be a closed point of `Z` at which `r_W|_X` is unramified and such that the fibre of `r_W|_X`
through `x` meets `Z` only in `x`. Then `r_W|_Z` is a closed immersion over an open neighbourhood
of the image of `x`. Both clauses descend from `X` to `Z` along the closed immersion `Z ⟶ X`:
the fibre one because a closed immersion is injective, unramifiedness through the open
unramified locus of `r_W|_X`. -/
private theorem exists_isOpen_isClosedImmersion_projection_restrict_of_ambient [IsAlgClosed k]
    [FiniteDimensional k V] [Nontrivial V] {Z X : Scheme.{u}}
    (iZ : Z ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iZ]
    (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    (e : Z ⟶ X) (he : e ≫ iX = iZ) (W : Submodule k V)
    (jX : X ⟶ (projectionDomain k V W).toScheme) (hjX : jX ≫ (projectionDomain k V W).ι = iX)
    (x : Z) (hx : IsClosed ({x} : Set Z))
    (hunrX : UnramifiedAt (jX ≫ projection k V W) (e x))
    (hfibX : (jX ≫ projection k V W) ⁻¹' {(jX ≫ projection k V W) (e x)} ∩ Set.range e =
      {e x}) :
    ∃ N : (projectiveSpaceOfModule k ↥W).Opens, ((e ≫ jX) ≫ projection k V W) x ∈ N ∧
      IsClosedImmersion (((e ≫ jX) ≫ projection k V W) ∣_ N) := by
  have hce := isClosedImmersion_of_comp_eq e iX he
  have hjZ : (e ≫ jX) ≫ (projectionDomain k V W).ι = iZ := by
    rw [Category.assoc, hjX, he]
  have hjp : (e ≫ jX) ≫ projection k V W = e ≫ (jX ≫ projection k V W) :=
    Category.assoc _ _ _
  -- The fibre condition descends along the closed immersion `e`, which is injective.
  have hfib : ((e ≫ jX) ≫ projection k V W) ⁻¹' {((e ≫ jX) ≫ projection k V W) x} = {x} := by
    rw [hjp]
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply]
    refine ⟨fun hy => e.isClosedEmbedding.injective ?_, fun hy => by rw [hy]⟩
    have hmem : e y ∈ (jX ≫ projection k V W) ⁻¹' {(jX ≫ projection k V W) (e x)} ∩
        Set.range e := ⟨hy, ⟨y, rfl⟩⟩
    rwa [hfibX, Set.mem_singleton_iff] at hmem
  -- So does unramifiedness at `x`, through the open unramified locus of `r_W|_X`.
  have hVunr : Unramified (Scheme.Opens.ι (⟨_, isOpen_setOf_unramifiedAt
      (jX ≫ projection k V W)⟩ : X.Opens) ≫ (jX ≫ projection k V W)) :=
    unramified_ι_comp_of_forall_unramifiedAt _ _ fun _ hy => hy
  refine exists_isOpen_isClosedImmersion_projection_restrict_of_unramified_ι_comp iZ W (e ≫ jX)
    hjZ x hx hfib (Z₀ := e ⁻¹ᵁ ⟨_, isOpen_setOf_unramifiedAt (jX ≫ projection k V W)⟩)
    hunrX ?_
  rw [hjp, ← Category.assoc, ← morphismRestrict_ι e _, Category.assoc]
  exact MorphismProperty.comp_mem @Unramified _ _ inferInstance hVunr

/-- The image of a closed subvariety of `𝐏(V)` is a closed irreducible subset of the same
dimension as the subvariety. -/
private theorem isClosed_isIrreducible_range_base {Z : Scheme.{u}}
    (iZ : Z ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iZ] [IrreducibleSpace Z] :
    IsClosed (Set.range iZ.base) ∧ IsIrreducible (Set.range iZ.base) ∧
      topologicalKrullDim ↥(Set.range iZ.base) = topologicalKrullDim Z := by
  refine ⟨iZ.isClosedEmbedding.isClosed_range, ?_, ?_⟩
  · simpa only [Set.image_univ] using (IrreducibleSpace.isIrreducible_univ Z).image iZ.base
      iZ.base.hom.continuous.continuousOn
  · exact (IsHomeomorph.topologicalKrullDim_eq _
      iZ.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

section

variable [IsAlgClosed k] [FiniteDimensional k V]

/-- **A nonempty open set of centres for which the projection is unramified at a point of `Z` and
separates that point from the rest of `Z`.** Let `V` have dimension `m + 2`, let `X ⊆ 𝐏(V)` be a
closed subvariety other than `𝐏(V)`, let `Z ⊆ X` be an irreducible closed subscheme of dimension
less than `m` and let `z` be a closed point of `Z` which is nonsingular on `X`. Then there is a
nonempty Zariski open `U ⊆ 𝐏(V)` such that for every closed point `p ∈ U` the projection `r_p` is
defined on `X`, the morphism `r_p|_X` is unramified at `z` and the fibre of `r_p|_X` through `z`
meets `Z` only in `z`.

Unramifiedness holds for a centre off `X` and off the linear subspace cut out by the conormal
space of `X` at `z`; the fibre condition holds for a general centre because `Z` has dimension
less than that of `𝐏(W_z)`, so its secant directions at `z` do not fill `𝐏(W_z)` and a centre
off the secant cone separates `z` from the rest of `Z`. -/
public theorem exists_isOpen_unramifiedAt_fibre_inter_range_eq {m : ℕ}
    (hV : Module.finrank k V = m + 2) {X Z : Scheme.{u}}
    (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)] (hXP : ¬ IsIso iX)
    (iZ : Z ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iZ] [IrreducibleSpace Z]
    (e : Z ⟶ X) (he : e ≫ iX = iZ)
    (hdimZ : topologicalKrullDim Z < (m : WithBot ℕ∞))
    (z : Z) (hzc : IsClosed ({z} : Set Z)) (hzreg : e z ∈ regularLocus X) :
    ∃ U : (projectiveSpaceOfModule k V).Opens,
      (U : Set (projectiveSpaceOfModule k V)).Nonempty ∧
      ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
        ∃ jX : X ⟶ (projectionDomain k V (pointSubmodule k V p)).toScheme,
          jX ≫ (projectionDomain k V (pointSubmodule k V p)).ι = iX ∧
          UnramifiedAt (jX ≫ projection k V (pointSubmodule k V p)) (e z) ∧
          (jX ≫ projection k V (pointSubmodule k V p)) ⁻¹'
              {(jX ≫ projection k V (pointSubmodule k V p)) (e z)} ∩ Set.range e = {e z} := by
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  have hce := isClosedImmersion_of_comp_eq e iX he
  have hezc : IsClosed ({e z} : Set X) := by
    simpa using e.isClosedEmbedding.isClosedMap _ hzc
  obtain ⟨hZc, hZirr, hZdim⟩ := isClosed_isIrreducible_range_base iZ
  obtain ⟨U₁, hU₁ne, hU₁⟩ :=
    exists_isOpen_isFinite_unramifiedAt_projection_restrict iX hXP (e z) hezc hzreg
  obtain ⟨U₂, hU₂open, hU₂ne, hU₂⟩ := exists_isOpen_nonempty_forall_eq_of_isIrreducible k V
    (iZ.base z) (isClosed_singleton_base iZ z hzc) hV hZc hZirr (by rw [hZdim]; exact hdimZ)
  refine ⟨⟨(U₁ : Set (projectiveSpaceOfModule k V)) ∩ U₂, U₁.isOpen.inter hU₂open⟩,
    nonempty_preirreducible_inter U₁.isOpen hU₂open hU₁ne hU₂ne, ?_⟩
  rintro p ⟨hp₁, hp₂⟩ hpc
  obtain ⟨jX, hjX, -, hunr⟩ := hU₁ p hp₁ hpc
  obtain ⟨_, hsep⟩ := hU₂ p hp₂ hpc
  have hbase : ∀ y : X, (jX.base y).1 = iX.base y := fun y => by
    rw [← hjX]
    rfl
  have hzval : (jX.base (e z)).1 = iZ.base z := by rw [hbase (e z), ← he]; rfl
  refine ⟨jX, hjX, hunr, ?_⟩
  refine Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr ⟨rfl, z, rfl⟩)
  rintro y ⟨hy, w, rfl⟩
  have hyZ : (jX.base (e w)).1 ∈ Set.range iZ.base := by
    rw [hbase (e w), ← he]
    exact ⟨w, rfl⟩
  have hproj : projection k V (pointSubmodule k V p) (jX.base (e w)) =
      projection k V (pointSubmodule k V p) (jX.base (e z)) := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply] using hy
  have heq := hsep (jX.base (e w)) (jX.base (e z)) hyZ hzval hproj
  have hz2 : iZ.base z = iX.base (e z) := by rw [← he]; rfl
  rw [hbase (e w), hz2] at heq
  exact Set.mem_singleton_iff.mpr (iX.isClosedEmbedding.injective heq)

/-- **Tag 0H8A at a closed point.** The case of the following theorem in which the point `x` is
closed, which is where the secant cone and the conormal space are available. -/
private theorem exists_isOpen_forall_closedPoint_projection_restrict_of_isClosed
    {Z X : Scheme.{u}}
    (iZ : Z ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iZ] [IrreducibleSpace Z]
    (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (e : Z ⟶ X) (he : e ≫ iX = iZ) (hZX : ¬ IsIso e) (hX : ¬ IsIso iX)
    (x : Z) (hx : IsClosed ({x} : Set Z)) (hreg : e x ∈ regularLocus X) :
    ∃ U : (projectiveSpaceOfModule k V).Opens,
      (U : Set (projectiveSpaceOfModule k V)).Nonempty ∧
      ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
        ∃ j : Z ⟶ (projectionDomain k V (pointSubmodule k V p)).toScheme,
          j ≫ (projectionDomain k V (pointSubmodule k V p)).ι = iZ ∧
          ∃ N : (projectiveSpaceOfModule k ↥(pointSubmodule k V p)).Opens,
            (j ≫ projection k V (pointSubmodule k V p)) x ∈ N ∧
            IsClosedImmersion ((j ≫ projection k V (pointSubmodule k V p)) ∣_ N) := by
  have hce := isClosedImmersion_of_comp_eq e iX he
  -- `V` is nontrivial, `𝐏(V)` having the closed point `iZ x`.
  have hV1 : 1 ≤ Module.finrank k V := by
    have h1 := Submodule.finrank_quotient_add_finrank (pointSubmodule k V (iZ.base x))
    rw [finrank_quotient_pointSubmodule k V _ (isClosed_singleton_base iZ x hx)] at h1
    omega
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank k V = n + 1 := ⟨_, (Nat.sub_add_cancel hV1).symm⟩
  -- The dimensions: `dim Z < dim X < dim 𝐏(V) = n`.
  have : IsReduced (projectiveSpaceOfModule k V) := isReduced_projectiveSpaceOfModule k V
  have : IsLocallyNoetherian (projectiveSpaceOfModule k V) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOfModuleToSpec k V)
  have : CompactSpace (projectiveSpaceOfModule k V) :=
    QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceOfModuleToSpec k V)
  have : IsNoetherian (projectiveSpaceOfModule k V) := {}
  have : NoetherianSpace X := iX.isClosedEmbedding.isInducing.noetherianSpace
  have hPdim := topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hn
  have hXlt := topologicalKrullDim_lt_natCast_of_isClosedImmersion iX hX hPdim
  have : Nonempty X := ⟨e x⟩
  obtain ⟨d, hd, hdn⟩ := exists_nat_topologicalKrullDim_eq_of_lt hXlt
  have hZlt := topologicalKrullDim_lt_natCast_of_isClosedImmersion e hZX hd
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hdimZ : topologicalKrullDim Z < (m : WithBot ℕ∞) :=
    hZlt.trans_le (by exact_mod_cast (show d ≤ m by omega))
  obtain ⟨U, hUne, hU⟩ := exists_isOpen_unramifiedAt_fibre_inter_range_eq (m := m)
    (by rw [hn]) iX hX iZ e he hdimZ x hx hreg
  refine ⟨U, hUne, fun p hp hpc => ?_⟩
  obtain ⟨jX, hjX, hunr, hfib⟩ := hU p hp hpc
  exact ⟨e ≫ jX, by rw [Category.assoc, hjX, he],
    exists_isOpen_isClosedImmersion_projection_restrict_of_ambient iZ iX e he _ jX hjX x hx
      hunr hfib⟩

/-- **Stacks Project, Tag 0H8A.** Let `V` be a finite-dimensional vector space over an
algebraically closed field `k`, let `Z ⊆ X ⊆ 𝐏(V)` be closed subvarieties with `Z ≠ X` and
`X ≠ 𝐏(V)`, and let `x` be a point of `Z` which is nonsingular on `X`. Then there is a nonempty
Zariski open `U ⊆ 𝐏(V)` such that for every closed point `p ∈ U` the projection `r_p` is
defined on `Z` and the morphism `r_p|_Z : Z → r_p(Z)` is an isomorphism over an open
neighbourhood of `r_p(x)`.

`X` is a closed subvariety, a closed immersion `iX` whose source is a variety over `k`; `Z` is
an irreducible closed subscheme of `X`, the closed immersion `e` with `e ≫ iX = iZ` — this
generalizes the source, which takes `Z` reduced as well. `Z ≠ X` and `X ≠ 𝐏(V)` are `e` and `iX`
not being isomorphisms. That `r_p` is defined on `Z` is the lift `j` of `iZ` through the domain
of definition of the projection away from `p`, and the isomorphism of `Z` onto `r_p(Z)` over a
neighbourhood `N` of `r_p(x)` is spelled as `r_p|_Z` restricted over `N` being a closed
immersion, which is the same thing: a closed immersion over `N` is an isomorphism of its source
onto its scheme-theoretic image, and that image is `r_p(Z) ∩ N`. -/
@[stacks 0H8A]
public theorem exists_isOpen_forall_closedPoint_projection_restrict {Z X : Scheme.{u}}
    (iZ : Z ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iZ] [IrreducibleSpace Z]
    (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (e : Z ⟶ X) (he : e ≫ iX = iZ) (hZX : ¬ IsIso e) (hX : ¬ IsIso iX)
    (x : Z) (hreg : e x ∈ regularLocus X) :
    ∃ U : (projectiveSpaceOfModule k V).Opens,
      (U : Set (projectiveSpaceOfModule k V)).Nonempty ∧
      ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
        ∃ j : Z ⟶ (projectionDomain k V (pointSubmodule k V p)).toScheme,
          j ≫ (projectionDomain k V (pointSubmodule k V p)).ι = iZ ∧
          ∃ N : (projectiveSpaceOfModule k ↥(pointSubmodule k V p)).Opens,
            (j ≫ projection k V (pointSubmodule k V p)) x ∈ N ∧
            IsClosedImmersion ((j ≫ projection k V (pointSubmodule k V p)) ∣_ N) := by
  -- `x` specializes to a closed point `y` of `Z` which is still nonsingular on `X`.
  have hce := isClosedImmersion_of_comp_eq e iX he
  have : JacobsonSpace Z :=
    LocallyOfFiniteType.jacobsonSpace (e ≫ iX ≫ projectiveSpaceOfModuleToSpec k V)
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (iX ≫ projectiveSpaceOfModuleToSpec k V)
  have hopen : IsOpen (e.base ⁻¹' regularLocus X) :=
    ((Scheme.isJ2_of_locallyOfFiniteType_over_field k
      (iX ≫ projectiveSpaceOfModuleToSpec k V)).isOpen_regularLocus (𝟙 X)).preimage e.continuous
  obtain ⟨y, ⟨hycl, hyreg⟩, hyc⟩ := nonempty_inter_closedPoints
    (Z := closure ({x} : Set Z) ∩ e.base ⁻¹' regularLocus X) ⟨x, subset_closure rfl, hreg⟩
    (isClosed_closure.isLocallyClosed.inter hopen.isLocallyClosed)
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hycl
  -- The conclusion at `y` concerns an open neighbourhood, so it passes back to `x`.
  obtain ⟨U, hUne, hU⟩ :=
    exists_isOpen_forall_closedPoint_projection_restrict_of_isClosed iZ iX e he hZX hX y hyc hyreg
  refine ⟨U, hUne, fun p hp hpc => ?_⟩
  obtain ⟨j, hj, N, hN, hci⟩ := hU p hp hpc
  exact ⟨j, hj, N, (hxy.map (j ≫ projection k V (pointSubmodule k V p)).continuous).mem_open
    N.isOpen hN, hci⟩

end

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
