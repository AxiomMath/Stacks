module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite

/-!
# Every covering sieve of an affine étale chart is refined by a finite affine covering family

Let `F` be an algebraic space over a scheme `S` and let `U` be an *affine* étale chart of `F`.
A covering sieve of `U` in the small étale topology need not contain any of the site's chosen
covering families: the topology is the one *generated* by them, so a covering sieve is only
built up from them by the pullback and local-character axioms. This file shows that a covering
sieve of an affine chart is nevertheless *refined* by a covering family which is **finite** and
whose members are **affine**.

The finiteness is the point. An object of the small étale site of `F` is an arbitrary étale
chart; nothing restricts it to be quasi-compact, and the site contains the infinite disjoint
unions of affine charts produced by
`AlgebraicGeometry.Space.exists_etale_surjective_coproduct_affine_cover`. Over an affine chart
the restriction is harmless, because an affine scheme is quasi-compact and an étale covering of
it therefore has a finite refinement.

## Main results

* `AlgebraicGeometry.BigFppfSite.etaleCovering_singleton_id` and
  `AlgebraicGeometry.BigFppfSite.etaleCovering_bind`: the one-element family of an identity is a
  chosen étale covering family, and chosen étale covering families are closed under composition.
* `AlgebraicGeometry.Space.AffineEtale.isCovering_singleton_id` and
  `AlgebraicGeometry.Space.AffineEtale.isCovering_bind`: the same two closure properties for the
  covering families of the affine étale site of `F`.
* `AlgebraicGeometry.Space.AffineEtale.exists_covering_refining_pullback`: for a covering sieve
  `R` of an étale chart `U` and a morphism `a : X ⟶ U` from an *affine* chart, some covering
  family of `X` in the affine étale site has all its arrows carried into `R` by `a`.
* `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement`: **a covering sieve of an
  affine étale chart is refined by a finite family of affine étale charts which is itself
  covering.**

## Implementation notes

No fibre products of charts are used anywhere, and in particular the base-change axiom of a
site is never needed for the small étale site of `F`. The induction over
`CategoryTheory.Precoverage.Saturate` is run in the form *generalized over a morphism*
`a : X ⟶ U` from an affine chart, exactly as in the cocontinuity proof of Stacks 04JS in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineEtaleDenseSubsite.lean`: the pullback step of the
induction then becomes precomposition into `a`, and the only base change performed is the one
inside `AlgebraicGeometry.Space.exists_finite_affine_pullback_refinement`, which happens in
`Sch_κ` where the site axioms of `B` are available. So the two closure properties proved here
are only the isomorphism and composition axioms, both of which are combinatorial.

The size cutoff of `B` plays no role: the index type of the refinement is the index type of a
family already present in the site, so no new cardinality bound has to be checked and in
particular no regularity of `B.cutoff` is involved.

The headline statement is given with its index type in `Type`, not in the `Type (u + 1)` of the
site's own covering families: the refinement is finite, so it can be reindexed by a `Fin n`
without changing the presieve it generates
(`CategoryTheory.PreZeroHypercover.presieve₀_restrictIndex_equiv`). That is what lets a consumer
take the finite limit computing the sections over `U` from the sheaf condition without carrying
a universe-polymorphic index.

Nothing here mentions modules, so the module universe of the ringed site does not enter and the
statement is free of the universe constraint carried by the sheafification instances of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleSite.lean`.

## References

* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
* [Stacks Project, Tag 0H01](https://stacks.math.columbia.edu/tag/0H01)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Two combinatorial closure properties of chosen étale covering families -/

namespace BigFppfSite

/-- The one-element family of an identity is a chosen étale covering family.

This is the isomorphism axiom of a site for `AlgebraicGeometry.BigFppfSite.etaleCovering`, in
the only case it is needed below. The chosen-fppf half is the isomorphism axiom of `B` itself;
the étale half holds because an identity is surjective and étale. -/
theorem etaleCovering_singleton_id (B : BigFppfSite.{u}) (T : B.Schemes) :
    B.etaleCovering ⟨T, PreZeroHypercover.singleton.{u + 1} (𝟙 T)⟩ := by
  refine ⟨B.coverings_isSite.1 (𝟙 T), ?_⟩
  refine (Scheme.presieve₀_mem_precoverage_iff
    ((PreZeroHypercover.singleton.{u + 1} (𝟙 T)).map B.inclusion)).mpr
      ⟨fun x => ⟨PUnit.unit, x, ?_⟩, fun _ => ?_⟩
  · change (B.inclusion.map (𝟙 T)).base x = x
    rw [B.inclusion.map_id]
    rfl
  · change Etale (B.inclusion.map (𝟙 T))
    rw [B.inclusion.map_id]
    infer_instance

/-- **Chosen étale covering families are closed under composition.** A chosen étale covering
family of `T`, each of whose members is in turn covered by a chosen étale covering family,
composes to a chosen étale covering family of `T`.

This is the composition axiom of a site for `AlgebraicGeometry.BigFppfSite.etaleCovering`. The
chosen-fppf half is the composition axiom of `B`; the étale half is joint surjectivity of the
composites, which is the two joint surjectivities chained, together with stability of étale
morphisms under composition. -/
theorem etaleCovering_bind (B : BigFppfSite.{u}) {T : B.Schemes}
    (E : PreZeroHypercover.{u + 1} T) (hE : B.etaleCovering ⟨T, E⟩)
    (G : ∀ i, PreZeroHypercover.{u + 1} (E.X i))
    (hG : ∀ i, B.etaleCovering ⟨E.X i, G i⟩) :
    B.etaleCovering ⟨T, E.bind G⟩ := by
  have hEiff := (Scheme.presieve₀_mem_precoverage_iff (E.map B.inclusion)).mp hE.2
  have hGiff := fun i => (Scheme.presieve₀_mem_precoverage_iff
    ((G i).map B.inclusion)).mp (hG i).2
  have hEs : ∀ x : B.inclusion.obj T, ∃ i, ∃ y : B.inclusion.obj (E.X i),
      (B.inclusion.map (E.f i)).base y = x := hEiff.1
  have hEe : ∀ i, Etale (B.inclusion.map (E.f i)) := hEiff.2
  have hGs : ∀ i, ∀ y : B.inclusion.obj (E.X i), ∃ j, ∃ z : B.inclusion.obj ((G i).X j),
      (B.inclusion.map ((G i).f j)).base z = y := fun i => (hGiff i).1
  have hGe : ∀ i j, Etale (B.inclusion.map ((G i).f j)) := fun i => (hGiff i).2
  refine ⟨?_, ?_⟩
  · have h := B.coverings_isSite.2.1 ⟨T, E⟩ hE.1 (fun i => ⟨E.X i, G i⟩)
      (fun i => (hG i).1) (fun _ => rfl)
    have hfam : (E.bind fun i => (G i).pushforward (eqToHom (rfl : E.X i = E.X i))) =
        E.bind G := by
      simp [PreZeroHypercover.bind, PreZeroHypercover.pushforward]
    rwa [hfam] at h
  · refine (Scheme.presieve₀_mem_precoverage_iff ((E.bind G).map B.inclusion)).mpr
      ⟨fun x => ?_, fun ij => ?_⟩
    · obtain ⟨i, y, hy⟩ := hEs x
      obtain ⟨j, z, hz⟩ := hGs i y
      refine ⟨⟨i, j⟩, z, ?_⟩
      change (B.inclusion.map ((G i).f j ≫ E.f i)).base z = x
      rw [Functor.map_comp]
      change (B.inclusion.map (E.f i)).base ((B.inclusion.map ((G i).f j)).base z) = x
      rw [hz, hy]
    · have h1 := hEe ij.1
      have h2 := hGe ij.1 ij.2
      change Etale (B.inclusion.map ((G ij.1).f ij.2 ≫ E.f ij.1))
      rw [Functor.map_comp]
      infer_instance

end BigFppfSite

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### The same two closure properties for the affine étale site -/

/-- The one-element family of the identity of an affine étale chart is a covering family of the
affine étale site. -/
theorem AffineEtale.isCovering_singleton_id (X : AffineEtale B S hS F) :
    AffineEtale.IsCovering B S hS F ⟨X, PreZeroHypercover.singleton.{u + 1} (𝟙 X)⟩ := by
  refine ⟨?_, inferInstanceAs (Finite PUnit.{u + 2})⟩
  change B.etaleCovering ⟨(AffineEtale.toSchemes B S hS F).obj X,
    PreZeroHypercover.singleton.{u + 1} (𝟙 ((AffineEtale.toSchemes B S hS F).obj X))⟩
  exact B.etaleCovering_singleton_id _

/-- **The covering families of the affine étale site are closed under composition.** A covering
family of an affine chart, each of whose members is in turn covered by a covering family, has a
covering family of composites: the index type of the composite is a sigma type over finite
types, hence finite, and the geometric half is
`AlgebraicGeometry.BigFppfSite.etaleCovering_bind`. -/
theorem AffineEtale.isCovering_bind {X : AffineEtale B S hS F}
    (E : PreZeroHypercover.{u + 1} X) (hE : AffineEtale.IsCovering B S hS F ⟨X, E⟩)
    (G : ∀ i, PreZeroHypercover.{u + 1} (E.X i))
    (hG : ∀ i, AffineEtale.IsCovering B S hS F ⟨E.X i, G i⟩) :
    AffineEtale.IsCovering B S hS F ⟨X, E.bind G⟩ := by
  have _ : Finite E.I₀ := hE.2
  have _ : ∀ i, Finite (G i).I₀ := fun i => (hG i).2
  refine ⟨?_, inferInstanceAs (Finite (Σ i, (G i).I₀))⟩
  change B.etaleCovering ⟨(AffineEtale.toSchemes B S hS F).obj X,
    ((E.map (AffineEtale.inclusion B S hS F)).map (SmallEtale.toSchemes B S hS F)).bind
      fun i => ((G i).map (AffineEtale.inclusion B S hS F)).map
        (SmallEtale.toSchemes B S hS F)⟩
  exact B.etaleCovering_bind _ hE.1 _ fun i => (hG i).1

/-! ### Refining a covering sieve over an affine chart -/

/-- **Over an affine chart, a covering sieve is refined by a covering family of the affine étale
site.** Let `R` be a covering sieve of an étale chart `U` of `F` and let `a : X ⟶ U` be a
morphism of charts with `X` affine. Then some covering presieve of `X` in the affine étale site
— so a finite family of affine charts — has every one of its arrows carried into `R` by `a`.

The induction is over the generation of the small étale topology from its precoverage. Its
generating step is
`AlgebraicGeometry.Space.exists_finite_affine_pullback_refinement`; the pullback step is
precomposition into `a`, which is why no fibre products of charts are needed; and the
local-character step is
`AlgebraicGeometry.Space.AffineEtale.isCovering_bind`. -/
theorem AffineEtale.exists_covering_refining_pullback
    {U : SmallEtale B S hS F} {R : Sieve U} (hR : R ∈ SmallEtale.topology B S hS F U)
    {X : AffineEtale B S hS F} (a : (AffineEtale.inclusion B S hS F).obj X ⟶ U) :
    ∃ P : Presieve X, P ∈ AffineEtale.precoverage B S hS F X ∧
      ∀ ⦃Z : AffineEtale B S hS F⦄ (g : Z ⟶ X), P g →
        R ((AffineEtale.inclusion B S hS F).map g ≫ a) := by
  rw [SmallEtale.topology, Precoverage.mem_toGrothendieck_iff] at hR
  induction hR generalizing X with
  | of U P hP =>
      obtain ⟨E, rfl, hE⟩ := (SmallEtale.mem_precoverage_iff B S hS F).mp hP
      obtain ⟨E', hE', hfactor⟩ :=
        exists_finite_affine_pullback_refinement B S hS F X a E hE
      refine ⟨E'.presieve₀, hE', ?_⟩
      rintro Z g ⟨i⟩
      exact hfactor i
  | top U =>
      exact ⟨(PreZeroHypercover.singleton.{u + 1} (𝟙 X)).presieve₀,
        ⟨PreZeroHypercover.singleton.{u + 1} (𝟙 X), rfl,
          AffineEtale.isCovering_singleton_id B S hS F X⟩,
        fun _ _ _ => trivial⟩
  | pullback U R _ Y f ih =>
      obtain ⟨P, hP, hPle⟩ := ih (a ≫ f)
      refine ⟨P, hP, fun Z g hg => ?_⟩
      simpa only [Sieve.pullback_apply, Category.assoc] using hPle g hg
  | transitive U R T _ _ ih ihlocal =>
      obtain ⟨P, hP, hPle⟩ := ih a
      obtain ⟨E, rfl, hE⟩ := (AffineEtale.mem_precoverage_iff B S hS F).mp hP
      have key : ∀ i : E.I₀, ∃ D : PreZeroHypercover.{u + 1} (E.X i),
          AffineEtale.IsCovering B S hS F ⟨E.X i, D⟩ ∧
            ∀ j, T ((AffineEtale.inclusion B S hS F).map (D.f j ≫ E.f i) ≫ a) := by
        intro i
        obtain ⟨Q, hQ, hQle⟩ := ihlocal (hPle (E.f i) ⟨i⟩)
          (𝟙 ((AffineEtale.inclusion B S hS F).obj (E.X i)))
        obtain ⟨D, rfl, hD⟩ := (AffineEtale.mem_precoverage_iff B S hS F).mp hQ
        refine ⟨D, hD, fun j => ?_⟩
        simpa only [Sieve.pullback_apply, Functor.map_comp, Category.comp_id,
          Category.assoc] using hQle (D.f j) ⟨j⟩
      choose D hD hDle using key
      refine ⟨(E.bind D).presieve₀,
        ⟨E.bind D, rfl, AffineEtale.isCovering_bind B S hS F E hE D hD⟩, ?_⟩
      rintro Z g ⟨⟨i, j⟩⟩
      exact hDle i j

/-! ### The finite affine refinement -/

/-- **Stacks 03DX, the covering input: a covering sieve of an affine étale chart of an algebraic
space is refined by a finite covering family of affine étale charts.**

Precisely: if `U` is an étale chart of `F` whose underlying scheme is affine and `R` is a
covering sieve of `U` in the small étale topology, then there are finitely many affine étale
charts `V i` and morphisms `f i : V i ⟶ U` such that the sieve they generate is contained in `R`
and is itself a covering sieve.

The finiteness is what the base change criterion of Stacks 03DX(2) needs: the sections over `U`
are computed from the sections over the `V i` by the sheaf condition, a *finite* limit, and flat
base change — flatness of the restriction maps being
`AlgebraicGeometry.Space.flat_chartRestrict_of_isAffine` — commutes with it.

Affineness of `U` is not a convenience. The objects of the small étale site include infinite
disjoint unions of affine charts, over which no covering has a finite refinement; over an affine
chart the underlying scheme is quasi-compact and an étale covering of it does. -/
theorem SmallEtale.exists_finite_affine_refinement (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (R : Sieve U) (hR : R ∈ SmallEtale.topology B S hS F U) :
    ∃ (ι : Type) (_ : Finite ι) (V : ι → SmallEtale B S hS F) (f : ∀ i, V i ⟶ U),
      (∀ i, IsAffine
          ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (V i))) ∧
        Sieve.ofArrows V f ≤ R ∧
        Sieve.ofArrows V f ∈ SmallEtale.topology B S hS F U := by
  obtain ⟨P, hP, hPle⟩ :=
    AffineEtale.exists_covering_refining_pullback B S hS F hR (X := ⟨U, hU⟩) (𝟙 U)
  obtain ⟨E, rfl, hE⟩ := (AffineEtale.mem_precoverage_iff B S hS F).mp hP
  have _ : Finite E.I₀ := hE.2
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin E.I₀
  have hfam : Presieve.ofArrows
      (fun i : Fin n => (AffineEtale.inclusion B S hS F).obj (E.X (e.symm i)))
      (fun i => (AffineEtale.inclusion B S hS F).map (E.f (e.symm i))) =
      (E.map (AffineEtale.inclusion B S hS F)).presieve₀ := by
    refine le_antisymm ?_ ?_
    · rintro Y g ⟨i⟩
      exact ⟨e.symm i⟩
    · rintro Y g ⟨k⟩
      obtain ⟨i, rfl⟩ := e.symm.surjective k
      exact ⟨i⟩
  refine ⟨Fin n, inferInstance,
    fun i => (AffineEtale.inclusion B S hS F).obj (E.X (e.symm i)),
    fun i => (AffineEtale.inclusion B S hS F).map (E.f (e.symm i)),
    fun i => (E.X (e.symm i)).property, ?_, ?_⟩
  · rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    have h := hPle (E.f (e.symm i)) ⟨e.symm i⟩
    have hid : (AffineEtale.inclusion B S hS F).map (E.f (e.symm i)) ≫ 𝟙 U =
      (AffineEtale.inclusion B S hS F).map (E.f (e.symm i)) := Category.comp_id _
    exact hid ▸ h
  · change Sieve.generate (Presieve.ofArrows _ _) ∈ SmallEtale.topology B S hS F U
    rw [hfam]
    exact Precoverage.generate_mem_toGrothendieck
      ⟨E.map (AffineEtale.inclusion B S hS F), rfl, hE.1⟩

end Space

end AlgebraicGeometry

end
