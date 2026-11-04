module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusRepresentable
public import StacksFrontier.CategoryTheory.Sites.Stack.FullSubcategorySliceLocus

/-!
# The local complete intersection locus is inherited along morphisms

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
and let `d` be a natural number. The open locus of **Stacks 05X8** and **Stacks 06CE**, carried
as `AlgebraicGeometry.Stack.FiniteHilbert.HasOpenLciLocus`, says that every scheme-valued point
of `ℋ_d(𝒳/𝒴)` over an object `U` of the site cuts out an object `V` of the big fppf site of `U`
through which an object `T` maps exactly when the value of the point at `T` lies in the local
complete intersection locus of **Stacks 06CJ**.

That is already enough to see that the locus is inherited along *arbitrary* morphisms of
`ℋ_d(𝒳/𝒴)`: the base of a morphism `φ : x ⟶ y` names an object of the big fppf site of the base
of `y`, which maps to the terminal object, and the terminal object maps to `V` because `y` is in
the locus. This is the general statement
`CategoryTheory.Functor.prop_of_hom_of_sliceLocus`, read at the projection of `ℋ_d(𝒳/𝒴)`.

Condition (1) of **Stacks 04TU** follows, and with it that the locus is fibred in groupoids,
the witness that `AlgebraicGeometry.Stack.lciFiniteHilbertFibered` and
`AlgebraicGeometry.Stack.isAlgebraicStack_of_lciFiniteHilbertCover` take as an argument. The open
locus also gives condition (3) of Stacks 04TU, in its sieve form and in the covering-family form
of Stacks 02ZI that the stack-in-groupoids clause of Stacks 06CL,
`AlgebraicGeometry.Stack.isStackInGroupoids_lciFiniteHilbertCategory_of_flat`, consumes.

## Main results

* `AlgebraicGeometry.Stack.FiniteHilbert.lciLocus_of_hom`: the locus is inherited along
  morphisms of `ℋ_d(𝒳/𝒴)`.
* `AlgebraicGeometry.Stack.FiniteHilbert.closedUnderStronglyCartesianUpToIso_lciLocus`:
  condition (1) of Stacks 04TU for the locus.
* `AlgebraicGeometry.Stack.FiniteHilbert.locallyClosedUpToIso_lciLocus` and
  `AlgebraicGeometry.Stack.FiniteHilbert.lciLocus_of_cover`: condition (3) of Stacks 04TU for the
  locus, relative to covering sieves and relative to covering families.
* `AlgebraicGeometry.Stack.isFiberedInGroupoids_lciFiniteHilbertCategory`: the locus
  `ℋ_{d,lci}(𝒳/𝒴)` is fibred in groupoids over the big fppf site of `S`.

## References

* [Stacks Project, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU)
* [Stacks Project, Tag 05X8](https://stacks.math.columbia.edu/tag/05X8)
* [Stacks Project, Tag 06CE](https://stacks.math.columbia.edu/tag/06CE)
* [Stacks Project, Tag 06CJ](https://stacks.math.columbia.edu/tag/06CJ)
* [Stacks Project, Tag 06CL](https://stacks.math.columbia.edu/tag/06CL)
-/

@[expose] public section

open CategoryTheory

universe u w v₂ u₂

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w, u, v₂, u + 1, u₂} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory} {d : ℕ}

namespace FiniteHilbert

/-- **The local complete intersection locus is inherited along morphisms of `ℋ_d(𝒳/𝒴)`.** If
`φ : x ⟶ y` is a morphism of quintuples and `y` lies in the locus, so does `x`.

Read the open locus at the scheme-valued point of `ℋ_d(𝒳/𝒴)` attached to `y` by the 2-Yoneda
lemma: the terminal object of the big fppf site of the base of `y` maps to the object `V` it cuts
out, hence so does the object named by the base of `φ`, and the value of the point there is
isomorphic to `x`. -/
theorem lciLocus_of_hom (hopen : HasOpenLciLocus B S hS 𝒳 𝒴 F d)
    {x y : Object B S hS 𝒳 𝒴 F d} (φ : x ⟶ y)
    (hy : lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) y) :
    lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) x := by
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) :=
    isClosedUnderIsomorphisms_lciLocus
  refine Functor.prop_of_hom_of_sliceLocus _ isFiberedInGroupoids_finiteHilbertProjection _
    (fun U W hW => ?_) φ hy
  obtain ⟨V, -, hV⟩ := hopen U W hW
  exact ⟨V, hV⟩

/-- **Condition (1) of Stacks 04TU for the local complete intersection locus.** -/
theorem closedUnderStronglyCartesianUpToIso_lciLocus
    (hopen : HasOpenLciLocus B S hS 𝒳 𝒴 F d) :
    Functor.ClosedUnderStronglyCartesianUpToIso
      (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))
      (lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) :=
  Functor.closedUnderStronglyCartesianUpToIso_of_hom _ _ fun φ h => lciLocus_of_hom hopen φ h

/-- The shared argument for `locallyClosedUpToIso_lciLocus` and `lciLocus_of_cover`. -/
private theorem lciLocus_of_cover_aux (hopen : HasOpenLciLocus B S hS 𝒳 𝒴 F d)
    {U : BigFppfOver B S hS} {I : Type*} (V : I → BigFppfOver B S hS) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology B S hS U)
    (x₀ : Object B S hS 𝒳 𝒴 F d)
    (hx₀ : (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).obj x₀ = U)
    (x : I → Object B S hS 𝒳 𝒴 F d) (χ : ∀ i, x i ⟶ x₀)
    (hχ : ∀ i, (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴)
      (F := F) (d := d)).IsHomLift (f i) (χ i))
    (hx : ∀ i, lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)
      (x i)) :
    lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) x₀ := by
  have hfib := isFiberedInGroupoids_finiteHilbertProjection
    (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)
  have : (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).IsFibered := hfib.isFibered
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) :=
    isClosedUnderIsomorphisms_lciLocus
  obtain ⟨W, hWopen, hchar⟩ := hopen U
    (Functor.slicePointOfObject (finiteHilbertProjection (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) U x₀ hx₀)
    (Functor.slicePointOfObject_comp _ U x₀ hx₀)
  -- every member of the covering family maps to the object cut out by the locus
  have hi : ∀ i, Nonempty (Over.mk (f i).left ⟶ W) := by
    intro i
    refine (hchar (Over.mk (f i).left)).2 ?_
    obtain ⟨e⟩ := Functor.nonempty_iso_slicePointObj _ hfib hx₀ (f i) (χ i) (hχ i)
    exact ObjectProperty.prop_of_iso _ e.symm (hx i)
  -- hence that object has every point of the base in its image, so it is all of the base
  have hrange : Set.range (W.hom.hom).base = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y
    obtain ⟨V', g, hg, z, hz⟩ := BigFppfOver.exists_mem_range_of_mem_topology B S hS hf y
    obtain ⟨Y, k, g', hg', hfac⟩ := hg
    cases hg' with
    | mk i =>
      obtain ⟨m⟩ := hi i
      have hw : (m.left).hom ≫ (W.hom).hom = (BigFppfOver.toScheme B S hS).map (f i) :=
        congrArg (fun t : (V i).left ⟶ U.left => t.hom) (Over.w m)
      refine ⟨((m.left).hom).base (((BigFppfOver.toScheme B S hS).map k).base z), ?_⟩
      have hzy : ((BigFppfOver.toScheme B S hS).map (k ≫ f i)).base z = y := by
        rw [hfac]; exact hz
      rw [Functor.map_comp, ← hw] at hzy
      simpa using hzy
  have : AlgebraicGeometry.IsOpenImmersion (W.hom.hom) := hWopen
  have : IsIso (W.hom.hom) :=
    AlgebraicGeometry.isIso_of_isOpenImmersion_of_opensRange_eq_top _
      (TopologicalSpace.Opens.ext (by simpa using hrange))
  have : IsIso W.hom := (ObjectProperty.isIso_hom_iff W.hom).1 inferInstance
  have h0 := (hchar (Over.mk (𝟙 U.left))).1 ⟨Over.homMk (inv W.hom) (by simp)⟩
  have := Functor.isIso_slicePointUnit _ hfib U x₀ hx₀
  exact ObjectProperty.prop_of_iso _ (asIso (Functor.slicePointUnit
    (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)) U x₀ hx₀)) h0

/-- **Condition (3) of Stacks 04TU for the local complete intersection locus.** If the pullbacks
of an object of `ℋ_d(𝒳/𝒴)` along a covering family all lie in the locus, so does the object.

Read the open locus at the scheme-valued point attached to the object: each member of the
covering family maps to the object `V` it cuts out, so the underlying open immersion
`V ⟶ U` has every point of `U` in its image — a covering sieve of the big fppf site is jointly
surjective on points, `AlgebraicGeometry.BigFppfOver.exists_mem_range_of_mem_topology` — hence is
an isomorphism, hence the terminal object maps to `V` as well. -/
theorem locallyClosedUpToIso_lciLocus (hopen : HasOpenLciLocus B S hS 𝒳 𝒴 F d) :
    haveI : (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
        (d := d)).IsPreFibered :=
      isFiberedInGroupoids_finiteHilbertProjection.isFibered.toIsPreFibered
    Functor.LocallyClosedUpToIso
      (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))
      (lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))
      (BigFppfOver.topology B S hS) := by
  have hfib := isFiberedInGroupoids_finiteHilbertProjection
    (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)
  have : (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).IsFibered := hfib.isFibered
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) :=
    isClosedUnderIsomorphisms_lciLocus
  intro U κ Uᵢ fᵢ hcov x hx
  simp only [ObjectProperty.isoClosure_eq_self] at hx ⊢
  exact lciLocus_of_cover_aux hopen Uᵢ fᵢ hcov x.1 x.2 _
    (fun i => Functor.IsPreFibered.pullbackMap x.2 (fᵢ i)) (fun i => inferInstance) hx

/-- **Condition (3) of Stacks 04TU for the local complete intersection locus, relative to a
covering family.** If an object `x₀` of `ℋ_d(𝒳/𝒴)` over `U` receives morphisms over the members
of a covering family of `U` from objects of the locus, it lies in the locus.

This is `AlgebraicGeometry.Stack.FiniteHilbert.locallyClosedUpToIso_lciLocus` with the chosen
pullbacks replaced by arbitrary morphisms over the covering family, which is the form the
covering-family conditions of Stacks 02ZI produce. -/
theorem lciLocus_of_cover (hopen : HasOpenLciLocus B S hS 𝒳 𝒴 F d) {U : BigFppfOver B S hS}
    {I : Type*} (V : I → BigFppfOver B S hS) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology B S hS U)
    (x₀ : Object B S hS 𝒳 𝒴 F d)
    (hx₀ : (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).obj x₀ = U)
    (x : I → Object B S hS 𝒳 𝒴 F d) (χ : ∀ i, x i ⟶ x₀)
    (hχ : ∀ i, (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴)
      (F := F) (d := d)).IsHomLift (f i) (χ i))
    (hx : ∀ i, lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)
      (x i)) :
    lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) x₀ :=
  lciLocus_of_cover_aux hopen V f hf x₀ hx₀ x χ hχ hx

end FiniteHilbert

/-- **The local complete intersection locus is fibred in groupoids.** The locus
`ℋ_{d,lci}(𝒳/𝒴)` is fibred in groupoids over the big fppf site of `S`, given the open locus of
Stacks 05X8 and 06CE, which `AlgebraicGeometry.Stack.FiniteHilbert.hasOpenLciLocus` supplies at
the hypotheses of Stacks 06CL. It is part of the stack-in-groupoids clause of Stacks 06CL,
`AlgebraicGeometry.Stack.isStackInGroupoids_lciFiniteHilbertCategory_of_flat`.

Existence of lifts is existence of lifts in `ℋ_d(𝒳/𝒴)` together with
`AlgebraicGeometry.Stack.FiniteHilbert.lciLocus_of_hom`, which puts the source of the lift in the
locus; the fill-in clause needs no condition on the locus, the inclusion of a full subcategory
being fully faithful. -/
theorem isFiberedInGroupoids_lciFiniteHilbertCategory
    (hopen : FiniteHilbert.HasOpenLciLocus B S hS 𝒳 𝒴 F d) :
    (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p.IsFiberedInGroupoids :=
  Functor.isFiberedInGroupoids_restrict_of_hom _ isFiberedInGroupoids_finiteHilbertProjection _
    fun φ h => FiniteHilbert.lciLocus_of_hom hopen φ h

end AlgebraicGeometry.Stack

end
