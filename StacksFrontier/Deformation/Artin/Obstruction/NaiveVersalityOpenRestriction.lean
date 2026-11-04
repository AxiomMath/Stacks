module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityAffineOpenBase

/-!
# Versality is unchanged by restriction to an open subscheme

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S`, let `x` be an object
of `𝒳` over `U`, and let `x'` be an object of `𝒳` over `U'` carrying an arrow `x' ⟶ x` whose
underlying morphism of schemes `j : U' ⟶ U` is an open immersion. This file shows that the
lifting property `Deformation.Artin.LiftsAtResiduePoint` holds for `x` at a residue point
`κ ≫ j` exactly when it holds for `x'` at `κ`.

This is the invariance that the geometric reduction at the start of [Stacks, Tag 07YU] needs:
there a scheme `U` locally of finite type over `S` is replaced by an affine open in which the
chosen finite type point is closed, and versality has to be read in either.

## Main results

* `Deformation.Artin.liftsAtResiduePoint_iff_restrict` — the lifting property at `κ ≫ j` for
  `x` and at `κ` for `x'` are the same property.

## Implementation notes

Both implications are the unique factorization through a cartesian arrow
(`Deformation.Artin.factor_through_cartesian_schemeMap`) applied to the arrow `x' ⟶ x`; what
makes them available is that every scheme occurring in a lifting problem is the spectrum of an
Artinian local ring, hence a one-point space, so a morphism out of it whose value at one point
lands in the image of `j` lands there entirely. That is
`Deformation.Artin.range_subset_range_of_comp` together with
`Deformation.Artin.subsingleton_spec_of_isArtinianRing`, and `j` being an open immersion is what
turns the resulting inclusion of ranges into an actual factorization.

The open immersion is phrased as an arbitrary `j` together with an equation identifying it with
the morphism of schemes underlying `ρ`, and its being an open immersion is an ordinary
hypothesis rather than an instance: at the point of use the source of `j` is the spectrum of the
ring of a charted object, which is the spectrum of its ring only after unfolding a definition,
and instance search does not unfold.

## References

* [Stacks Project, Tag 07YU](https://stacks.math.columbia.edu/tag/07YU)
* [Stacks Project, Tag 07XF](https://stacks.math.columbia.edu/tag/07XF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v w

/-! ### The spectrum of an Artinian local ring is a one-point space -/

/-- The spectrum of an Artinian local ring is a one-point space: every prime of an Artinian
ring is maximal, and a local ring has exactly one maximal ideal. -/
public theorem subsingleton_spec_of_isArtinianRing (A : Type u) [CommRing A] [IsArtinianRing A]
    [IsLocalRing A] (a b : (Spec (CommRingCat.of A) : Scheme.{u})) : a = b := by
  have key : ∀ c : (Spec (CommRingCat.of A) : Scheme.{u}),
      c.asIdeal = IsLocalRing.maximalIdeal A := fun c =>
    have : c.asIdeal.IsPrime := c.isPrime
    IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime c.asIdeal)
  exact PrimeSpectrum.ext ((key a).trans (key b).symm)

/-- A morphism out of a one-point space lands in the image of `j` as soon as it does so after
precomposition with a morphism from a nonempty scheme. -/
public theorem range_subset_range_of_comp {W W' Z Y : Scheme.{u}} (h : W' ⟶ W) (g : W ⟶ Z)
    (j : Y ⟶ Z) (κ : W' ⟶ Y) (hcomp : h ≫ g = κ ≫ j) (w' : W')
    (hsub : ∀ a b : W, a = b) : Set.range g.base ⊆ Set.range j.base := by
  rintro _ ⟨t, rfl⟩
  rw [hsub t (h.base w')]
  refine ⟨κ.base w', ?_⟩
  simpa using (congrArg (fun m : W' ⟶ Z => m.base w') hcomp).symm

/-! ### The lifting property and restriction along an open immersion -/

section Restriction

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (CommRingCat.of Λ) ⟶ S)
  {U U' : Over S} {x x' : X}
  (hx : (p ⋙ Over.post B.inclusion).obj x = U)
  (hx' : (p ⋙ Over.post B.inclusion).obj x' = U')
  (ρ : x' ⟶ x) (j : U'.left ⟶ U.left) (hj : IsOpenImmersion j)
  (hρ : schemeMap (p ⋙ Over.post B.inclusion) hx' hx ρ = j)
  (κ : Spec (CommRingCat.of k) ⟶ U'.left)

include hρ in
/-- The structure morphism of the open restriction factors that of the ambient object. -/
public theorem comp_hom_eq_of_schemeMap_eq : j ≫ U.hom = U'.hom := by
  rw [← hρ]
  exact schemeMap_over (p ⋙ Over.post B.inclusion) hx' hx ρ

/-- An arrow into `x` whose underlying morphism lands in the image of `j` lifts along `ρ`. -/
private theorem exists_comp_eq_of_range_subset (hp : p.IsFiberedInGroupoids)
    (hj : IsOpenImmersion j) (hρ : schemeMap (p ⋙ Over.post B.inclusion) hx' hx ρ = j)
    {y : X} {Y : Over S} (hy : (p ⋙ Over.post B.inclusion).obj y = Y) (a : y ⟶ x)
    (hrange : Set.range (schemeMap _ hy hx a).base ⊆ Set.range j.base) :
    ∃ l : y ⟶ x', l ≫ ρ = a := by
  have := hj
  have hgfac := IsOpenImmersion.lift_fac j (schemeMap _ hy hx a) hrange
  obtain ⟨l, hl, -⟩ := factor_through_cartesian_schemeMap B S hS p hp hy hx' hx ρ a
    (IsOpenImmersion.lift j (schemeMap _ hy hx a) hrange)
    (by
      rw [← comp_hom_eq_of_schemeMap_eq B S hS p hx hx' ρ j hρ, ← Category.assoc, hgfac]
      exact schemeMap_over _ hy hx a)
    (by rw [hρ, hgfac])
  exact ⟨l, hl.2⟩

include hp hj hρ in
/-- **The lifting property descends to an open restriction.** If `x` has the lifting property at
the residue point `κ ≫ j`, then its restriction `x'` has it at `κ`. -/
public theorem liftsAtResiduePoint_restrict
    (hU : LiftsAtResiduePoint iΛ (p ⋙ Over.post B.inclusion) U x hx (κ ≫ j)) :
    LiftsAtResiduePoint iΛ (p ⋙ Over.post B.inclusion) U' x' hx' κ := by
  intro A₀ B₀ f hf y z hy hz i hi a ha
  have ha₁ : Spec.map (CommRingCat.ofHom (residueMap A₀)) ≫
      schemeMap _ hy hx (a ≫ ρ) = κ ≫ j := by
    rw [schemeMap_comp _ hy hx' hx a ρ, hρ, ← Category.assoc, ha]
  obtain ⟨b₁, hb₁⟩ := hU A₀ B₀ f hf y z hy hz i hi (a ≫ ρ) ha₁
  have hcomp : Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ schemeMap _ hz hx b₁ =
      schemeMap _ hy hx' a ≫ j := by
    rw [← hi, ← schemeMap_comp _ hy hz hx i b₁, hb₁, schemeMap_comp _ hy hx' hx a ρ, hρ]
  have hrange : Set.range (schemeMap _ hz hx b₁).base ⊆ Set.range j.base :=
    range_subset_range_of_comp _ _ _ _ hcomp (IsLocalRing.closedPoint (A₀ : Type u))
      (subsingleton_spec_of_isArtinianRing (B₀ : Type u))
  obtain ⟨l, hl⟩ := exists_comp_eq_of_range_subset B S hS p hx hx' ρ j hp hj hρ hz b₁ hrange
  refine ⟨l, ?_⟩
  have hstep : schemeMap _ hy hx' a ≫ j = schemeMap _ hy hx (a ≫ ρ) := by
    rw [← hρ, ← schemeMap_comp _ hy hx' hx a ρ]
  have key := factor_through_cartesian_schemeMap B S hS p hp hy hx' hx ρ (a ≫ ρ)
    (schemeMap _ hy hx' a) (schemeMap_over _ hy hx' a) (by rw [hρ, hstep])
  have h2 : (i ≫ l) ≫ ρ = a ≫ ρ := by rw [Category.assoc, hl, hb₁]
  have h1 : schemeMap _ hy hx' (i ≫ l) = schemeMap _ hy hx' a := by
    rw [← cancel_mono j, ← hρ, ← schemeMap_comp _ hy hx' hx (i ≫ l) ρ,
      ← schemeMap_comp _ hy hx' hx a ρ, h2]
  exact key.unique ⟨h1, h2⟩ ⟨rfl, rfl⟩

include hp hj hρ in
/-- **The lifting property ascends from an open restriction.** If the restriction `x'` has the
lifting property at the residue point `κ`, then `x` has it at `κ ≫ j`. -/
public theorem liftsAtResiduePoint_of_restrict
    (hU' : LiftsAtResiduePoint iΛ (p ⋙ Over.post B.inclusion) U' x' hx' κ) :
    LiftsAtResiduePoint iΛ (p ⋙ Over.post B.inclusion) U x hx (κ ≫ j) := by
  intro A₀ B₀ f hf y z hy hz i hi a ha
  have hrange : Set.range (schemeMap _ hy hx a).base ⊆ Set.range j.base :=
    range_subset_range_of_comp _ _ _ _ ha (IsLocalRing.closedPoint k)
      (subsingleton_spec_of_isArtinianRing (A₀ : Type u))
  obtain ⟨a', ha'⟩ := exists_comp_eq_of_range_subset B S hS p hx hx' ρ j hp hj hρ hy a hrange
  have hstep : schemeMap _ hy hx' a' ≫ j = schemeMap _ hy hx a := by
    rw [← hρ, ← schemeMap_comp _ hy hx' hx a' ρ, ha']
  have ha'res : Spec.map (CommRingCat.ofHom (residueMap A₀)) ≫ schemeMap _ hy hx' a' = κ := by
    rw [← cancel_mono j, Category.assoc, hstep, ha]
  obtain ⟨b', hb'⟩ := hU' A₀ B₀ f hf y z hy hz i hi a' ha'res
  exact ⟨b' ≫ ρ, by rw [← Category.assoc, hb', ha']⟩

include hp hj hρ in
/-- **The lifting property is unchanged by restriction to an open subscheme.** -/
public theorem liftsAtResiduePoint_iff_restrict :
    LiftsAtResiduePoint iΛ (p ⋙ Over.post B.inclusion) U' x' hx' κ ↔
      LiftsAtResiduePoint iΛ (p ⋙ Over.post B.inclusion) U x hx (κ ≫ j) :=
  ⟨liftsAtResiduePoint_of_restrict B S hS p hp iΛ hx hx' ρ j hj hρ κ,
    liftsAtResiduePoint_restrict B S hS p hp iΛ hx hx' ρ j hj hρ κ⟩

end Restriction

/-! ### The residue field at a point of the chart, as an algebra over the chart -/

section ChartAlgebra

variable {Λ : Type u} [CommRing Λ] {S : Scheme.{u}} (iΛ : Spec (CommRingCat.of Λ) ⟶ S)
  [IsOpenImmersion iΛ] (U : Over S) (u : U.left)

omit [IsOpenImmersion iΛ] in
/-- **Two ring maps into one ring with the same spectrum over a monomorphic chart agree.** -/
public theorem ringHom_eq_of_specMap_comp_eq {C : Type u} [CommRing C] [Mono iΛ]
    (g g' : Λ →+* C)
    (h : Spec.map (CommRingCat.ofHom g) ≫ iΛ = Spec.map (CommRingCat.ofHom g') ≫ iΛ) :
    g = g' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono iΛ).mp h))

variable (H : Set.range (U.left.fromSpecResidueField u ≫ U.hom).base ⊆ Set.range iΛ.base)

/-- The morphism `Spec κ(u) ⟶ Spec Λ` through which the residue point of `u` factors, for a
point `u` whose image in `S` lies in the chart. -/
public def chartResiduePoint :
    Spec (CommRingCat.of (U.left.residueField u : Type u)) ⟶ Spec (CommRingCat.of Λ) :=
  IsOpenImmersion.lift iΛ (U.left.fromSpecResidueField u ≫ U.hom) H

/-- The factorization that `Deformation.Artin.chartResiduePoint` is defined by. -/
public theorem chartResiduePoint_comp :
    chartResiduePoint iΛ U u H ≫ iΛ = U.left.fromSpecResidueField u ≫ U.hom :=
  IsOpenImmersion.lift_fac _ _ _

/-- **The residue field at a point of the chart is an algebra over the chart.** The structure
map is the ring map underlying `Deformation.Artin.chartResiduePoint`. This attaches a structure
to a residue field which carries none, so it replaces nothing. -/
@[instance_reducible]
public def chartResidueAlgebra : Algebra Λ (U.left.residueField u) :=
  (ringHom_of_schemeMap (chartResiduePoint iΛ U u H)).toAlgebra

/-- The structure map of `Deformation.Artin.chartResidueAlgebra`, read through the chart, is
the residue point of `u` followed by the structure morphism. -/
public theorem algebraMap_chartResidueAlgebra :
    letI := chartResidueAlgebra iΛ U u H
    Spec.map (CommRingCat.ofHom (algebraMap Λ (U.left.residueField u))) ≫ iΛ =
      U.left.fromSpecResidueField u ≫ U.hom := by
  let := chartResidueAlgebra iΛ U u H
  have h : Spec.map (CommRingCat.ofHom (algebraMap Λ (U.left.residueField u : Type u))) =
      chartResiduePoint iΛ U u H :=
    specMap_ringHom_of_schemeMap (chartResiduePoint iΛ U u H)
  exact (congrArg (fun m => m ≫ iΛ) h).trans (chartResiduePoint_comp iΛ U u H)

variable {X : Type v} [Category.{w} X]

/-- **Versality read over a chart.** This is
`Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint_affineOpen` with the point of the chart
below `u` supplied: it is the image of the closed point under the spectrum of the structure
map. -/
public theorem isVersalAt_iff_liftsAtResiduePoint_chart (q : X ⥤ Over S) (x : X)
    (hx : q.obj x = U) [Algebra Λ (U.left.residueField u)]
    (hcompat : Spec.map (CommRingCat.ofHom (algebraMap Λ (U.left.residueField u))) ≫ iΛ =
      U.left.fromSpecResidueField u ≫ U.hom) :
    IsVersalAt U q u x hx ↔
      LiftsAtResiduePoint (Λ := Λ) (k := U.left.residueField u) iΛ q U x hx
        (U.left.fromSpecResidueField u) :=
  isVersalAt_iff_liftsAtResiduePoint_affineOpen iΛ U q u x hx
    ((Spec.map (CommRingCat.ofHom (algebraMap Λ (U.left.residueField u : Type u)))).base
      (IsLocalRing.closedPoint (U.left.residueField u : Type u)))
    (congrArg (fun m : Spec (CommRingCat.of (U.left.residueField u : Type u)) ⟶ S =>
      m.base (IsLocalRing.closedPoint (U.left.residueField u : Type u))) hcompat) hcompat

end ChartAlgebra

/-! ### Versality at a point is unchanged by restriction to an open subscheme -/

section VersalRestriction

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  {Λ : Type u} [CommRing Λ] (iΛ : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion iΛ]
  {U U' : Over S} {x x' : X}
  (hx : (p ⋙ Over.post B.inclusion).obj x = U)
  (hx' : (p ⋙ Over.post B.inclusion).obj x' = U')
  (ρ : x' ⟶ x) (j : U'.left ⟶ U.left) (hj : IsOpenImmersion j)
  (hρ : schemeMap (p ⋙ Over.post B.inclusion) hx' hx ρ = j)

include hp hj hρ in
/-- **Versality is unchanged by restriction to an open subscheme.** Let `x'` be an object over
an open `U'` of `U` with an arrow `x' ⟶ x` lying over the open immersion `j`. Then `x` is versal
at `j u` exactly when `x'` is versal at `u`.

Both sides are read as the lifting property over a common affine chart `Spec Λ ⊆ S` containing
the images of the two residue points — which is the same point of `S` — so the local rings of
`S` never enter; the two residue fields are then identified by the canonical isomorphism of an
open immersion, whose `Λ`-linearity is forced by `Spec Λ ⟶ S` being a monomorphism. -/
public theorem isVersalAt_iff_restrict (u : U'.left)
    (H : Set.range (U.left.fromSpecResidueField (j.base u) ≫ U.hom).base ⊆ Set.range iΛ.base)
    (H' : Set.range (U'.left.fromSpecResidueField u ≫ U'.hom).base ⊆ Set.range iΛ.base) :
    IsVersalAt U' (p ⋙ Over.post B.inclusion) u x' hx' ↔
      IsVersalAt U (p ⋙ Over.post B.inclusion) (j.base u) x hx := by
  have := hj
  have hjU : j ≫ U.hom = U'.hom := comp_hom_eq_of_schemeMap_eq B S hS p hx hx' ρ j hρ
  let algU : Algebra Λ (U.left.residueField (j.base u)) := chartResidueAlgebra iΛ U (j.base u) H
  let algU' : Algebra Λ (U'.left.residueField u) := chartResidueAlgebra iΛ U' u H'
  have hcU := algebraMap_chartResidueAlgebra iΛ U (j.base u) H
  have hcU' := algebraMap_chartResidueAlgebra iΛ U' u H'
  have hres : Spec.map (j.residueFieldMap u) ≫ U.left.fromSpecResidueField (j.base u) =
      U'.left.fromSpecResidueField u ≫ j :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField j u
  -- the residue field isomorphism of the open immersion is `Λ`-linear
  have hlin : ∀ l : Λ, (j.residueFieldMap u).hom
      (algebraMap Λ (U.left.residueField (j.base u) : Type u) l) =
      algebraMap Λ (U'.left.residueField u : Type u) l := by
    have h : ((j.residueFieldMap u).hom.comp
        (algebraMap Λ (U.left.residueField (j.base u) : Type u))) =
        algebraMap Λ (U'.left.residueField u : Type u) := by
      refine ringHom_eq_of_specMap_comp_eq iΛ _ _ ?_
      have h₁ : CommRingCat.ofHom ((j.residueFieldMap u).hom.comp
          (algebraMap Λ (U.left.residueField (j.base u) : Type u))) =
          CommRingCat.ofHom (algebraMap Λ (U.left.residueField (j.base u) : Type u)) ≫
            j.residueFieldMap u := rfl
      rw [h₁, Spec.map_comp, Category.assoc, hcU, ← Category.assoc, hres, Category.assoc, hjU,
        hcU']
    exact RingHom.congr_fun h
  let e : (U.left.residueField (j.base u) : Type u) ≃ₐ[Λ] (U'.left.residueField u : Type u) :=
    AlgEquiv.ofRingEquiv (f := (asIso (j.residueFieldMap u)).commRingCatIsoToRingEquiv) hlin
  have heq : U'.left.fromSpecResidueField u ≫ j =
      Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom) ≫
        U.left.fromSpecResidueField (j.base u) := hres.symm
  rw [isVersalAt_iff_liftsAtResiduePoint_chart iΛ U' u (p ⋙ Over.post B.inclusion) x' hx' hcU',
    isVersalAt_iff_liftsAtResiduePoint_chart iΛ U (j.base u) (p ⋙ Over.post B.inclusion) x hx hcU]
  refine Iff.trans (liftsAtResiduePoint_iff_restrict (k := (U'.left.residueField u : Type u))
    B S hS p hp iΛ hx hx' ρ j hj hρ (U'.left.fromSpecResidueField u)) ?_
  refine Iff.trans ?_ (liftsAtResiduePoint_iff_changeResidueField e iΛ
    (p ⋙ Over.post B.inclusion) U x hx (U.left.fromSpecResidueField (j.base u))).symm
  rw [heq]

end VersalRestriction

end Deformation.Artin

end
