module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AlgebraSiteCartesianBase
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesOnAffineSite

/-!
# Flat coverings of the algebra site are faithfully flat on the tautological rings

The cartesian sheaf criterion of
`Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_refinements'` asks, for each finite
covering family of the site which is flat on spectra, that the product of the restriction maps
of the structure presheaf of rings be faithfully flat.  For the site
`Stacks.Adequate.algebraSite` of the `A`-algebras of a big site that structure presheaf is the
tautological one, `Stacks.Adequate.algebraSiteRings`, whereas the flatness hypothesis is a
statement about `Stacks.Adequate.algebraSiteScheme`.

This file supplies the hypothesis.  The scheme-side statement is
`AlgebraicGeometry.Scheme.faithfullyFlat_pi_appTop`, and all that is needed is to move it across
the comparison `AlgebraicGeometry.Scheme.ΓSpecIso` between an algebra and the global functions on
its spectrum: the two families of ring maps are conjugate by ring isomorphisms, and faithful
flatness is invariant under that.

## Main results

* `Stacks.Adequate.faithfullyFlat_pi_of_ringEquiv` — faithful flatness of a product map is
  unchanged when the source and each factor of the target are replaced by isomorphic rings.
* `Stacks.Adequate.faithfullyFlat_pi_of_spec_flat_cover` — **a finite family of ring maps whose
  spectra are flat and jointly surjective has faithfully flat product map.**
* `Stacks.Adequate.algebraSiteScheme_map_eq` — the spectrum functor of the algebra site is
  `Spec` of the tautological presheaf of rings, on the nose.
* `Stacks.Adequate.algebraSiteScheme_appTop_eq` — the restriction maps of the presheaf of rings
  and the global functions of the spectrum functor agree up to `ΓSpecIso`.
* `Stacks.Adequate.faithfullyFlat_pi_algebraSiteRings_map` — **the product of the restriction
  maps of the tautological rings along a finite flat covering family of the algebra site is
  faithfully flat.**

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Adequate

/-! ### Transporting faithful flatness of a product map along ring isomorphisms -/

/-- Faithful flatness of the product of a family of ring maps `f i : R →+* S i` is unchanged
when the source and each factor of the target are replaced by isomorphic rings, compatibly with
the maps: the two product maps are then conjugate by ring isomorphisms, and
`RingHom.FaithfullyFlat` respects isomorphisms. -/
public theorem faithfullyFlat_pi_of_ringEquiv {I : Type u} {R R' : Type u} [CommRing R]
    [CommRing R'] {S S' : I → Type u} [∀ i, CommRing (S i)] [∀ i, CommRing (S' i)]
    (f : ∀ i, R →+* S i) (f' : ∀ i, R' →+* S' i) (e : R' ≃+* R) (e' : ∀ i, S i ≃+* S' i)
    (hcomp : ∀ (i : I) (x : R'), f' i x = e' i (f i (e x)))
    (H : (RingHom.pi f).FaithfullyFlat) : (RingHom.pi f').FaithfullyFlat := by
  have hpi : RingHom.pi f' =
      (RingEquiv.piCongrRight e').toRingHom.comp ((RingHom.pi f).comp e.toRingHom) :=
    RingHom.ext fun x => funext fun i => hcomp i x
  rw [hpi]
  exact RingHom.FaithfullyFlat.respectsIso.1 _ _
    (RingHom.FaithfullyFlat.respectsIso.2 _ _ H)

/-- The global sections of `Spec.map f` are `f` conjugated by the `ΓSpecIso` comparisons. -/
private theorem appTop_spec_map_eq {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (Spec.map f).appTop = (Scheme.ΓSpecIso R).hom ≫ f ≫ (Scheme.ΓSpecIso S).inv := by
  rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- **A finite family of ring maps out of `R` whose spectra are flat over `Spec R` and jointly
surjective onto it has faithfully flat product map.**  This is
`AlgebraicGeometry.Scheme.faithfullyFlat_pi_appTop` read through `ΓSpecIso`. -/
public theorem faithfullyFlat_pi_of_spec_flat_cover {I : Type u} [Finite I]
    {R : CommRingCat.{u}} {S : I → CommRingCat.{u}} (g : ∀ i, R ⟶ S i)
    (hflat : ∀ i, Flat (Spec.map (g i)))
    (hcover : ∀ x : Spec R, ∃ i, ∃ y : Spec (S i), (Spec.map (g i)) y = x) :
    (RingHom.pi fun i => (g i).hom).FaithfullyFlat := by
  let _ (i : I) : Flat (Spec.map (g i)) := hflat i
  have H : (RingHom.pi fun i => (Spec.map (g i)).appTop.hom).FaithfullyFlat :=
    Scheme.faithfullyFlat_pi_appTop (fun i => Spec (S i)) (fun i => Spec.map (g i)) hcover
  refine faithfullyFlat_pi_of_ringEquiv _ _
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
    (fun i => (Scheme.ΓSpecIso (S i)).commRingCatIsoToRingEquiv) (fun i x => ?_) H
  have h : g i = (Scheme.ΓSpecIso R).inv ≫ (Spec.map (g i)).appTop ≫
      (Scheme.ΓSpecIso (S i)).hom := by
    rw [appTop_spec_map_eq]; simp
  exact congrArg (fun k : R ⟶ S i => k.hom x) h

/-! ### The algebra site of a big site -/

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- The spectrum functor of the algebra site is `Spec` applied to the tautological presheaf of
commutative rings, on the nose. -/
public theorem algebraSiteScheme_map_eq {X Y : algebraSite B} (g : X ⟶ Y) :
    (algebraSiteScheme B).map g = Spec.map ((algebraSiteRings B).map g.op) := rfl

/-- The restriction maps of the tautological presheaf of rings of the algebra site and the global
functions of its spectrum functor agree up to `AlgebraicGeometry.Scheme.ΓSpecIso`.  This is the
comparison `Stacks.Adequate.affineRingMap` read on global sections, and it is what transports a
flatness statement about the scheme side to the ring side. -/
public theorem algebraSiteScheme_appTop_eq {X Y : algebraSite B} (g : X ⟶ Y) :
    ((algebraSiteScheme B).map g).appTop =
      (Scheme.ΓSpecIso ((algebraSiteRings B).obj (op Y))).hom ≫
        (algebraSiteRings B).map g.op ≫
          (Scheme.ΓSpecIso ((algebraSiteRings B).obj (op X))).inv := by
  exact appTop_spec_map_eq _

/-- **The product of the restriction maps of the tautological presheaf of rings of the algebra
site along a finite family which is a flat covering of spectra is faithfully flat.**  This is the
ring-side hypothesis of the cartesian sheaf criterion for the algebra site. -/
public theorem faithfullyFlat_pi_algebraSiteRings_map
    {U : algebraSite B} (E : CategoryTheory.PreZeroHypercover.{u} U) (hfin : Finite E.I₀)
    (hE : (E.map (algebraSiteScheme B)).presieve₀ ∈
      AlgebraicGeometry.Scheme.precoverage @AlgebraicGeometry.Flat
        ((algebraSiteScheme B).obj U)) :
    (RingHom.pi (fun k => ((algebraSiteRings B).map (E.f k).op).hom)).FaithfullyFlat := by
  have _ : Finite E.I₀ := hfin
  obtain ⟨hcover, hflat⟩ :=
    (Scheme.presieve₀_mem_precoverage_iff (E.map (algebraSiteScheme B))).mp hE
  exact faithfullyFlat_pi_of_spec_flat_cover (fun k => (algebraSiteRings B).map (E.f k).op)
    (fun k => hflat k) (fun x => hcover x)

end Stacks.Adequate

end
