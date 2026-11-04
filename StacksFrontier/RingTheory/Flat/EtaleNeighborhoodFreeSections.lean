module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.RingTheory.Module.Kaplansky

/-!
# Free sections over the local ring of an elementary étale neighbourhood

Two statements about modules of sections over the local ring of a scheme at a point, whose
hypotheses provide sections that are *projective* over that local ring, conclude that those
sections are *free*: a projective module over a local ring is free.

## Main results

* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections_of_projective_sections`:
  if, after base change to the local scheme of an affine elementary étale neighbourhood, a module
  has projective sections on an affine neighbourhood of a lifted point, then those sections are
  free.
* `AlgebraicGeometry.exists_etale_neighborhood_with_free_globalSections_of_projective`: if a
  pointed affine étale neighbourhood over the local ring of an elementary étale neighbourhood of
  the base has projective global sections, then those global sections are free.

## References

* [Stacks Project, Tag 05MF](https://stacks.math.columbia.edu/tag/05MF)
* [Stacks Project, Tag 05KY](https://stacks.math.columbia.edu/tag/05KY)
* [Stacks Project, Tag 0593](https://stacks.math.columbia.edu/tag/0593)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A projective module over a local ring is free, with the module structure as an explicit
argument. -/
private theorem free_of_projective_module (R : Type*) [CommRing R] [IsLocalRing R] (M : Type*)
    [AddCommGroup M] (inst : Module R M) (h : @Module.Projective R _ M _ inst) :
    @Module.Free R M _ _ inst :=
  @Module.free_of_projective_of_isLocalRing R M _ _ inst _ h

/-- If, after base change to the local scheme of an affine elementary étale neighbourhood of the
image point, the module `F` has projective sections on an affine neighbourhood of a lifted point,
then those sections are free over the local ring. -/
theorem exists_elementaryEtaleNeighborhood_free_sections_of_projective_sections
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    (hproj : ∃ (N : EtaleNeighborhood S (f x)),
      N.IsElementary ∧ IsAffine N.scheme ∧
        let g := N.scheme.fromSpecStalk N.point ≫ N.toBase
        let P := pullback f g
        ∃ (x' : P) (W : P.Opens),
          pullback.fst f g x' = x ∧
            N.scheme.fromSpecStalk N.point (pullback.snd f g x') = N.point ∧
            IsAffineOpen W ∧ x' ∈ W ∧
              let F' := (Scheme.Modules.pullback (pullback.fst f g)).obj F
              letI : Module (N.scheme.presheaf.stalk N.point) Γ(F', W) :=
                Module.compHom Γ(F', W)
                  (((Scheme.ΓSpecIso (.of (N.scheme.presheaf.stalk N.point))).inv ≫
                    (pullback.snd f g).appLE ⊤ W (by simp)).hom)
              Module.Projective (N.scheme.presheaf.stalk N.point) Γ(F', W)) :
    ∃ (N : EtaleNeighborhood S (f x)),
      N.IsElementary ∧ IsAffine N.scheme ∧
        let g := N.scheme.fromSpecStalk N.point ≫ N.toBase
        let P := pullback f g
        ∃ (x' : P) (W : P.Opens),
          pullback.fst f g x' = x ∧
            N.scheme.fromSpecStalk N.point (pullback.snd f g x') = N.point ∧
            IsAffineOpen W ∧ x' ∈ W ∧
              let F' := (Scheme.Modules.pullback (pullback.fst f g)).obj F
              letI : Module (N.scheme.presheaf.stalk N.point) Γ(F', W) :=
                Module.compHom Γ(F', W)
                  (((Scheme.ΓSpecIso (.of (N.scheme.presheaf.stalk N.point))).inv ≫
                    (pullback.snd f g).appLE ⊤ W (by simp)).hom)
              Module.Free (N.scheme.presheaf.stalk N.point) Γ(F', W) := by
  obtain ⟨N, helem, haffine, x', W, hfst, hsnd, hW, hxW, hP⟩ := hproj
  exact ⟨N, helem, haffine, x', W, hfst, hsnd, hW, hxW, free_of_projective_module _ _ _ hP⟩

/-- If a pointed affine étale neighbourhood over the local ring of an elementary étale
neighbourhood of the base has projective global sections of the pullback of `F`, then those global
sections are free over the local ring. -/
theorem exists_etale_neighborhood_with_free_globalSections_of_projective
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    (hproj : ∃ (U : EtaleNeighborhood S (f x)) (_ : U.IsElementary)
      (X' : Scheme.{u}) (x' : X') (g : X' ⟶ X)
      (q : X' ⟶ Spec (.of (U.scheme.presheaf.stalk U.point)))
      (_ : g x' = x)
      (_ : q x' = IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point))
      (hcomm : g ≫ f = q ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase)
      (_ : Etale (pullback.lift g q hcomm))
      (_ : IsIso (g.residueFieldMap x'))
      (_ : IsAffine X')
      (_ : FinitePresentation q)
      (_ : ((Scheme.Modules.pullback g).obj F).IsFinitePresentation),
      letI : Module (U.scheme.presheaf.stalk U.point)
          Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
        Module.compHom _
          ((Scheme.ΓSpecIso (.of (U.scheme.presheaf.stalk U.point))).inv ≫ q.appTop).hom
      Module.Projective (U.scheme.presheaf.stalk U.point)
        Γ((Scheme.Modules.pullback g).obj F, ⊤)) :
    ∃ (U : EtaleNeighborhood S (f x)) (_ : U.IsElementary)
      (X' : Scheme.{u}) (x' : X') (g : X' ⟶ X)
      (q : X' ⟶ Spec (.of (U.scheme.presheaf.stalk U.point)))
      (_ : g x' = x)
      (_ : q x' = IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point))
      (hcomm : g ≫ f = q ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase)
      (_ : Etale (pullback.lift g q hcomm))
      (_ : IsIso (g.residueFieldMap x'))
      (_ : IsAffine X')
      (_ : FinitePresentation q)
      (_ : ((Scheme.Modules.pullback g).obj F).IsFinitePresentation),
      letI : Module (U.scheme.presheaf.stalk U.point)
          Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
        Module.compHom _
          ((Scheme.ΓSpecIso (.of (U.scheme.presheaf.stalk U.point))).inv ≫ q.appTop).hom
      Module.Free (U.scheme.presheaf.stalk U.point)
        Γ((Scheme.Modules.pullback g).obj F, ⊤) := by
  obtain ⟨U, helem, X', x', g, q, hgx, hqx, hcomm, hetale, hres, haffine, hfp, hmfp, hP⟩ := hproj
  exact ⟨U, helem, X', x', g, q, hgx, hqx, hcomm, hetale, hres, haffine, hfp, hmfp,
    free_of_projective_module _ _ _ hP⟩

end AlgebraicGeometry

end
