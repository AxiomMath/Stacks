module

public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningCoherentSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAbelian

/-!
# Detecting vanishing and surjectivity on a tower of thickenings

Let `ι n : Z n ⟶ X` be a tower of closed subspaces of an algebraic space and `Φ` the restriction
of coherent `𝒪_X`-modules to the tower. Wherever `Φ` is faithful — which Grothendieck's
existence theorem provides for modules with proper support — vanishing and surjectivity can be
read on the tower: a coherent module whose restrictions to all the `Z n` vanish is zero, and a map
of coherent modules is surjective as soon as its restrictions to all the `Z n` are.

## Main results

* `AlgebraicGeometry.Space.isZero_of_injective_thickeningRestriction_map`: a coherent module whose
  restrictions to the tower vanish, and on which `Φ` is injective on endomorphisms, is zero.
* `AlgebraicGeometry.Space.epi_of_epi_modulePullback_map`: a map of coherent modules whose
  restrictions to the tower are surjective is surjective, provided `Φ` is injective on the
  endomorphisms of its cokernel.

## References

* [Stacks Project, Tag 08BG](https://stacks.math.columbia.edu/tag/08BG)
* [Stacks Project, Tag 08B5](https://stacks.math.columbia.edu/tag/08B5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {Z : ℕ → AlgebraicSpaces B S hS} (ι : ∀ n, Z n ⟶ X)
  (t : ∀ n, Z n ⟶ Z (n + 1)) (hι : ∀ n, t n ≫ ι (n + 1) = ι n)
  (hZ : ∀ n, HasEtaleLocalProperty B S hS (Z n).1 (fun V : Scheme.{u} => IsLocallyNoetherian V))

/-- **A coherent module whose restrictions to the tower vanish is zero**, as soon as the
restriction to the tower is injective on its endomorphisms. -/
theorem isZero_of_injective_thickeningRestriction_map (C : CoherentModules.{u, u} B S hS X.1 X.2)
    (hinj : Function.Injective
      (fun a : C ⟶ C => (thickeningRestriction B S hS ι t hι hZ).map a))
    (hzero : ∀ n, IsZero ((modulePullback B S hS (ι n)).obj C.obj)) :
    IsZero C.obj := by
  have h : (𝟙 C : C ⟶ C) = 0 := hinj (TowerSystem.hom_ext fun n => (hzero n).eq_of_src _ _)
  refine (IsZero.iff_id_eq_zero _).2 ?_
  exact congrArg (fun a : C ⟶ C => a.hom) h

/-- **A map of coherent modules whose restrictions to the tower are surjective is surjective**,
provided the restriction to the tower is injective on the endomorphisms of a coherent cokernel
`C`: the inverse images preserve cokernels, so `C` restricts to zero on the tower. -/
theorem epi_of_epi_modulePullback_map {M N C : CoherentModules.{u, u} B S hS X.1 X.2} (s : M ⟶ N)
    (π : N.obj ⟶ C.obj) (hw : s.hom ≫ π = 0) (hπ : IsColimit (CokernelCofork.ofπ π hw))
    (hinj : Function.Injective
      (fun a : C ⟶ C => (thickeningRestriction B S hS ι t hι hZ).map a))
    (hepi : ∀ n, Epi ((modulePullback B S hS (ι n)).map s.hom)) :
    Epi s.hom := by
  have hzero := isZero_of_injective_thickeningRestriction_map B S hS ι t hι hZ C hinj fun n => by
    have := (modulePullbackAdjunction B S hS (ι n)).leftAdjoint_preservesColimits
    have hn := hepi n
    exact CokernelCofork.IsColimit.isZero_of_epi
      (isColimitCoforkMapOfIsColimit' (modulePullback B S hS (ι n)) hw hπ)
  exact Preadditive.epi_of_isZero_cokernel' _ hπ hzero

end AlgebraicGeometry.Space

end
