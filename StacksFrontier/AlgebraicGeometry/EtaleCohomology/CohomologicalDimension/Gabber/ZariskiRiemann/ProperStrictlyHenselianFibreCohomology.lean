module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperGeometricFibreStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianSmallEtaleHigherDirectImageStalk
public import StacksFrontier.CategoryTheory.Sites.Point.UliftFiber
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology

/-!
# Cohomology of a proper scheme over a strictly henselian local ring is that of its closed fibre

Let `B` be a strictly henselian local ring, `f : Y ⟶ Spec B` a proper morphism and
`x : Spec Ω ⟶ Spec B` a geometric point over the closed point, `Ω` algebraically closed, with
geometric closed fibre `Y_Ω = Y ×_{Spec B} Spec Ω`. For every torsion abelian sheaf `G` on
`Y_étale` and every `q`,

`H^q(Y, G) ≅ H^q(Y_Ω, G|_{Y_Ω})`.

This is the consequence of the proper base change theorem used in the first step of Gabber's
Zariski–Riemann proof of the bound `cd(Frac B) ≤ 2 dim B - 1` (Travaux de Gabber, Exposé XVIII-A,
last remark of §2): for `Y` proper birational over `Spec B` with closed fibre `Y₀`, cohomology of
`Y` is cohomology of `Y₀`. (Over a henselian, not strictly henselian, local ring the same holds
with `Y₀` in place of `Y_Ω`: [Stacks, Tag 0A0C]; only the strictly henselian case is needed here,
and its proof is shorter.)

The proof composes three identifications of the stalk of `R^q f_* G` at `x`:

* it is `H^q(Y, G)`, because over a strictly henselian base the étale neighbourhoods of `x` have
  an initial object
  (`Stacks.EtaleCohomology.smallEtaleHigherDirectImageStalkIsoCohomologyClosedPoint`,
  [Stacks, Tag 03Q9] at a strictly henselian base);
* the stalk at the universe lift of the point is the stalk at the point
  (`CategoryTheory.GrothendieckTopology.Point.sheafFiberUliftIso`);
* it is `H^q(Y_Ω, G|_{Y_Ω})` by proper base change
  (`Stacks.EtaleCohomology.etaleAbelianSheafFiberRightDerivedDirectImageIsoOfIsProper`,
  [Stacks, Tag 0DDF] (1), from [Stacks, Tag 095T]).

## Main results

* `Stacks.EtaleCohomology.sheafHIsoGeometricClosedFibreOfIsProper` — the isomorphism
  `H^q(Y, G) ≅ H^q(Y_Ω, G|_{Y_Ω})`.
* `Stacks.EtaleCohomology.subsingleton_sheafH_iff_geometricClosedFibre_of_isProper` — vanishing
  of `H^q(Y, G)` is vanishing of `H^q(Y_Ω, G|_{Y_Ω})`.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 0A0C](https://stacks.math.columbia.edu/tag/0A0C)
* [Stacks Project, Tag 0DDF](https://stacks.math.columbia.edu/tag/0DDF)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

variable {B : Type u} [CommRing B] [StrictlyHenselianLocalRing B] {Y : Scheme.{u}}
  (f : Y ⟶ Spec (.of B)) [IsProper f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (x : Spec (.of Ω) ⟶ Spec (.of B)) (hx : x (default : Spec (.of Ω)) = IsLocalRing.closedPoint B)

/-- **Cohomology of a proper scheme over a strictly henselian local ring is cohomology of its
geometric closed fibre.** For `B` strictly henselian local, `f : Y ⟶ Spec B` proper, a geometric
point `x : Spec Ω ⟶ Spec B` over the closed point and a torsion abelian sheaf `G` on `Y_étale`,
`H^q(Y, G) ≅ H^q(Y ×_{Spec B} Spec Ω, G|)`. Both sides are the stalk of `R^q f_* G` at `x`: the
left by [Stacks, Tag 03Q9] at a strictly henselian base, the right by proper base change
([Stacks, Tag 0DDF] (1)). -/
def sheafHIsoGeometricClosedFibreOfIsProper (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology G) (q : ℕ) :
    AddCommGrpCat.of (Sheaf.H.{u + 1} G q) ≅
      AddCommGrpCat.of
        (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (pullback.fst f x)).obj G) q) :=
  ((Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{0, u, u + 1}
      Y.smallEtaleTopology q).app G).symm ≪≫
    (smallEtaleHigherDirectImageStalkIsoCohomologyClosedPoint f x hx G q).symm ≪≫
    (GrothendieckTopology.Point.sheafFiberUliftIso.{u, u + 1} (pointSmallEtale x)
      (((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj G)).symm ≪≫
    etaleAbelianSheafFiberRightDerivedDirectImageIsoOfIsProper f x G hG q

include hx in
/-- **Vanishing on `Y` is vanishing on the geometric closed fibre**, for `Y` proper over a strictly
henselian local ring and torsion coefficients. -/
theorem subsingleton_sheafH_iff_geometricClosedFibre_of_isProper
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology G) (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} G q) ↔
      Subsingleton
        (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (pullback.fst f x)).obj G) q) := by
  exact (sheafHIsoGeometricClosedFibreOfIsProper f x hx G hG q).addCommGroupIsoToAddEquiv
    |>.toEquiv.subsingleton_congr

end Stacks.EtaleCohomology

end
