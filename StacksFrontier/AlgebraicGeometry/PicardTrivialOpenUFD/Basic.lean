module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Triviality of the Picard group of an open subscheme, and the affine-space case

Stacks Tag 0BDA has two parts: the Picard group of an open subscheme of `Spec R` is trivial
when `R` is a unique factorization domain, and the same for an open subscheme of affine space
over such an `R`. This file proves that part (2) follows from part (1), with triviality of a
Picard group expressed directly: every invertible `𝒪_X`-module is isomorphic to `𝒪_X`.

## Main definitions

* `Stacks.PicardTrivialOpenUFD.HasTrivialPicard`: every invertible `𝒪_X`-module on `X` is
  isomorphic to `𝒪_X`.

## Main results

* `Stacks.PicardTrivialOpenUFD.hasTrivialPicard_of_iso`: triviality transports along an
  isomorphism of schemes.
* `Stacks.PicardTrivialOpenUFD.part2_of_part1`: Tag 0BDA part (2) from part (1): if every open
  subscheme of the spectrum of a domain with unique factorization has trivial Picard group, then
  so does every open subscheme of affine space over such a ring.

## References

* [Stacks Project, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.PicardTrivialOpenUFD

/-- **The Picard group of `X` is trivial**: every invertible `𝒪_X`-module is isomorphic to the
structure sheaf. -/
def HasTrivialPicard (X : Scheme.{u}) : Prop :=
  ∀ L : X.Modules, Stacks.Ample.IsInvertibleModule X L →
    Nonempty (L ≅ Stacks.Ample.unitModule X)

/-- **The pullback of `𝒪_Y` along `f : X ⟶ Y` is `𝒪_X`**, for `Scheme.Modules.pullback`. -/
def pullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (Stacks.Ample.unitModule Y) ≅
      Stacks.Ample.unitModule X :=
  RingedSpaceModuleAdjunction.modulePullbackObjUnitIso f.toLRSHom.toShHom

/-- Pulling a module on `Y` back along `e.hom` and then along `e.inv` returns it. -/
def pullbackInvPullbackHomIso {X Y : Scheme.{u}} (e : X ≅ Y) (L : Y.Modules) :
    (Scheme.Modules.pullback e.inv).obj ((Scheme.Modules.pullback e.hom).obj L) ≅ L :=
  (Scheme.Modules.pullbackComp e.inv e.hom).app L ≪≫
    (Scheme.Modules.pullbackCongr (by simp : e.inv ≫ e.hom = 𝟙 Y)).app L ≪≫
    (Scheme.Modules.pullbackId Y).app L

/-- **Triviality of the Picard group transports along an isomorphism of schemes.** -/
theorem hasTrivialPicard_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (h : HasTrivialPicard X) : HasTrivialPicard Y := by
  intro L hL
  obtain ⟨g⟩ := h ((Scheme.Modules.pullback e.hom).obj L) <| by
    change Stacks.Ample.IsInvertibleModule X
      ((RingedSpaceModuleAdjunction.modulePullback e.hom.toLRSHom.toShHom).obj L)
    infer_instance
  exact ⟨(pullbackInvPullbackHomIso e L).symm ≪≫
    (Scheme.Modules.pullback e.inv).mapIso g ≪≫ pullbackUnitIso e.inv⟩

/-- **Stacks Project, Tag 0BDA, part (2) from part (1).** If every open subscheme of the
spectrum of a domain with unique factorization has trivial Picard group, then so does every
open subscheme of affine space over such a ring. -/
theorem part2_of_part1
    (h : ∀ (S : Type u) [CommRing S] [IsDomain S] [UniqueFactorizationMonoid S]
      (V : (Spec (.of S)).Opens), HasTrivialPicard V.toScheme)
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (ι : Type u) (U : (AffineSpace ι (Spec (.of R))).Opens) :
    HasTrivialPicard U.toScheme := by
  let f := (AffineSpace.SpecIso ι (CommRingCat.of R)).inv
  exact hasTrivialPicard_of_iso (Scheme.Hom.preimageIso f U)
    (h (MvPolynomial ι R) ((TopologicalSpace.Opens.map f.base).obj U))

end Stacks.PicardTrivialOpenUFD
