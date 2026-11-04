module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc

/-!
# The direct image along a morphism that equals a composite

Stacks 03LU compares the iterated direct image `f_* ∘ g_*` of `𝒪`-modules with the direct image
`(f ≫ g)_*` along the composite.  This file records that comparison for a morphism `k` which is
only *equal* to `f ≫ g`, taking `f ≫ g = k` as a hypothesis, together with its coherences; it is
the direct-image analogue of `AlgebraicGeometry.Space.modulePullbackTriangle`.

## Main definitions

* `AlgebraicGeometry.Space.modulePushforwardTriangle`: for `hk : f ≫ g = k`, the comparison
  `f_* ⋙ g_* ≅ k_*`.
* `AlgebraicGeometry.Space.modulePushforwardTriangleApp`: the same at a single module, with its
  type written as `g_*(f_*N) ≅ k_*N` rather than as `(f_* ⋙ g_*).obj N ≅ k_*.obj N`.
* `AlgebraicGeometry.Space.modulePushforwardSquare`: the comparison of the two iterated direct
  images along the two sides of a commuting square.

## Main results

* `AlgebraicGeometry.Space.modulePushforwardTriangle_rfl`: at the composite itself the
  comparison is `AlgebraicGeometry.Space.modulePushforwardCompIso`.
* `AlgebraicGeometry.Space.modulePushforwardTriangle_congr` and
  `AlgebraicGeometry.Space.modulePushforwardTriangle_congr_left`: the comparison depends on the
  morphism and not on its presentation as a composite.
* `AlgebraicGeometry.Space.modulePushforwardTriangle_assoc`: **the associativity coherence**, for
  composites presented as single morphisms, and
  `AlgebraicGeometry.Space.modulePushforwardTriangle_hom_app_assoc`, the same read at a single
  module.

## Implementation notes

Composites are presented as single named morphisms so that the identification of the spellings
`(f ≫ g) ≫ h` and `f ≫ (g ≫ h)` never enters a statement: it is cheap as an equality of functors
and very expensive inside a composition of morphisms of `𝒪`-modules (see the implementation notes
of `StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackPresentationTail.lean`).

The orientation is the one of `AlgebraicGeometry.Space.modulePushforwardCompIso`, from the
iterated direct image to the direct image along the single morphism.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {V W X Y Z : AlgebraicSpaces B S hS}

/-- The iterated direct image along `f` and then `g`, compared with the direct image along a
*single* morphism `k` with `f ≫ g = k`. -/
def modulePushforwardTriangle (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z} (hk : f ≫ g = k) :
    modulePushforward B S hS f ⋙ modulePushforward B S hS g ≅ modulePushforward B S hS k :=
  modulePushforwardCompIso B S hS f g ≪≫ eqToIso (congrArg (modulePushforward B S hS) hk)

/-- `AlgebraicGeometry.Space.modulePushforwardTriangle` written out. -/
theorem modulePushforwardTriangle_eq {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z} (hk : f ≫ g = k) :
    modulePushforwardTriangle B S hS hk =
      modulePushforwardCompIso B S hS f g ≪≫
        eqToIso (congrArg (modulePushforward B S hS) hk) := rfl

/-- At the composite itself, the comparison of
`AlgebraicGeometry.Space.modulePushforwardTriangle` is the comparison of Stacks 03LU. -/
theorem modulePushforwardTriangle_rfl (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePushforwardTriangle B S hS (f := f) (g := g) rfl =
      modulePushforwardCompIso B S hS f g := by
  simp [modulePushforwardTriangle_eq]

/-- The comparison depends on the morphism and not on the presentation of it as a composite. -/
theorem modulePushforwardTriangle_congr {f : X ⟶ Y} {g : Y ⟶ Z} {k k' : X ⟶ Z}
    (hk : f ≫ g = k) (hk' : f ≫ g = k') (hkk : k = k') :
    modulePushforwardTriangle B S hS hk' =
      modulePushforwardTriangle B S hS hk ≪≫
        eqToIso (congrArg (modulePushforward B S hS) hkk) := by
  rw [modulePushforwardTriangle_eq, modulePushforwardTriangle_eq, Iso.trans_assoc, eqToIso_trans]

/-- Replacing the first factor of the composite by an equal morphism changes the comparison only
by the induced identification of the two direct images. -/
theorem modulePushforwardTriangle_congr_left {f f' : X ⟶ Y} (hff : f = f') {g : Y ⟶ Z}
    {k : X ⟶ Z} (hk : f ≫ g = k) (hk' : f' ≫ g = k) :
    modulePushforwardTriangle B S hS hk =
      isoWhiskerRight (eqToIso (congrArg (modulePushforward B S hS) hff))
          (modulePushforward B S hS g) ≪≫
        modulePushforwardTriangle B S hS hk' := by
  subst hff
  have hE : modulePushforwardTriangle B S hS hk = modulePushforwardTriangle B S hS hk' := rfl
  rw [hE]
  simp

/-- **`AlgebraicGeometry.Space.modulePushforwardTriangle` at a single module**, with its type
written as `g_*(f_*N) ≅ k_*N` rather than as `(f_* ⋙ g_*).obj N ≅ k_*.obj N`. -/
def modulePushforwardTriangleApp (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z} (hk : f ≫ g = k)
    (N : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS g).obj ((modulePushforward B S hS f).obj N) ≅
      (modulePushforward B S hS k).obj N :=
  (modulePushforwardTriangle B S hS hk).app N

/-- The `hom` of `AlgebraicGeometry.Space.modulePushforwardTriangleApp` is the component of the
comparison of `AlgebraicGeometry.Space.modulePushforwardTriangle`. -/
theorem modulePushforwardTriangleApp_hom {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z} (hk : f ≫ g = k)
    (N : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforwardTriangleApp B S hS hk N).hom =
      (modulePushforwardTriangle B S hS hk).hom.app N := rfl

/-- The comparison of the two iterated direct images along the two sides of a commuting square
`e ≫ l = r ≫ q` of morphisms of algebraic spaces. -/
def modulePushforwardSquare (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V W X Z : AlgebraicSpaces B S hS} {e : V ⟶ W} {l : W ⟶ Z} {r : V ⟶ X} {q : X ⟶ Z}
    {k : V ⟶ Z} (hk : e ≫ l = k) (hk' : r ≫ q = k) :
    modulePushforward B S hS e ⋙ modulePushforward B S hS l ≅
      modulePushforward B S hS r ⋙ modulePushforward B S hS q :=
  modulePushforwardTriangle B S hS hk ≪≫ (modulePushforwardTriangle B S hS hk').symm

/-! ### The associativity coherence -/

/-- **The comparison of direct images along composites is compatible with composition.**  For
`f : V ⟶ W`, `g : W ⟶ X` and `p : X ⟶ Z`, breaking the direct image along the triple composite
into three steps through `k = f ≫ g` or through `q = g ≫ p` gives the same comparison. -/
theorem modulePushforwardTriangle_assoc
    {f : V ⟶ W} {g : W ⟶ X} {p : X ⟶ Z} {k : V ⟶ X} {q : W ⟶ Z} {r : V ⟶ Z}
    (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r) (hkr : k ≫ p = r) :
    isoWhiskerLeft (modulePushforward B S hS f) (modulePushforwardTriangle B S hS hq) ≪≫
        modulePushforwardTriangle B S hS hr =
      (associator (modulePushforward B S hS f) (modulePushforward B S hS g)
          (modulePushforward B S hS p)).symm ≪≫
        isoWhiskerRight (modulePushforwardTriangle B S hS hk)
          (modulePushforward B S hS p) ≪≫
        modulePushforwardTriangle B S hS hkr := by
  subst hk hq
  have hE : modulePushforwardTriangle B S hS hr =
      modulePushforwardCompIso B S hS f (g ≫ p) ≪≫
        eqToIso (congrArg (modulePushforward B S hS) hkr) := rfl
  rw [modulePushforwardTriangle_eq hkr, hE, modulePushforwardTriangle_rfl,
    modulePushforwardTriangle_rfl, ← Iso.trans_assoc, ← Iso.trans_assoc,
    modulePushforwardCompIso_assoc B S hS f g p]
  simp only [Iso.trans_assoc]

/-- `AlgebraicGeometry.Space.modulePushforwardTriangle_assoc` at a single module. -/
theorem modulePushforwardTriangle_hom_app_assoc
    {f : V ⟶ W} {g : W ⟶ X} {p : X ⟶ Z} {k : V ⟶ X} {q : W ⟶ Z} {r : V ⟶ Z}
    (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r) (hkr : k ≫ p = r)
    (N : Modules.{u, u} B S hS V.1 V.2) :
    (modulePushforward B S hS p).map ((modulePushforwardTriangle B S hS hk).hom.app N) ≫
        (modulePushforwardTriangle B S hS hkr).hom.app N =
      (modulePushforwardTriangle B S hS hq).hom.app ((modulePushforward B S hS f).obj N) ≫
        (modulePushforwardTriangle B S hS hr).hom.app N :=
  Functor.cocycle_app_of_iso (modulePushforwardTriangle B S hS hk)
    (modulePushforwardTriangle B S hS hq) (modulePushforwardTriangle B S hS hkr)
    (modulePushforwardTriangle B S hS hr)
    (modulePushforwardTriangle_assoc hk hq hr hkr) N

end AlgebraicGeometry.Space

end
