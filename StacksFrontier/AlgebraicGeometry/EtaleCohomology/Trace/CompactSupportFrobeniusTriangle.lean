module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobeniusNatTrans
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusAdditivity

/-!
# The Frobenius-equivariant triangle of compactly supported cohomology

Let `k` be a finite field, `X` a scheme over `k` with a compactification `j : X ⟶ X̄` and `k̄` an
extension of `k`.  A short exact sequence `0 → K₁ → K₂ → K₃ → 0` of bounded below complexes of
sheaves of `Λ`-modules on `X_étale` gives a distinguished triangle

`RΓ_c(X_k̄, K₁) ⟶ RΓ_c(X_k̄, K₂) ⟶ RΓ_c(X_k̄, K₃) ⟶ RΓ_c(X_k̄, K₁)[1]`

on which the canonical action `π_X^*` of `Stacks.EtaleCohomology.canonicalCompactSupportFrobenius`
acts by a morphism of triangles.  Hence the long exact sequence of the `H^i_c(X_k̄, -)`, connecting
maps included, is `π_X^*`-equivariant.  For the open–closed sequence
`0 → j_!j^{-1}K → K → i_*i^{-1}K → 0` this is the equivariant localization sequence used in Step 1
of the proof of [Stacks, Tag 03UG].

## Main definitions

* `Stacks.EtaleCohomology.compactSupportFrobeniusTriangle` — the triangle.
* `Stacks.EtaleCohomology.compactSupportFrobeniusTriangleEndo` — `π_X^*` as an endomorphism of it.

## Main results

* `Stacks.EtaleCohomology.compactSupportFrobeniusTriangle_distinguished` — it is distinguished.
* `Stacks.EtaleCohomology.compactSupportFrobeniusTriangle_mor₁`,
  `Stacks.EtaleCohomology.compactSupportFrobeniusTriangle_mor₂` — its first two maps are
  `RΓ_c(X_k̄, -)` of the maps of the sequence.
* `Stacks.EtaleCohomology.compactSupportFrobeniusTriangleEndo_hom₁` (and `₂`, `₃`) — the components
  of the endomorphism are the canonical `π_X^*`.

## Implementation notes

The connecting map is read off a twisted injective resolution of the image of the sequence on
`X̄_k̄` (`CategoryTheory.Functor.TwistResolution`), chosen once and for all; the triangle is
isomorphic to the triangle of the short exact sequence obtained by applying `f_*` and `Γ(Spec k̄)`
degreewise to that resolution (`CategoryTheory.Functor.twistTriangleIso`).

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 1.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section CompactSupport

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-! ### The Frobenius-equivariant triangle -/

section Triangle

variable {S : ShortComplex (CochainComplex (EtaleModules.{u, r} Λ X) ℤ)} (hS : S.ShortExact)
  (h₁ : CochainComplex.plus _ S.X₁) (h₂ : CochainComplex.plus _ S.X₂)
  (h₃ : CochainComplex.plus _ S.X₃)

/-- A twisted injective resolution of the image on `X̄_k̄` of a short exact sequence on `X`. -/
def compactSupportTwistResolution :
    Functor.TwistResolution (etaleModuleDirectImage.{u, r} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
      (compactSupportShortComplexTwist.{u, r} Λ f j kbar p q hcard S) :=
  Classical.choice (Functor.TwistResolution.nonempty _
    (compactSupportShortComplex_shortExact.{u, r} Λ f j kbar hS)
    (((etaleModuleInverseImage.{u, r} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj
          ⟨S.X₁, h₁⟩)).property)
    (((etaleModuleInverseImage.{u, r} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj
          ⟨S.X₃, h₃⟩)).property) _)

/-- **The Frobenius-equivariant triangle of compactly supported cohomology**
`RΓ_c(X_k̄, K₁) ⟶ RΓ_c(X_k̄, K₂) ⟶ RΓ_c(X_k̄, K₃) ⟶ RΓ_c(X_k̄, K₁)[1]` of a short exact sequence
`0 → K₁ → K₂ → K₃ → 0` of bounded below complexes on `X`, in the unbounded derived category of
`Λ`-modules.  Its first two maps are `RΓ_c` of the maps of the sequence
(`compactSupportFrobeniusTriangle_mor₁`, `compactSupportFrobeniusTriangle_mor₂`), it is
distinguished (`compactSupportFrobeniusTriangle_distinguished`), and `π_X^*` acts on it by a
morphism of triangles (`compactSupportFrobeniusTriangleEndo`). -/
def compactSupportFrobeniusTriangle :
    Pretriangulated.Triangle (DerivedCategory (ModuleCat.{max (u + 1) r} Λ)) :=
  Functor.twistTriangle.{r, u + 1}
    (etaleModuleDirectImage.{u, r} Λ (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (((etaleModuleInverseImage.{u, r} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj
          ⟨S.X₁, h₁⟩)).property)
    (((etaleModuleInverseImage.{u, r} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj
          ⟨S.X₂, h₂⟩)).property)
    (((etaleModuleInverseImage.{u, r} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj
          ⟨S.X₃, h₃⟩)).property)
    (compactSupportTwistResolution.{u, r} Λ f j kbar p q hcard hS h₁ h₃)

/-- The triangle `compactSupportFrobeniusTriangle` is distinguished. -/
lemma compactSupportFrobeniusTriangle_distinguished :
    compactSupportFrobeniusTriangle.{u, r} Λ f j kbar p q hcard hS h₁ h₂ h₃ ∈
      distTriang (DerivedCategory (ModuleCat.{max (u + 1) r} Λ)) :=
  Functor.twistTriangle_distinguished _ _ _ _ _ _

/-- The first object of the triangle is `RΓ_c(X_k̄, K₁)`. -/
lemma compactSupportFrobeniusTriangle_obj₁ :
    (compactSupportFrobeniusTriangle.{u, r} Λ f j kbar p q hcard hS h₁ h₂ h₃).obj₁ =
      DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar ⟨S.X₁, h₁⟩) :=
  rfl

/-- The second object of the triangle is `RΓ_c(X_k̄, K₂)`. -/
lemma compactSupportFrobeniusTriangle_obj₂ :
    (compactSupportFrobeniusTriangle.{u, r} Λ f j kbar p q hcard hS h₁ h₂ h₃).obj₂ =
      DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar ⟨S.X₂, h₂⟩) :=
  rfl

/-- The third object of the triangle is `RΓ_c(X_k̄, K₃)`. -/
lemma compactSupportFrobeniusTriangle_obj₃ :
    (compactSupportFrobeniusTriangle.{u, r} Λ f j kbar p q hcard hS h₁ h₂ h₃).obj₃ =
      DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar ⟨S.X₃, h₃⟩) :=
  rfl

/-- The first map of the triangle is `RΓ_c(X_k̄, -)` applied to `K₁ ⟶ K₂`. -/
lemma compactSupportFrobeniusTriangle_mor₁ :
    (compactSupportFrobeniusTriangle.{u, r} Λ f j kbar p q hcard hS h₁ h₂ h₃).mor₁ =
      DerivedCategory.Plus.ι.map ((compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).map
        (ObjectProperty.homMk S.f : (⟨S.X₁, h₁⟩ : CochainComplex.Plus _) ⟶ ⟨S.X₂, h₂⟩)) :=
  rfl

/-- The second map of the triangle is `RΓ_c(X_k̄, -)` applied to `K₂ ⟶ K₃`. -/
lemma compactSupportFrobeniusTriangle_mor₂ :
    (compactSupportFrobeniusTriangle.{u, r} Λ f j kbar p q hcard hS h₁ h₂ h₃).mor₂ =
      DerivedCategory.Plus.ι.map ((compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).map
        (ObjectProperty.homMk S.g : (⟨S.X₂, h₂⟩ : CochainComplex.Plus _) ⟶ ⟨S.X₃, h₃⟩)) :=
  rfl

/-- **`π_X^*` acts on the triangle by a morphism of triangles**: its components are the canonical
endomorphisms `π_X^*` of the three `RΓ_c`, so the long exact sequence of compactly supported
cohomology, connecting maps included, is `π_X^*`-equivariant. -/
def compactSupportFrobeniusTriangleEndo :
    compactSupportFrobeniusTriangle.{u, r} Λ f j kbar p q hcard hS h₁ h₂ h₃ ⟶
      compactSupportFrobeniusTriangle.{u, r} Λ f j kbar p q hcard hS h₁ h₂ h₃ :=
  Functor.twistTriangleEndo.{r, u + 1}
    (etaleModuleDirectImage.{u, r} Λ (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (etaleModuleDirectImageComp.{u, r} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard).symm)
    (((etaleModuleInverseImage.{u, r} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj
          ⟨S.X₁, h₁⟩)).property)
    (((etaleModuleInverseImage.{u, r} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj
          ⟨S.X₂, h₂⟩)).property)
    (((etaleModuleInverseImage.{u, r} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj
          ⟨S.X₃, h₃⟩)).property)
    (compactSupportTwistResolution.{u, r} Λ f j kbar p q hcard hS h₁ h₃)

/-- The first component of `compactSupportFrobeniusTriangleEndo` is the canonical `π_X^*` on
`RΓ_c(X_k̄, K₁)`. -/
lemma compactSupportFrobeniusTriangleEndo_hom₁ :
    (compactSupportFrobeniusTriangleEndo.{u, r} Λ f j kbar p q hcard hS h₁ h₂ h₃).hom₁ =
      DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard ⟨S.X₁, h₁⟩) :=
  rfl

/-- The second component of `compactSupportFrobeniusTriangleEndo` is the canonical `π_X^*` on
`RΓ_c(X_k̄, K₂)`. -/
lemma compactSupportFrobeniusTriangleEndo_hom₂ :
    (compactSupportFrobeniusTriangleEndo.{u, r} Λ f j kbar p q hcard hS h₁ h₂ h₃).hom₂ =
      DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard ⟨S.X₂, h₂⟩) :=
  rfl

/-- The third component of `compactSupportFrobeniusTriangleEndo` is the canonical `π_X^*` on
`RΓ_c(X_k̄, K₃)`. -/
lemma compactSupportFrobeniusTriangleEndo_hom₃ :
    (compactSupportFrobeniusTriangleEndo.{u, r} Λ f j kbar p q hcard hS h₁ h₂ h₃).hom₃ =
      DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard ⟨S.X₃, h₃⟩) :=
  rfl

end Triangle

end CompactSupport

end Stacks.EtaleCohomology
