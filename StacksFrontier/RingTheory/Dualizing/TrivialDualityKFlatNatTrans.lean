module

public import StacksFrontier.RingTheory.Dualizing.TrivialDualityKFlat

/-!
# The comparison of Stacks 0BZE as one natural transformation on the whole derived category

`Stacks0BZE.comparison` of `StacksFrontier/RingTheory/Dualizing/TrivialDualityKFlat.lean` is defined
only at the K-flat complexes, and is natural only in chain maps between them: tensoring the derived
counit of Stacks 0A70 with a complex uses a chain-level fraction, which computes the derived tensor
product only on the K-flat complexes. This file assembles that family into a single natural
transformation

`Stacks0BZE.comparisonNatTrans : (- ⊗ᴸ_R RHom_R(A, R)) ⟶ RHom_R(A, -)`

of functors on all of `D(R)`, whose component at a K-flat complex is the comparison itself, and
records that its invertibility is equivalent to the pointwise invertibility that
`Stacks0BZE.cardIso` consumes.

The point of the reformulation is that a *single* natural transformation is the input the
compact-object dévissage of `StacksFrontier/Homology/Devissage/` wants: there, invertibility of a
shift-compatible natural transformation between triangulated, direct-sum-preserving functors out of
`D(R)` need only be checked at the free module of rank one in degree zero. Against
`Stacks0BZE.cardIso`, which asks for invertibility at every K-flat complex, that is a reduction
from a family of statements to one.

## Main definitions

* `Stacks0BZE.comparisonNatTrans` — the comparison of Stacks 0BZE as a natural transformation of
  functors on all of `D(R)`.

## Main results

* `Stacks0BZE.comparisonNatTrans_app` — its component at a K-flat complex is
  `Stacks0BZE.comparison`.
* `Stacks0BZE.isIso_comparisonNatTrans_iff` — it is invertible exactly when
  `Stacks0BZE.comparison` is invertible at every K-flat complex, so nothing is lost by passing to
  it.
* `Stacks0BZE.cardIsoOfIsIsoComparisonNatTrans` — **Stacks 0BZE from invertibility of that one
  natural transformation.**

## Implementation notes

The descent is `ModuleSystemRlimTensor.natTransOfResolutions`: the K-flat complexes resolve every
cochain complex, and `DerivedCategory.Q` is a localization with a calculus of fractions, so a
family of morphisms on a resolving class that is natural in chain maps between its members
determines a natural transformation on the localization. `Stacks0BZE.comparison_naturality` is
exactly the naturality that descent asks for.

That the component at a K-flat complex `K` is `Stacks0BZE.comparison f K hK` — rather than the
comparison at the *chosen* K-flat resolution of `Q K`, which is what the construction produces —
is `ModuleSystemRlimTensor.map_comp_eq_of_resolutions`: the family is natural along every morphism
of `D(R)` between images of K-flat complexes, in particular along the resolution isomorphism.

What this file does **not** supply are the two remaining hypotheses of the dévissage, namely
`CategoryTheory.NatTrans.CommShift` for this transformation and preservation of direct sums by the
derived tensor functor. The first is not reachable from the interface of
`CochainComplex.DerivedTensor.DerivedTensorChangeOfRings`: its field `commShift` is unconstrained
data, carrying no coherence with `alphaF`, with `directTensor` or with the shift on complexes, so
there is nothing to compare the shifted comparison against.

## References

* [The Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
* [The Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [The Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [The Stacks Project, Tag 09SN](https://stacks.math.columbia.edu/tag/09SN), the dévissage.
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe u v

namespace Stacks0BZE

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

/-- Every cochain complex of `R`-modules is resolved by a K-flat one, in the shape the descent of
`ModuleSystemRlimTensor.natTransOfResolutions` asks for. -/
theorem kFlat_resolves (K : CochainComplex (ModuleCat.{max v u} R) ℤ) :
    ∃ (L : CochainComplex (ModuleCat.{max v u} R) ℤ) (s : L ⟶ K),
      CochainComplex.KFlat.{u, max v u} L ∧ QuasiIso s := by
  obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution K
  exact ⟨P, s, hP, hs⟩

/-- **The comparison of Stacks 0BZE, as a natural transformation on all of `D(R)`.** The K-flat
complexes resolve, and `Stacks0BZE.comparison` is natural in chain maps between them, so the family
descends to a natural transformation from the derived tensor product with `RHom_R(A, R)` to derived
coextension of scalars. -/
def comparisonNatTrans : (bundle.{u, v} f).F ⟶ Dualizing.derivedHom.{u, v} f :=
  ModuleSystemRlimTensor.natTransOfResolutions
    (B := ModuleCat.{max v u} R) (fun K => CochainComplex.KFlat.{u, max v u} K)
    kFlat_resolves.{u} _ _ (fun K hK => comparison.{u, v} f K hK)
    (fun _ _ hK hL g => (comparison_naturality.{u, v} f hK hL g).symm)

/-- At a K-flat complex, `Stacks0BZE.comparisonNatTrans` is `Stacks0BZE.comparison`. The
construction uses a chosen K-flat resolution of the object, and the comparison is natural along the
resolution isomorphism, so the choice drops out. -/
theorem comparisonNatTrans_app (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    (comparisonNatTrans.{u, v} f).app (DerivedCategory.Q.obj K) = comparison.{u, v} f K hK := by
  have h := ModuleSystemRlimTensor.map_comp_eq_of_resolutions
    (B := ModuleCat.{max v u} R) (fun K => CochainComplex.KFlat.{u, max v u} K)
    kFlat_resolves.{u} (bundle.{u, v} f).F (Dualizing.derivedHom.{u, v} f)
    (fun K hK => comparison.{u, v} f K hK)
    (fun _ _ hK hL g => (comparison_naturality.{u, v} f hK hL g).symm)
    _ K (ModuleSystemRlimTensor.resolutionComplex_prop _ kFlat_resolves.{u} _) hK
    (ModuleSystemRlimTensor.resolutionIso (fun K => CochainComplex.KFlat.{u, max v u} K)
      kFlat_resolves.{u} (DerivedCategory.Q.obj K)).hom
  have e1 : (comparisonNatTrans.{u, v} f).app (DerivedCategory.Q.obj K) =
      (bundle.{u, v} f).F.map (ModuleSystemRlimTensor.resolutionIso
          (fun K => CochainComplex.KFlat.{u, max v u} K) kFlat_resolves.{u}
          (DerivedCategory.Q.obj K)).inv ≫
        comparison.{u, v} f _ (ModuleSystemRlimTensor.resolutionComplex_prop _
          kFlat_resolves.{u} (DerivedCategory.Q.obj K)) ≫
        (Dualizing.derivedHom.{u, v} f).map (ModuleSystemRlimTensor.resolutionIso
          (fun K => CochainComplex.KFlat.{u, max v u} K) kFlat_resolves.{u}
          (DerivedCategory.Q.obj K)).hom :=
    ModuleSystemRlimTensor.natTransOfResolutions_app _ _ _ _ _ _ _
  rw [e1, ← h, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  simp

/-- Pointwise invertibility of the comparison on the K-flat complexes gives invertibility of
`Stacks0BZE.comparisonNatTrans` at every object: every object is the image of a K-flat complex up
to isomorphism, and the transformation is natural. -/
theorem isIso_app_comparisonNatTrans_of_forall_kFlat
    (h : ∀ (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
      (hK : CochainComplex.KFlat.{u, max v u} K), IsIso (comparison.{u, v} f K hK))
    (X : DerivedCategory (ModuleCat.{max v u} R)) :
    IsIso ((comparisonNatTrans.{u, v} f).app X) := by
  obtain ⟨P, s, hP, hs⟩ := kFlat_resolves.{u} (DerivedCategory.Q.objPreimage X)
  let eX : DerivedCategory.Q.obj P ≅ X :=
    asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso X
  have : IsIso ((comparisonNatTrans.{u, v} f).app (DerivedCategory.Q.obj P)) := by
    rw [comparisonNatTrans_app.{u, v} f P hP]
    exact h P hP
  have : IsIso ((bundle.{u, v} f).F.map eX.hom ≫ (comparisonNatTrans.{u, v} f).app X) := by
    rw [(comparisonNatTrans.{u, v} f).naturality eX.hom]
    infer_instance
  exact IsIso.of_isIso_comp_left ((bundle.{u, v} f).F.map eX.hom) _

/-- **Nothing is lost in passing to the single natural transformation**: it is invertible exactly
when `Stacks0BZE.comparison` is invertible at every K-flat complex, which is the hypothesis of
`Stacks0BZE.cardIso`. -/
theorem isIso_comparisonNatTrans_iff :
    IsIso (comparisonNatTrans.{u, v} f) ↔
      ∀ (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
        (hK : CochainComplex.KFlat.{u, max v u} K), IsIso (comparison.{u, v} f K hK) := by
  refine ⟨fun h K hK => ?_, fun h => ?_⟩
  · rw [← comparisonNatTrans_app.{u, v} f K hK]
    infer_instance
  · have := isIso_app_comparisonNatTrans_of_forall_kFlat.{u, v} f h
    exact NatIso.isIso_of_isIso_app _

/-- **Stacks 0BZE from invertibility of one natural transformation.** If
`Stacks0BZE.comparisonNatTrans` is invertible, derived coextension of scalars along `f` is the
derived tensor product with `RHom_R(A, R)`. -/
def cardIsoOfIsIsoComparisonNatTrans (h : IsIso (comparisonNatTrans.{u, v} f)) :
    Dualizing.derivedHom.{u, v} f ≅ (bundle.{u, v} f).F :=
  (asIso (comparisonNatTrans.{u, v} f)).symm

end Stacks0BZE

end
