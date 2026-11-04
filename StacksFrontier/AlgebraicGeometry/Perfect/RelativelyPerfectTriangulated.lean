module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObject
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTriangulated
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DirectSummand
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DirectSummands
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Objects perfect relative to a base scheme form a saturated triangulated subcategory

Let `f : X ⟶ S` be a morphism of schemes which is flat and locally of finite presentation. The
`S`-perfect objects of `D(𝒪_X)` (Stacks 0DI0) form a strictly full, saturated, triangulated
subcategory: the property is closed under isomorphisms, it contains the zero object and is closed
under shifts and extensions, and it passes to direct summands. This is Stacks 0DI3.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo` is relative perfectness packaged as a
  property of the objects of `D(𝒪_X)`.
* `AlgebraicGeometry.RingedSpace.FiniteTorDimensionRestricts` says of a family of derived tensor
  products, one on each open subspace, that finite Tor dimension over a larger open forces finite
  Tor dimension over a smaller one.
* `AlgebraicGeometry.Scheme.Hom.locallyHasFiniteTorDimensionOver` and
  `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentOfFiniteTorDimensionRelativeTo`: locally finite
  Tor dimension over `f⁻¹𝒪_S`, and condition (B) of Stacks 0DI9, as properties of the objects of
  `D(𝒪_X)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isClosedUnderIsomorphisms_isPerfectRelativeTo` and
  `AlgebraicGeometry.Scheme.Hom.isSaturated_isPerfectRelativeTo`: for an arbitrary
  family of certificates, the `S`-perfect objects form a strictly full saturated subcategory.
* `AlgebraicGeometry.Scheme.Hom.isTriangulated_isPerfectRelativeTo`: for a family of certificates
  whose operations `- ⊗^{L} ℱ[0]` are exact and along which finite Tor dimension restricts to
  smaller opens, the `S`-perfect objects form a triangulated subcategory. At the derived tensor
  product of Stacks 06YU this is
  `AlgebraicGeometry.Scheme.Hom.isTriangulated_isPerfectRelativeTo_canonical`, and the whole of
  Stacks 0DI3 is
  `AlgebraicGeometry.Scheme.Hom.isSaturated_and_isTriangulated_isPerfectRelativeTo_canonical`.
* `AlgebraicGeometry.RingedSpace.finiteTorDimensionRestricts_firstProjection`: the family of
  first-projection certificates satisfies
  `AlgebraicGeometry.RingedSpace.FiniteTorDimensionRestricts`.
* `AlgebraicGeometry.Scheme.Hom.isTriangulated_isPseudoCoherentOfFiniteTorDimensionRelativeTo`
  together with its `isClosedUnderIsomorphisms_` companion (Stacks 0DI9, condition (B)): for `f`
  only locally of finite type, the objects of `D(𝒪_X)` pseudo-coherent relative to `S` and of
  locally finite Tor dimension in `D(f⁻¹𝒪_S)` form a strictly full triangulated subcategory. The
  `isSaturated_` companion adds that it is saturated.

## Implementation notes

Strict fullness is `CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms`, the
triangulated-subcategory condition is `CategoryTheory.ObjectProperty.IsTriangulated` and
saturation is `CategoryTheory.ObjectProperty.IsSaturated` (Stacks 05RB).

Pseudo-coherence contributes through its own providers: it is preserved by isomorphisms, it holds
for a zero object, it satisfies two-out-of-three in a distinguished triangle (Stacks 08CD) and it
passes to direct summands (Stacks 08CE).

Finite Tor dimension contributes through Stacks 08CK for summands — proved here for a retract, so
that no additivity of the restriction functors is needed — and through the long exact cohomology
sequence for a distinguished triangle, which is Stacks 08CJ. The latter uses that each
`- ⊗^{L} ℱ[0]` is exact, a property that
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring` does not record, so the statements
that use it are stated for families with shift-compatible exact operations, exactly as in
`StacksFrontier.Homology.RelativelyPerfect.Triangulated` for a ring map.

Closure under extensions needs one further property. Part (3) of Stacks 08CG is an existential
over open coverings, so combining two coverings requires passing to a common refinement, and a
certificate on an open subspace has no relation to the certificate on a smaller one. The
triangulated statement is therefore stated for families with the locality of finite Tor dimension,
`AlgebraicGeometry.RingedSpace.FiniteTorDimensionRestricts`; the derived tensor product of
Stacks 06YU has it, since it commutes with restriction to an open
(`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectTriangulatedCanonical`). Strict fullness
and saturation hold for an arbitrary family of certificates.

## References

* [Stacks Project, Lemma 36.35.4 (Tag 0DI3)](https://stacks.math.columbia.edu/tag/0DI3)
* [Stacks Project, Lemma 20.47.4 (Tag 08CD)](https://stacks.math.columbia.edu/tag/08CD)
* [Stacks Project, Lemma 20.47.6 (Tag 08CE)](https://stacks.math.columbia.edu/tag/08CE)
* [Stacks Project, Lemma 20.48.6 (Tag 08CJ)](https://stacks.math.columbia.edu/tag/08CJ)
* [Stacks Project, Lemma 20.48.8 (Tag 08CK)](https://stacks.math.columbia.edu/tag/08CK)
* [Stacks Project, Definition 13.6.1 (Tag 05RB)](https://stacks.math.columbia.edu/tag/05RB)
* [Stacks Project, Remark 36.35.5 (Tag 0DI9)](https://stacks.math.columbia.edu/tag/0DI9)
* [Stacks Project, Lemma 36.61.6 (Tag 09UL)](https://stacks.math.columbia.edu/tag/09UL)
* [Stacks Project, Lemma 36.61.9 (Tag 09UN)](https://stacks.math.columbia.edu/tag/09UN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
  StrictlyPerfect ZeroObject

universe d d' u

namespace AlgebraicGeometry.RingedSpace

/-! ### Tor amplitude at a single certificate -/

namespace CertifiedDerivedSheafTensoring

section OneSpace

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u, u} X)]
  (D : CertifiedDerivedSheafTensoring.{d, u} X)

/-- Widening the interval weakens Tor amplitude. -/
private theorem hasTorAmplitudeIn_mono (E : DerivedCategory (OXMod.{u, u} X)) {a b a' b' : ℤ}
    (ha : a' ≤ a) (hb : b ≤ b') (h : D.HasTorAmplitudeIn E a b) :
    D.HasTorAmplitudeIn E a' b' := by
  intro F i hi
  refine h F i ?_
  simp only [Set.mem_Icc, not_and, not_le] at hi ⊢
  omega

/-- Tor amplitude only depends on the isomorphism class of the object. -/
private theorem hasTorAmplitudeIn_of_iso {E E' : DerivedCategory (OXMod.{u, u} X)} (e : E ≅ E')
    {a b : ℤ} (h : D.HasTorAmplitudeIn E a b) : D.HasTorAmplitudeIn E' a b := fun F i hi =>
  (h F i hi).of_iso ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).mapIso
    ((D.derivedTensor.mapIso e).app
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F))).symm

/-- Finite Tor dimension only depends on the isomorphism class of the object. -/
private theorem hasFiniteTorDimension_of_iso {E E' : DerivedCategory (OXMod.{u, u} X)}
    (e : E ≅ E') (h : D.HasFiniteTorDimension E) : D.HasFiniteTorDimension E' := by
  obtain ⟨a, b, h⟩ := h
  exact ⟨a, b, hasTorAmplitudeIn_of_iso D e h⟩

/-- **Stacks 08CK for a retract.** If `B` has Tor amplitude in `[a, b]` and `A` is a retract of
`B`, then `A` has Tor amplitude in `[a, b]`: through `H^i(- ⊗^{L} ℱ[0])` the object `A` stays a
retract of `B`, and a retract of a zero object is zero. -/
private theorem hasTorAmplitudeIn_of_retract {A B : DerivedCategory (OXMod.{u, u} X)}
    (i : A ⟶ B) (r : B ⟶ A) (hir : i ≫ r = 𝟙 A) {a b : ℤ}
    (h : D.HasTorAmplitudeIn B a b) : D.HasTorAmplitudeIn A a b := fun F j hj =>
  Stacks.Cohomology.TorAmplitude.isZero_obj_of_retract
    (D.derivedTensor.flip.obj ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) ⋙
      DerivedCategory.homologyFunctor (OXMod.{u, u} X) j) i r hir (h F j hj)

/-- **Stacks 08CK for a retract**, for finite Tor dimension: the same interval works. -/
private theorem hasFiniteTorDimension_of_retract {A B : DerivedCategory (OXMod.{u, u} X)}
    (i : A ⟶ B) (r : B ⟶ A) (hir : i ≫ r = 𝟙 A) (h : D.HasFiniteTorDimension B) :
    D.HasFiniteTorDimension A := by
  obtain ⟨a, b, h⟩ := h
  exact ⟨a, b, hasTorAmplitudeIn_of_retract D i r hir h⟩

variable
  (commShift : ∀ F : OXMod.{u, u} X,
    (D.derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F)).CommShift ℤ)
  (triangulated : ∀ F : OXMod.{u, u} X, letI := commShift F;
    (D.derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F)).IsTriangulated)

include commShift triangulated in
/-- **Stacks 08CJ.** The three propagation rules for Tor amplitude in a distinguished triangle: if
two of the vertices have Tor amplitude in the displayed ranges, so has the third. Each
`- ⊗^{L} ℱ[0]` is exact, so it carries the triangle to a distinguished triangle, and the claim is
read off the long exact cohomology sequence. -/
private theorem hasTorAmplitudeIn_of_distinguished
    (T : Triangle (DerivedCategory (OXMod.{u, u} X))) (hT : T ∈ distinguishedTriangles)
    (a b : ℤ) :
    (D.HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1) → D.HasTorAmplitudeIn T.obj₂ a b →
        D.HasTorAmplitudeIn T.obj₃ a b) ∧
      (D.HasTorAmplitudeIn T.obj₁ a b → D.HasTorAmplitudeIn T.obj₃ a b →
        D.HasTorAmplitudeIn T.obj₂ a b) ∧
      (D.HasTorAmplitudeIn T.obj₂ (a + 1) (b + 1) → D.HasTorAmplitudeIn T.obj₃ a b →
        D.HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1)) := by
  have key (F : OXMod.{u, u} X) :
      (D.derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F)).mapTriangle.obj T ∈
          distinguishedTriangles := by
    let _ := commShift F
    let _ := triangulated F
    exact Functor.map_distinguished _ T hT
  refine ⟨fun h₁ h₂ F i hi => ?_, fun h₁ h₃ F i hi => ?_, fun h₂ h₃ F i hi => ?_⟩
  · have hex := DerivedCategory.HomologySequence.exact₃ _ (key F) i (i + 1) rfl
    refine hex.isZero_of_both_zeros ((h₂ F i hi).eq_zero_of_src _)
      ((h₁ F (i + 1) ?_).eq_zero_of_tgt _)
    simp only [Set.mem_Icc, not_and, not_le] at hi ⊢
    omega
  · have hex := DerivedCategory.HomologySequence.exact₂ _ (key F) i
    exact hex.isZero_of_both_zeros ((h₁ F i hi).eq_zero_of_src _)
      ((h₃ F i hi).eq_zero_of_tgt _)
  · have hex := DerivedCategory.HomologySequence.exact₁ _ (key F) (i - 1) i (by omega)
    refine hex.isZero_of_both_zeros ((h₃ F (i - 1) ?_).eq_zero_of_src _)
      ((h₂ F i hi).eq_zero_of_tgt _)
    simp only [Set.mem_Icc, not_and, not_le] at hi ⊢
    omega

include commShift triangulated in
/-- **Stacks 08CJ** for finite Tor dimension: two out of three in a distinguished triangle. The
intervals are widened to a common one and the propagation rules apply. -/
private theorem hasFiniteTorDimension_of_distinguished
    (T : Triangle (DerivedCategory (OXMod.{u, u} X))) (hT : T ∈ distinguishedTriangles) :
    (D.HasFiniteTorDimension T.obj₁ → D.HasFiniteTorDimension T.obj₂ →
        D.HasFiniteTorDimension T.obj₃) ∧
      (D.HasFiniteTorDimension T.obj₁ → D.HasFiniteTorDimension T.obj₃ →
        D.HasFiniteTorDimension T.obj₂) ∧
      (D.HasFiniteTorDimension T.obj₂ → D.HasFiniteTorDimension T.obj₃ →
        D.HasFiniteTorDimension T.obj₁) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a₁, b₁, h₁⟩ ⟨a₂, b₂, h₂⟩
    exact ⟨min (a₁ - 1) a₂, max (b₁ - 1) b₂,
      (hasTorAmplitudeIn_of_distinguished D commShift triangulated T hT _ _).1
        (hasTorAmplitudeIn_mono D _ (by omega) (by omega) h₁)
        (hasTorAmplitudeIn_mono D _ (min_le_right ..) (le_max_right ..) h₂)⟩
  · rintro ⟨a₁, b₁, h₁⟩ ⟨a₃, b₃, h₃⟩
    exact ⟨min a₁ a₃, max b₁ b₃,
      (hasTorAmplitudeIn_of_distinguished D commShift triangulated T hT _ _).2.1
        (hasTorAmplitudeIn_mono D _ (min_le_left ..) (le_max_left ..) h₁)
        (hasTorAmplitudeIn_mono D _ (min_le_right ..) (le_max_right ..) h₃)⟩
  · rintro ⟨a₂, b₂, h₂⟩ ⟨a₃, b₃, h₃⟩
    exact ⟨min (a₂ - 1) a₃ + 1, max (b₂ - 1) b₃ + 1,
      (hasTorAmplitudeIn_of_distinguished D commShift triangulated T hT _ _).2.2
        (hasTorAmplitudeIn_mono D _ (by omega) (by omega) h₂)
        (hasTorAmplitudeIn_mono D _ (min_le_right ..) (le_max_right ..) h₃)⟩

include commShift triangulated in
/-- A zero object has finite Tor dimension: each `- ⊗^{L} ℱ[0]` is exact, hence sends a zero
object to a zero object. -/
private theorem hasFiniteTorDimension_of_isZero {E : DerivedCategory (OXMod.{u, u} X)}
    (hE : IsZero E) : D.HasFiniteTorDimension E := by
  refine ⟨0, 0, fun F i _ => ?_⟩
  let _ := commShift F
  let _ := triangulated F
  exact (DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).map_isZero
    ((D.derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F)).map_isZero hE)

end OneSpace

end CertifiedDerivedSheafTensoring

/-! ### Locally finite Tor dimension -/

section Local

open CertifiedDerivedSheafTensoring

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u, u} X)]
  [∀ U : Opens X.carrier,
    HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]
  (D : ∀ U : Opens X.carrier,
    CertifiedDerivedSheafTensoring.{d', u} (X.restrict U.isOpenEmbedding))

/-- **Finite Tor dimension restricts to smaller opens** for the family of certificates `D`: if
`E|_V` has finite Tor dimension and `U ≤ V`, then `E|_U` has finite Tor dimension.

A family of certificates carries no relation between its members, so this is not automatic; it
holds for the genuine derived tensor product, which commutes with restriction to an open. -/
public def FiniteTorDimensionRestricts : Prop :=
  ∀ ⦃U V : Opens X.carrier⦄, U ≤ V → ∀ E : DerivedCategory (OXMod.{u, u} X),
    (D V).HasFiniteTorDimension ((derivedRestrictModules X V).obj E) →
      (D U).HasFiniteTorDimension ((derivedRestrictModules X U).obj E)

/-- **The cohomology of a derived restriction, computed on a complex.** For a complex `K` of
`𝒪_X`-modules together with an identification `Q(K) ≅ E` in `D(𝒪_X)`, the `i`-th cohomology of
`E|_W` is the `i`-th cohomology sheaf of the degreewise restriction `K|_W`.

Restriction of modules to an open is exact, so the derived restriction of `Q(K)` is the class of
`K|_W` (`AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso`), and the cohomology of the
class of a complex is the cohomology of the complex
(`DerivedCategory.homologyFunctorFactors`). -/
private def homologyDerivedRestrictModulesIso (K : CochainComplex (OXMod.{u, u} X) ℤ)
    (E : DerivedCategory (OXMod.{u, u} X)) (ε : DerivedCategory.Q.obj K ≅ E)
    (W : Opens X.carrier) (i : ℤ) :
    (DerivedCategory.homologyFunctor
        (OXMod.{u, u} (X.restrict W.isOpenEmbedding)) i).obj
          ((derivedRestrictModules X W).obj E) ≅
      (StrictlyPerfect.restrictComplex K W).homology i :=
  (DerivedCategory.homologyFunctor _ i).mapIso
      ((derivedRestrictModules X W).mapIso ε.symm ≪≫
        derivedRestrictModulesObjQIso X W K) ≪≫
    (DerivedCategory.homologyFunctorFactors _ i).app (restrictComplex K W)

/-- **Vanishing of a cohomology sheaf of a restriction passes to a smaller open.** If the `i`-th
cohomology of `E|_V` is zero and `U ≤ V`, then the `i`-th cohomology of `E|_U` is zero.

Choose a complex `K` representing `E`. Restricting `K` to `U` is restricting it to `V` and then
along the inclusion `U ≤ V` (`StrictlyPerfect.restrictComplexOfLEIso`), and the latter functor is
exact, so it preserves the vanishing of a cohomology sheaf
(`StrictlyPerfect.isZero_homology_restrictComplexOfLE`). -/
private theorem isZero_homology_derivedRestrictModules_of_le {U V : Opens X.carrier}
    (hUV : U ≤ V) (E : DerivedCategory (OXMod.{u, u} X)) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor
      (OXMod.{u, u} (X.restrict V.isOpenEmbedding)) i).obj
        ((derivedRestrictModules X V).obj E))) :
    IsZero ((DerivedCategory.homologyFunctor
      (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) i).obj
        ((derivedRestrictModules X U).obj E)) := by
  set K := DerivedCategory.Q.objPreimage E with hK
  have ε : DerivedCategory.Q.obj K ≅ E := Functor.objObjPreimageIso DerivedCategory.Q E
  refine (homologyDerivedRestrictModulesIso X K E ε U i).isZero_iff.2 ?_
  refine ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) i).mapIso
    (StrictlyPerfect.restrictComplexOfLEIso hUV K)).isZero_iff.1 ?_
  exact StrictlyPerfect.isZero_homology_restrictComplexOfLE hUV
    (StrictlyPerfect.restrictComplex K V) i
    ((homologyDerivedRestrictModulesIso X K E ε V i).isZero_iff.1 h)

/-- **`AlgebraicGeometry.RingedSpace.FiniteTorDimensionRestricts` is satisfiable**: the family of
first-projection certificates
(`AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection`), one on each
open subspace of `X`, has the property.

At the first-projection certificate, Tor amplitude in `[a, b]` is the vanishing of cohomology
outside `[a, b]` (`AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_firstProjection_iff`), so the
assertion is that the cohomology of `E|_U` vanishes wherever that of `E|_V` does, for `U ≤ V`.
That holds with the same interval, because restriction to `U` factors through restriction to `V`
and restriction to an open is exact, hence commutes with cohomology. -/
public theorem finiteTorDimensionRestricts_firstProjection :
    FiniteTorDimensionRestricts X
      (fun U => certifiedDerivedSheafTensoringOfFirstProjection.{d', u}
        (X.restrict U.isOpenEmbedding)) := by
  intro U V hUV E hE
  obtain ⟨a, b, hab⟩ := hE
  refine ⟨a, b, (hasTorAmplitudeIn_firstProjection_iff _ _ a b).2 fun i hi => ?_⟩
  exact isZero_homology_derivedRestrictModules_of_le X hUV E i
    ((hasTorAmplitudeIn_firstProjection_iff _ _ a b).1 hab i hi)

/-- Locally finite Tor dimension only depends on the isomorphism class of the object: the covering
witnessing it for one object witnesses it for any object isomorphic to it. -/
private theorem locallyHasFiniteTorDimension_of_iso {E E' : DerivedCategory (OXMod.{u, u} X)}
    (e : E ≅ E') (h : LocallyHasFiniteTorDimension X D E) :
    LocallyHasFiniteTorDimension X D E' := by
  obtain ⟨I, U, hU, hI⟩ := h
  exact ⟨I, U, hU, fun i => hasFiniteTorDimension_of_iso (D (U i))
    ((derivedRestrictModules X (U i)).mapIso e) (hI i)⟩

/-- **Stacks 08CK for a retract**, for locally finite Tor dimension: the covering witnessing it
for `G B` works for `G A`, since a restriction functor carries a retraction to a retraction. -/
private theorem locallyHasFiniteTorDimension_of_retract {C : Type*} [Category* C]
    (G : C ⥤ DerivedCategory (OXMod.{u, u} X)) {A B : C} (rt : Retract A B)
    (h : LocallyHasFiniteTorDimension X D (G.obj B)) :
    LocallyHasFiniteTorDimension X D (G.obj A) := by
  obtain ⟨I, U, hU, hI⟩ := h
  refine ⟨I, U, hU, fun k => hasFiniteTorDimension_of_retract (D (U k))
    ((derivedRestrictModules X (U k)).map (G.map rt.i))
    ((derivedRestrictModules X (U k)).map (G.map rt.r)) ?_ (hI k)⟩
  simp only [← Functor.map_comp, rt.retract, CategoryTheory.Functor.map_id]

variable
  (commShift : ∀ (U : Opens X.carrier) (F : OXMod.{u, u} (X.restrict U.isOpenEmbedding)),
    ((D U).derivedTensor.flip.obj ((DerivedCategory.singleFunctor
      (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) 0).obj F)).CommShift ℤ)
  (triangulated : ∀ (U : Opens X.carrier) (F : OXMod.{u, u} (X.restrict U.isOpenEmbedding)),
    letI := commShift U F;
    ((D U).derivedTensor.flip.obj ((DerivedCategory.singleFunctor
      (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) 0).obj F)).IsTriangulated)

include commShift triangulated in
/-- A zero object locally has finite Tor dimension: the one-member covering by the whole space
works, since each `- ⊗^{L} ℱ[0]` is exact. -/
private theorem locallyHasFiniteTorDimension_of_isZero {E : DerivedCategory (OXMod.{u, u} X)}
    (hE : IsZero E) : LocallyHasFiniteTorDimension X D E :=
  ⟨PUnit.{u + 1}, fun _ => ⊤, by simp, fun _ =>
    hasFiniteTorDimension_of_isZero (D ⊤) (commShift ⊤) (triangulated ⊤)
      ((derivedRestrictModules X ⊤).map_isZero hE)⟩

/-- **Two hypotheses of locally finite Tor dimension are combined on a common refinement.** If
`A` and `B` locally have finite Tor dimension and, over every open, finite Tor dimension of `A`
and of `B` forces that of `C`, then `C` locally has finite Tor dimension: the pairwise
intersections of the two coverings cover the space. -/
private theorem locallyHasFiniteTorDimension_of_two
    (hres : FiniteTorDimensionRestricts X D) (A B C : DerivedCategory (OXMod.{u, u} X))
    (hA : LocallyHasFiniteTorDimension X D A) (hB : LocallyHasFiniteTorDimension X D B)
    (key : ∀ W : Opens X.carrier,
      (D W).HasFiniteTorDimension ((derivedRestrictModules X W).obj A) →
        (D W).HasFiniteTorDimension ((derivedRestrictModules X W).obj B) →
          (D W).HasFiniteTorDimension ((derivedRestrictModules X W).obj C)) :
    LocallyHasFiniteTorDimension X D C := by
  obtain ⟨I, U, hU, hI⟩ := hA
  obtain ⟨J, V, hV, hJ⟩ := hB
  refine ⟨I × J, fun p => U p.1 ⊓ V p.2, ?_, fun p =>
    key _ (hres inf_le_left _ (hI p.1)) (hres inf_le_right _ (hJ p.2))⟩
  rw [← iSup_inf_iSup, hU, hV, top_inf_eq]

include commShift triangulated in
/-- **Stacks 08CJ** for locally finite Tor dimension: two out of three in a distinguished
triangle. Over a common refinement of the two coverings, restriction carries the triangle to a
distinguished triangle, where the propagation rules apply. -/
private theorem locallyHasFiniteTorDimension_of_distinguished
    (hres : FiniteTorDimensionRestricts X D)
    (T : Triangle (DerivedCategory (OXMod.{u, u} X))) (hT : T ∈ distinguishedTriangles) :
    (LocallyHasFiniteTorDimension X D T.obj₁ → LocallyHasFiniteTorDimension X D T.obj₂ →
        LocallyHasFiniteTorDimension X D T.obj₃) ∧
      (LocallyHasFiniteTorDimension X D T.obj₁ → LocallyHasFiniteTorDimension X D T.obj₃ →
        LocallyHasFiniteTorDimension X D T.obj₂) ∧
      (LocallyHasFiniteTorDimension X D T.obj₂ → LocallyHasFiniteTorDimension X D T.obj₃ →
        LocallyHasFiniteTorDimension X D T.obj₁) := by
  have key (W : Opens X.carrier) :=
    hasFiniteTorDimension_of_distinguished (D W) (commShift W) (triangulated W)
      ((derivedRestrictModules X W).mapTriangle.obj T)
      (map_distinguished_derivedRestrictModules X W T hT)
  refine ⟨fun h₁ h₂ => ?_, fun h₁ h₃ => ?_, fun h₂ h₃ => ?_⟩
  · exact locallyHasFiniteTorDimension_of_two X D hres _ _ _ h₁ h₂ fun W => (key W).1
  · exact locallyHasFiniteTorDimension_of_two X D hres _ _ _ h₁ h₃ fun W => (key W).2.1
  · exact locallyHasFiniteTorDimension_of_two X D hres _ _ _ h₂ h₃ fun W => (key W).2.2

end Local

/-! ### Pseudo-coherence in a distinguished triangle -/

section PseudoCoherent

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- **Stacks 08CD** without a fixed degree: two out of three for pseudo-coherence in a
distinguished triangle. Pseudo-coherence is `m`-pseudo-coherence for every `m`, and the three
parts of Stacks 08CD apply degree by degree. -/
private theorem isPseudoCoherent_of_distinguished
    (T : Triangle (DerivedCategory (OXMod.{u, u} X))) (hT : T ∈ distinguishedTriangles) :
    (IsPseudoCoherent T.obj₁ → IsPseudoCoherent T.obj₂ → IsPseudoCoherent T.obj₃) ∧
      (IsPseudoCoherent T.obj₁ → IsPseudoCoherent T.obj₃ → IsPseudoCoherent T.obj₂) ∧
      (IsPseudoCoherent T.obj₂ → IsPseudoCoherent T.obj₃ → IsPseudoCoherent T.obj₁) := by
  refine ⟨fun h₁ h₂ => (isPseudoCoherent_iff_forall _).2 fun m => ?_,
    fun h₁ h₃ => (isPseudoCoherent_iff_forall _).2 fun m => ?_,
    fun h₂ h₃ => (isPseudoCoherent_iff_forall _).2 fun m => ?_⟩
  · exact isPseudoCoherentFrom_obj₃_of_distinguished m T hT
      ((isPseudoCoherent_iff_forall _).1 h₁ (m + 1)) ((isPseudoCoherent_iff_forall _).1 h₂ m)
  · exact isPseudoCoherentFrom_obj₂_of_distinguished m T hT
      ((isPseudoCoherent_iff_forall _).1 h₁ m) ((isPseudoCoherent_iff_forall _).1 h₃ m)
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    exact isPseudoCoherentFrom_obj₁_of_distinguished n T hT
      ((isPseudoCoherent_iff_forall _).1 h₂ (n + 1)) ((isPseudoCoherent_iff_forall _).1 h₃ n)

end PseudoCoherent

end AlgebraicGeometry.RingedSpace

/-! ### Shift stability from two out of three -/

namespace CategoryTheory.ObjectProperty

/-- An object property of a pretriangulated category that contains the zero object, is closed
under isomorphisms and satisfies the first and third two-out-of-three rules in a distinguished
triangle is stable under all integer shifts: a shift by `n` is reached from the contractible
triangles by induction on `n`. -/
private theorem isStableUnderShift_of_twoOutOfThree {C : Type*} [Category* C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    (h₁ : ∀ T : Triangle C, T ∈ distinguishedTriangles → P T.obj₂ → P T.obj₃ → P T.obj₁)
    (h₃ : ∀ T : Triangle C, T ∈ distinguishedTriangles → P T.obj₁ → P T.obj₂ → P T.obj₃) :
    P.IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨by
    intro E hE
    induction n using Int.induction_on with
    | zero => exact P.prop_of_iso ((shiftFunctorZero C ℤ).symm.app E) hE
    | succ n hn =>
        exact P.prop_of_iso ((shiftFunctorAdd C (n : ℤ) 1).symm.app E)
          (h₃ _ (contractible_distinguished₂ (E⟦(n : ℤ)⟧)) hn P.prop_zero)
    | pred n hn =>
        apply h₁ (Triangle.mk (0 : E⟦-(n : ℤ) - 1⟧ ⟶ (0 : C)) 0
            (𝟙 ((E⟦-(n : ℤ) - 1⟧)⟦(1 : ℤ)⟧)))
          (contractible_distinguished₂ (E⟦-(n : ℤ) - 1⟧)) P.prop_zero
        exact P.prop_of_iso
          ((shiftFunctorAdd' C (-(n : ℤ) - 1) 1 (-(n : ℤ)) (by omega)).app E) hn⟩

end CategoryTheory.ObjectProperty

/-! ### The subcategory of objects perfect relative to the base -/

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory.ObjectProperty AlgebraicGeometry.RingedSpace
  AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
  [HasDerivedCategory.{d'} (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]
  [∀ U : TopologicalSpace.Opens
      (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    HasDerivedCategory.{d'}
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        U.isOpenEmbedding))]
  [Flat f] [LocallyOfFinitePresentation f]
  (D : ∀ U : TopologicalSpace.Opens
      (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
      ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))

/-- **Stacks 0DI3.** The objects of `D(𝒪_X)` that are perfect relative to `S` (Stacks 0DI0),
viewed as a property of the objects of `D(𝒪_X)`. The packaging is what lets the closure
properties of Stacks 0DI3 be stated as conditions on a subcategory. -/
public def isPerfectRelativeTo :
    ObjectProperty (DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :=
  fun E => f.IsPerfectRelativeTo D E

/-- An object of `D(𝒪_X)` lies in `isPerfectRelativeTo` exactly when it is perfect relative to
`S`. -/
public theorem isPerfectRelativeTo_iff (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    isPerfectRelativeTo f D E ↔ f.IsPerfectRelativeTo D E :=
  Iff.rfl

/-- For a flat, locally finitely presented morphism `f : X ⟶ S` of schemes and an arbitrary
family of Stacks 08CG certificates, the `S`-perfect objects of `D(𝒪_X)` form a *strictly full*
subcategory: relative perfectness is invariant under isomorphism in `D(𝒪_X)`. -/
public theorem isClosedUnderIsomorphisms_isPerfectRelativeTo :
    (isPerfectRelativeTo f D).IsClosedUnderIsomorphisms :=
  ⟨fun e h => ⟨h.1.of_iso e,
    locallyHasFiniteTorDimension_of_iso _ D ((derivedScalarRestriction f).mapIso e) h.2⟩⟩

/-- For a flat, locally finitely presented morphism `f : X ⟶ S` of schemes and an arbitrary
family of Stacks 08CG certificates, the `S`-perfect objects of `D(𝒪_X)` form a *saturated*
(thick) subcategory: a direct summand of an `S`-perfect object is `S`-perfect. -/
public theorem isSaturated_isPerfectRelativeTo :
    (isPerfectRelativeTo f D).IsSaturated := by
  let _ := isClosedUnderIsomorphisms_isPerfectRelativeTo f D
  have key (A B : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) [HasBinaryBiproduct A B]
      (h : f.IsPerfectRelativeTo D (A ⊞ B)) :
      f.IsPerfectRelativeTo D A ∧ f.IsPerfectRelativeTo D B :=
    ⟨⟨isPseudoCoherent_left_of_biprod A B h.1, locallyHasFiniteTorDimension_of_retract _ D
        (derivedScalarRestriction f) ⟨biprod.inl, biprod.fst, biprod.inl_fst⟩ h.2⟩,
      ⟨isPseudoCoherent_right_of_biprod A B h.1, locallyHasFiniteTorDimension_of_retract _ D
        (derivedScalarRestriction f) ⟨biprod.inr, biprod.snd, biprod.inr_snd⟩ h.2⟩⟩
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [ObjectProperty.isoClosure_eq_self] at h ⊢
  · exact (key _ _ h).1
  · exact (key _ _ h).2

variable
  (commShift : ∀ (U : TopologicalSpace.Opens
      (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
    (F : OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
      U.isOpenEmbedding)),
    ((D U).derivedTensor.flip.obj ((DerivedCategory.singleFunctor
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        U.isOpenEmbedding)) 0).obj F)).CommShift ℤ)
  (triangulated : ∀ (U : TopologicalSpace.Opens
      (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
    (F : OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
      U.isOpenEmbedding)),
    letI := commShift U F;
    ((D U).derivedTensor.flip.obj ((DerivedCategory.singleFunctor
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        U.isOpenEmbedding)) 0).obj F)).IsTriangulated)
  (hres : RingedSpace.FiniteTorDimensionRestricts
    (RingedSpace.inverseImage S.toRingedSpace f.base) D)

include commShift triangulated hres in
/-- Two out of three for relative perfectness in a distinguished triangle of `D(𝒪_X)`: restriction
of scalars along `f^{-1}𝒪_S ⟶ 𝒪_X` is exact, so it carries the triangle to a distinguished
triangle on the inverse-image ringed space, where locally finite Tor dimension propagates by
Stacks 08CJ; pseudo-coherence propagates by Stacks 08CD. -/
private theorem isPerfectRelativeTo_of_distinguished
    (T : Triangle (DerivedCategory (OXMod.{u, u} X.toRingedSpace)))
    (hT : T ∈ distinguishedTriangles) :
    let P := isPerfectRelativeTo f D
    (P T.obj₁ → P T.obj₂ → P T.obj₃) ∧ (P T.obj₁ → P T.obj₃ → P T.obj₂) ∧
      (P T.obj₂ → P T.obj₃ → P T.obj₁) := by
  have hTF : (derivedScalarRestriction f).mapTriangle.obj T ∈ distinguishedTriangles :=
    Functor.map_distinguished _ T hT
  have hpc := isPseudoCoherent_of_distinguished T hT
  have htor := locallyHasFiniteTorDimension_of_distinguished _ D commShift triangulated hres _ hTF
  exact ⟨fun h₁ h₂ => ⟨hpc.1 h₁.1 h₂.1, htor.1 h₁.2 h₂.2⟩,
    fun h₁ h₃ => ⟨hpc.2.1 h₁.1 h₃.1, htor.2.1 h₁.2 h₃.2⟩,
    fun h₂ h₃ => ⟨hpc.2.2 h₂.1 h₃.1, htor.2.2 h₂.2 h₃.2⟩⟩

include commShift triangulated hres in
/-- For a flat, locally finitely presented morphism `f : X ⟶ S` of schemes and a family of
Stacks 08CG certificates on the open subspaces of `(X, f^{-1}𝒪_S)` whose operations
`- ⊗^{L} ℱ[0]` commute with the shift and are exact, and for which finite Tor dimension on an open
subspace gives finite Tor dimension on every smaller one, the objects of `D(𝒪_X)` perfect relative
to `S` at that family form a *triangulated* subcategory: the property contains the zero object, is
stable under all shifts, and is closed under extensions. -/
@[sga "6 III 4.2" "flat, loc. fin. pres."]
public theorem isTriangulated_isPerfectRelativeTo :
    (isPerfectRelativeTo f D).IsTriangulated := by
  let _ := isClosedUnderIsomorphisms_isPerfectRelativeTo f D
  let _ : (isPerfectRelativeTo f D).ContainsZero :=
    ⟨⟨0, isZero_zero _,
      ⟨isPseudoCoherent_of_isZero (isZero_zero _),
        locallyHasFiniteTorDimension_of_isZero _ D commShift triangulated
          ((derivedScalarRestriction f).map_isZero (isZero_zero _))⟩⟩⟩
  have htri := isPerfectRelativeTo_of_distinguished f D commShift triangulated hres
  let _ := ObjectProperty.isStableUnderShift_of_twoOutOfThree (isPerfectRelativeTo f D)
    (fun T hT => (htri T hT).2.2) (fun T hT => (htri T hT).1)
  exact { ext₂' T hT h₁ h₃ := ObjectProperty.le_isoClosure _ _ ((htri T hT).2.1 h₁ h₃) }

end AlgebraicGeometry.Scheme.Hom

/-! ### Condition (B) of Stacks 0DI9 -/

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory.ObjectProperty AlgebraicGeometry.RingedSpace
  AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring

section ConditionB

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
  [HasDerivedCategory.{d'}
    (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]
  [∀ U : TopologicalSpace.Opens
      (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    HasDerivedCategory.{d'}
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        U.isOpenEmbedding))]
  (D : ∀ U : TopologicalSpace.Opens
      (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
      ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))

/-- The objects of `D(𝒪_X)` which, after restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X`, locally
have finite Tor dimension on the inverse-image ringed space `(X, f⁻¹𝒪_S)` — part (3) of
Stacks 08CG — viewed as a property of the objects of `D(𝒪_X)`. -/
public def locallyHasFiniteTorDimensionOver :
    ObjectProperty (DerivedCategory X.Modules) :=
  fun E => RingedSpace.LocallyHasFiniteTorDimension
    (RingedSpace.inverseImage S.toRingedSpace f.base) D ((derivedScalarRestriction f).obj E)

/-- **Condition (B) of Stacks 0DI9.** For a morphism of schemes `f : X ⟶ S` locally of finite
type, the objects of `D(𝒪_X)` which are pseudo-coherent relative to `S` (Stacks 09UI) and which,
viewed in `D(f⁻¹𝒪_S)`, locally have finite Tor dimension (part (3) of Stacks 08CG). -/
public def isPseudoCoherentOfFiniteTorDimensionRelativeTo :
    ObjectProperty (DerivedCategory X.Modules) :=
  isPseudoCoherentRelativeTo f ⊓ locallyHasFiniteTorDimensionOver f D

/-- An object of `D(𝒪_X)` satisfies condition (B) of Stacks 0DI9 exactly when it is
pseudo-coherent relative to `S` and locally has finite Tor dimension over `f⁻¹𝒪_S`. -/
public theorem isPseudoCoherentOfFiniteTorDimensionRelativeTo_iff
    (E : DerivedCategory X.Modules) :
    isPseudoCoherentOfFiniteTorDimensionRelativeTo f D E ↔
      f.IsPseudoCoherent E ∧
        RingedSpace.LocallyHasFiniteTorDimension
          (RingedSpace.inverseImage S.toRingedSpace f.base) D
          ((derivedScalarRestriction f).obj E) :=
  Iff.rfl

omit [LocallyOfFiniteType f] in
/-- Locally finite Tor dimension over `f⁻¹𝒪_S` only depends on the isomorphism class of the
object of `D(𝒪_X)`. -/
private theorem isClosedUnderIsomorphisms_locallyHasFiniteTorDimensionOver :
    (locallyHasFiniteTorDimensionOver f D).IsClosedUnderIsomorphisms :=
  ⟨fun e h =>
    locallyHasFiniteTorDimension_of_iso _ D ((derivedScalarRestriction f).mapIso e) h⟩

/-- **Stacks 0DI9, condition (B).** For a morphism of schemes `f : X ⟶ S` which is only assumed
locally of finite type, the objects of `D(𝒪_X)` satisfying condition (B) form a *strictly full*
subcategory: both clauses are invariant under isomorphism in `D(𝒪_X)`. -/
@[stacks 0DI9 "condition (B) defines a triangulated subcategory"]
public theorem isClosedUnderIsomorphisms_isPseudoCoherentOfFiniteTorDimensionRelativeTo :
    (isPseudoCoherentOfFiniteTorDimensionRelativeTo f D).IsClosedUnderIsomorphisms := by
  let _ := isClosedUnderIsomorphisms_isPseudoCoherentRelativeTo f
  let _ := isClosedUnderIsomorphisms_locallyHasFiniteTorDimensionOver f D
  exact inferInstanceAs ((isPseudoCoherentRelativeTo f ⊓
    locallyHasFiniteTorDimensionOver f D).IsClosedUnderIsomorphisms)

variable
  (commShift : ∀ (U : TopologicalSpace.Opens
      (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
    (F : OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
      U.isOpenEmbedding)),
    ((D U).derivedTensor.flip.obj ((DerivedCategory.singleFunctor
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        U.isOpenEmbedding)) 0).obj F)).CommShift ℤ)
  (triangulated : ∀ (U : TopologicalSpace.Opens
      (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
    (F : OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
      U.isOpenEmbedding)),
    letI := commShift U F;
    ((D U).derivedTensor.flip.obj ((DerivedCategory.singleFunctor
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        U.isOpenEmbedding)) 0).obj F)).IsTriangulated)
  (hres : RingedSpace.FiniteTorDimensionRestricts
    (RingedSpace.inverseImage S.toRingedSpace f.base) D)

omit [LocallyOfFiniteType f] in
include commShift triangulated hres in
/-- Two out of three for locally finite Tor dimension over `f⁻¹𝒪_S` in a distinguished triangle
of `D(𝒪_X)`: restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X` is exact, so it carries the triangle to
a distinguished triangle on the inverse-image ringed space, where Stacks 08CJ applies. -/
private theorem locallyHasFiniteTorDimensionOver_of_distinguished
    (T : Triangle (DerivedCategory X.Modules)) (hT : T ∈ distinguishedTriangles) :
    let P := locallyHasFiniteTorDimensionOver f D
    (P T.obj₁ → P T.obj₂ → P T.obj₃) ∧ (P T.obj₁ → P T.obj₃ → P T.obj₂) ∧
      (P T.obj₂ → P T.obj₃ → P T.obj₁) := by
  have hT' : (T : Triangle (DerivedCategory (OXMod.{u, u} X.toRingedSpace))) ∈
      distinguishedTriangles := hT
  exact locallyHasFiniteTorDimension_of_distinguished _ D commShift triangulated hres _
    (Functor.map_distinguished (derivedScalarRestriction f) _ hT')

omit [LocallyOfFiniteType f] in
include commShift triangulated hres in
/-- The objects of `D(𝒪_X)` which locally have finite Tor dimension over `f⁻¹𝒪_S` form a
triangulated subcategory. Exactness of each `- ⊗^{L} ℱ[0]` and locality of finite Tor dimension
are hypotheses, both of them properties of the genuine derived tensor product that an arbitrary
certificate need not have. -/
private theorem isTriangulated_locallyHasFiniteTorDimensionOver :
    (locallyHasFiniteTorDimensionOver f D).IsTriangulated := by
  let _ := isClosedUnderIsomorphisms_locallyHasFiniteTorDimensionOver f D
  let _ : (locallyHasFiniteTorDimensionOver f D).ContainsZero :=
    ⟨⟨0, isZero_zero _, locallyHasFiniteTorDimension_of_isZero _ D commShift triangulated
      ((derivedScalarRestriction f).map_isZero (isZero_zero _))⟩⟩
  have htri :=
    locallyHasFiniteTorDimensionOver_of_distinguished f D commShift triangulated hres
  let _ := ObjectProperty.isStableUnderShift_of_twoOutOfThree
    (locallyHasFiniteTorDimensionOver f D)
    (fun T hT => (htri T hT).2.2) (fun T hT => (htri T hT).1)
  exact { ext₂' T hT h₁ h₃ := ObjectProperty.le_isoClosure _ _ ((htri T hT).2.1 h₁ h₃) }

include commShift triangulated hres in
/-- **Stacks 0DI9, condition (B).** For a morphism of schemes `f : X ⟶ S` which is only assumed
locally of finite type — neither flat nor locally of finite presentation — the objects of
`D(𝒪_X)` that are pseudo-coherent relative to `S` and of locally finite Tor dimension in
`D(f⁻¹𝒪_S)` form a *triangulated* subcategory: the property contains the zero object, is stable
under all shifts, and is closed under extensions.

Both clauses are triangulated subcategories separately — relative pseudo-coherence by Stacks
09UL, finite Tor dimension by Stacks 08CJ — and their intersection is one again. Exactness of
each `- ⊗^{L} ℱ[0]` and locality of finite Tor dimension are hypotheses, both of them properties
of the genuine derived tensor product that an arbitrary certificate need not have. -/
@[stacks 0DI9 "condition (B) defines a triangulated subcategory"]
public theorem isTriangulated_isPseudoCoherentOfFiniteTorDimensionRelativeTo :
    (isPseudoCoherentOfFiniteTorDimensionRelativeTo f D).IsTriangulated := by
  let _ := isClosedUnderIsomorphisms_isPseudoCoherentRelativeTo f
  let _ := isTriangulated_isPseudoCoherentRelativeTo f
  let _ := isClosedUnderIsomorphisms_locallyHasFiniteTorDimensionOver f D
  let _ := isTriangulated_locallyHasFiniteTorDimensionOver f D commShift triangulated hres
  exact inferInstanceAs ((isPseudoCoherentRelativeTo f ⊓
    locallyHasFiniteTorDimensionOver f D).IsTriangulated)

/-- The objects of `D(𝒪_X)` satisfying condition (B) of Stacks 0DI9 form a *saturated* (thick)
subcategory: a direct summand of such an object is one again, by Stacks 09UN for relative
pseudo-coherence and by Stacks 08CK for finite Tor dimension. -/
public theorem isSaturated_isPseudoCoherentOfFiniteTorDimensionRelativeTo :
    (isPseudoCoherentOfFiniteTorDimensionRelativeTo f D).IsSaturated := by
  let _ := isClosedUnderIsomorphisms_isPseudoCoherentOfFiniteTorDimensionRelativeTo f D
  have key (A B : DerivedCategory X.Modules) [HasBinaryBiproduct A B]
      (h : isPseudoCoherentOfFiniteTorDimensionRelativeTo f D (A ⊞ B)) :
      isPseudoCoherentOfFiniteTorDimensionRelativeTo f D A ∧
        isPseudoCoherentOfFiniteTorDimensionRelativeTo f D B :=
    ⟨⟨IsPseudoCoherent.of_biprod_left f A B h.1, locallyHasFiniteTorDimension_of_retract _ D
        (derivedScalarRestriction f)
        (⟨biprod.inl, biprod.fst, biprod.inl_fst⟩ : Retract A (A ⊞ B)) h.2⟩,
      ⟨IsPseudoCoherent.of_biprod_right f A B h.1, locallyHasFiniteTorDimension_of_retract _ D
        (derivedScalarRestriction f)
        (⟨biprod.inr, biprod.snd, biprod.inr_snd⟩ : Retract B (A ⊞ B)) h.2⟩⟩
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [ObjectProperty.isoClosure_eq_self] at h ⊢
  · exact (key _ _ h).1
  · exact (key _ _ h).2

end ConditionB

end AlgebraicGeometry.Scheme.Hom

end
