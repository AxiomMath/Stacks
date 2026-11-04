module

public import StacksFrontier.AlgebraicGeometry.AmpleAffineAvoidance.AmpleFiniteSet
public import StacksFrontier.AlgebraicGeometry.AmpleCluster.QuasiAffineAndImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.DegreeOne
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Scheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeGroupSchemeQuotient

/-!
# Affine opens containing finite subsets of fibres, in seven cases

For a morphism `f : X ⟶ S`, the condition `AlgebraicGeometry.HasAffineFinitePointsInFibres f`
asks that every finite subset of a fibre of `f` lie in an affine open of `X`. It is the hypothesis
under which [Stacks, Tag 0B9A] represents the degree-`d` Hilbert functor of `X` over `S`. This
file proves that it holds in each of the seven cases of [Stacks, Tag 0B9B]: the source is
quasi-affine; the morphism is quasi-affine, quasi-projective or locally projective; or the source
carries an ample, an `f`-ample, or an `f`-very ample invertible sheaf.

## Main results

* `Stacks.HilbertFibreAffineOpen.exists_isAffineOpen_forall_mem_of_hasAffineFinitePointsInFibres`:
  the condition in the `d`-tuple form of [Stacks, Tag 0B9A].
* `Stacks.HilbertFibreAffineOpen.hasAffineFinitePointsInFibres_of_iSup_eq_top`: the condition is
  local on the base.
* `Stacks.HilbertFibreAffineOpen.hasAffineFinitePointsInFibres_of_isImmersion_projectiveBundle`:
  the condition holds for a morphism that factors through an immersion into a projective bundle
  over the base.
* `Stacks.HilbertFibreAffineOpen.hasAffineFinitePointsInFibres_of_isQuasiAffine`: case (1).
* `AlgebraicGeometry.hasAffineFinitePointsInFibres_of_isQuasiAffineHom`: case (2).
* `AlgebraicGeometry.hasAffineFinitePointsInFibres_of_isQuasiProjective`: case (3).
* `Stacks.HilbertFibreAffineOpen.hasAffineFinitePointsInFibres_of_isLocallyProjective`: case (4).
* `Stacks.HilbertFibreAffineOpen.hasAffineFinitePointsInFibres_of_isAmple` and
  `Stacks.HilbertFibreAffineOpen.hasAffineFinitePointsInFibres_of_modulesIsAmple`: case (5).
* `Stacks.HilbertFibreAffineOpen.hasAffineFinitePointsInFibres_of_isRelativelyAmple` and
  `Stacks.HilbertFibreAffineOpen.hasAffineFinitePointsInFibres_of_modulesIsRelativelyAmple`:
  case (6).
* `Stacks.HilbertFibreAffineOpen.hasAffineFinitePointsInFibres_of_isRelativelyVeryAmple` and
  `Stacks.HilbertFibreAffineOpen.hasAffineFinitePointsInFibres_of_isRelativelyVeryAmpleTwistOne`:
  case (7).

## References

* [Stacks Project, Tag 0B9B](https://stacks.math.columbia.edu/tag/0B9B)
* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
* [Stacks Project, Tag 01SK](https://stacks.math.columbia.edu/tag/01SK)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-! ### Cases (2) and (3) -/

add_to_stacks 0B9B "case (2), the morphism is quasi-affine"
  AlgebraicGeometry.hasAffineFinitePointsInFibres_of_isQuasiAffineHom
add_to_stacks 0B9B "case (3), the morphism is quasi-projective"
  AlgebraicGeometry.hasAffineFinitePointsInFibres_of_isQuasiProjective

namespace Stacks.HilbertFibreAffineOpen

variable {X S : Scheme.{u}}

/-! ### The `d`-tuple form of the condition -/

/-- If every finite subset of a fibre of `f : X ⟶ S` lies in an affine open of `X`, then for every
`s ∈ S` and every `d`-tuple of points of the fibre `X_s` there is an affine open of `X`
containing all `d` of them. -/
theorem exists_isAffineOpen_forall_mem_of_hasAffineFinitePointsInFibres {f : X ⟶ S}
    (hf : HasAffineFinitePointsInFibres f) (d : ℕ) (s : S) (x : Fin d → X)
    (hx : ∀ i, f.base (x i) = s) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U := by
  obtain ⟨U, hU, hxU⟩ := hf s (Set.range x) (Set.finite_range x)
    (by rintro _ ⟨i, rfl⟩; exact hx i)
  exact ⟨U, hU, fun i => hxU (Set.mem_range_self i)⟩

/-! ### Locality on the base and immersions into projective bundles -/

/-- The fibrewise affineness condition is local on the base: if the base is covered by opens
`V i` over each of which the restriction of `f` satisfies `HasAffineFinitePointsInFibres`, then
`f` does. -/
theorem hasAffineFinitePointsInFibres_of_iSup_eq_top {ι : Type*} (f : X ⟶ S) (V : ι → S.Opens)
    (hV : (⨆ i, V i) = ⊤)
    (h : ∀ i, HasAffineFinitePointsInFibres (f ∣_ V i)) :
    HasAffineFinitePointsInFibres f := by
  intro s E hE hEs
  have hs : s ∈ (⨆ i, V i) := by rw [hV]; trivial
  obtain ⟨i, hsi⟩ := Opens.mem_iSup.mp hs
  have hEV : ∀ x ∈ E, x ∈ f ⁻¹ᵁ V i := fun x hx => by
    show f.base x ∈ V i
    rw [hEs x hx]
    exact hsi
  obtain ⟨U, hU, hEU⟩ := h i ⟨s, hsi⟩ (Subtype.val ⁻¹' E)
    (hE.preimage Subtype.val_injective.injOn)
    (fun y hy => Subtype.ext ((morphismRestrict_base_coe f (V i) y).trans (hEs y.1 hy)))
  refine ⟨(f ⁻¹ᵁ V i).ι ''ᵁ U, hU.image_of_isOpenImmersion _, fun x hx => ?_⟩
  exact (Scheme.Opens.mem_ι_image_iff _).mpr (hEU (show (⟨x, hEV x hx⟩ : _) ∈ _ from hx))

/-- If `f` factors as an immersion `i` of `X` into the projective bundle `𝐏(E)` of a module `E`
with quasi-coherent symmetric pieces followed by the projection to the base, then `f` satisfies
the fibrewise affineness condition. -/
theorem hasAffineFinitePointsInFibres_of_isImmersion_projectiveBundle {f : X ⟶ S} (E : S.Modules)
    (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
    (i : X ⟶ (Stacks.SymGraded.schemeProjectiveBundle E hqc).scheme) (him : IsImmersion i)
    (hfi : i ≫ Stacks.SymGraded.schemeProjectiveBundleToBase E hqc = f) :
    HasAffineFinitePointsInFibres f := by
  have := him
  refine hasAffineFinitePointsInFibres_of_forall_isAffineOpen f fun V hV E' hE' => ?_
  have hpb := Stacks.SymGraded.schemeProjectiveBundle_isPullback E hqc V hV
  have hw : ((f ⁻¹ᵁ V).ι ≫ i) ≫ Stacks.SymGraded.schemeProjectiveBundleToBase E hqc =
      (f ∣_ V) ≫ V.ι := by
    rw [Category.assoc, show i ≫ Stacks.SymGraded.schemeProjectiveBundleToBase E hqc = f from hfi,
      morphismRestrict_ι]
  have himm : IsImmersion ((f ⁻¹ᵁ V).ι ≫ i) := inferInstance
  set l := hpb.lift ((f ⁻¹ᵁ V).ι ≫ i) (f ∣_ V) hw with hldef
  have hcomp : IsImmersion
      (l ≫ (Stacks.SymGraded.schemeProjectiveBundle E hqc).chart V hV) := by
    rw [hldef, hpb.lift_fst]
    exact himm
  have : IsImmersion l :=
    IsImmersion.of_comp l ((Stacks.SymGraded.schemeProjectiveBundle E hqc).chart V hV)
  exact Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_immersion_proj _ l hE'

/-! ### Case (1): the source is quasi-affine -/

/-- If `X` is quasi-affine then every finite subset of a fibre of any `f : X ⟶ S` lies in an
affine open of `X`. -/
@[stacks 0B9B "case (1), the source is quasi-affine"]
theorem hasAffineFinitePointsInFibres_of_isQuasiAffine [Scheme.IsQuasiAffine X] (f : X ⟶ S) :
    HasAffineFinitePointsInFibres f := fun _ _ hE _ =>
  Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_isQuasiAffine hE

/-! ### Case (4): the morphism is locally projective -/

/-- A locally projective morphism satisfies the fibrewise affineness condition. -/
@[stacks 0B9B "case (4), the morphism is locally projective"]
theorem hasAffineFinitePointsInFibres_of_isLocallyProjective {f : X ⟶ S}
    (hf : IsLocallyProjective f) : HasAffineFinitePointsInFibres f := by
  obtain ⟨ι, V, hV, hproj⟩ := hf
  exact hasAffineFinitePointsInFibres_of_iSup_eq_top f V hV
    fun i => hasAffineFinitePointsInFibres_of_isProjective _ (hproj i)

/-! ### Case (5): an ample invertible sheaf on the source -/

/-- If `X` carries an ample invertible sheaf then every finite subset of a fibre of any
`f : X ⟶ S` lies in an affine open of `X`. -/
@[stacks 0B9B "case (5), an ample invertible sheaf on the source"]
theorem hasAffineFinitePointsInFibres_of_isAmple (f : X ⟶ S) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L) :
    HasAffineFinitePointsInFibres f := fun _ _ hE _ =>
  Stacks.AmpleAffineAvoidance.exists_affineOpen_containing_finite_of_ample L hL hE

/-- If `X` carries an invertible sheaf that is ample in the sense of
`AlgebraicGeometry.Scheme.Modules.IsAmple`, then every finite subset of a fibre of any
`f : X ⟶ S` lies in an affine open of `X`. -/
@[stacks 0B9B
  "case (5), an ample invertible sheaf on the source, at `Scheme.Modules.IsAmple`"]
theorem hasAffineFinitePointsInFibres_of_modulesIsAmple (f : X ⟶ S) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L]
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple X L) :
    HasAffineFinitePointsInFibres f :=
  hasAffineFinitePointsInFibres_of_isAmple f L
    (Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X L hL)

/-! ### Case (6): an `f`-ample invertible sheaf -/

/-- A morphism admitting a relatively ample invertible sheaf satisfies the fibrewise affineness
condition. -/
@[stacks 0B9B "case (6), an f-ample invertible sheaf, at `Stacks.RelativeAmple.IsRelativelyAmple`"]
theorem hasAffineFinitePointsInFibres_of_isRelativelyAmple {f : X ⟶ S} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    HasAffineFinitePointsInFibres f :=
  hasAffineFinitePointsInFibres_of_forall_isAffineOpen f fun V hV _E hE =>
    Stacks.AmpleAffineAvoidance.exists_affineOpen_containing_finite_of_ample _
      (Stacks.RelativeAmple.IsRelativelyAmple.isAmple_preimage f L hL V hV) hE

/-- A morphism admitting a relatively ample sheaf `L`, invertible in the sense of
`AlgebraicGeometry.SheafOfModules.IsInvertible`, satisfies the fibrewise affineness
condition. -/
@[stacks 0B9B
  "case (6), an f-ample invertible sheaf, at `Stacks.RelativeAmple.IsRelativelyAmple`"]
theorem hasAffineFinitePointsInFibres_of_modulesIsRelativelyAmple {f : X ⟶ S} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    HasAffineFinitePointsInFibres f :=
  hasAffineFinitePointsInFibres_of_isRelativelyAmple L hL

/-! ### Case (7): an `f`-very ample invertible sheaf -/

/-- A morphism admitting an invertible sheaf that is relatively very ample in the sense of
`Stacks.Tag01VMRelativeVeryAmple.IsRelativelyVeryAmple` satisfies the fibrewise affineness
condition. -/
@[stacks 0B9B "case (7), an f-very ample invertible sheaf"]
theorem hasAffineFinitePointsInFibres_of_isRelativelyVeryAmple {f : X ⟶ S} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.Tag01VMRelativeVeryAmple.IsRelativelyVeryAmple f L) :
    HasAffineFinitePointsInFibres f := by
  obtain ⟨E, hE, M, hM, -, i, himm, hover, -⟩ := hL
  have := hE
  exact hasAffineFinitePointsInFibres_of_isImmersion_projectiveBundle E
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E) i himm hover

/-- A morphism admitting an invertible sheaf that is relatively very ample in the sense of
`Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple`, with twist `𝒪_{𝐏(E)}(1)`, satisfies the
fibrewise affineness condition. -/
@[stacks 0B9B "case (7), an f-very ample invertible sheaf, at the Tag 01VM predicate"]
theorem hasAffineFinitePointsInFibres_of_isRelativelyVeryAmpleTwistOne {f : X ⟶ S} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L) :
    HasAffineFinitePointsInFibres f :=
  hasAffineFinitePointsInFibres_of_isRelativelyVeryAmple L
    (Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_isDegreeOneTwist f L hL)

end Stacks.HilbertFibreAffineOpen

end
