module

public import StacksFrontier.AlgebraicGeometry.Etale.AffineOverPuncturedSpectrum
public import StacksFrontier.Homology.Tor.DerivedTensorInvertibleScalar

/-!
# The affine cover of a scheme with empty closed fibre, and the vanishing on its members

Let `A` be a commutative ring, let `I ⊆ A` be an ideal and let `V` be a scheme whose structure
morphism `f : V ⟶ Spec A` factors through the complement of the zero locus of `I` by an affine
morphism. For `x ∈ I` the standard open `V_x` of the image of `x` in `Γ(V, 𝒪_V)` is then an
affine open of `V`, and a family of elements of `I` generating `I` makes those opens cover `V`.
For `A` local and `I = 𝔪` this says that the closed fibre of `V` is empty, in the form in which
a Čech or Mayer--Vietoris argument can use it.

On each member of that cover the element `x` becomes invertible, so `x` acts invertibly on the
`A`-module `Γ(V, V_x)` while annihilating `A ⧸ I`. By
`Stacks.DerivedTensor.isZero_derivedTensor_single_quotient_of_isUnit` the derived tensor product
`Γ(V, V_x) ⊗^L_A A ⧸ I` therefore vanishes, in every degree.

## Main definitions

* `Stacks.PuncturedSpectrum.baseHomLE` — the ring map `A → Γ(V, W)` induced by `f` on an open
  `W ⊆ V`.
* `Stacks.PuncturedSpectrum.baseAlgebraLE` — the `A`-algebra structure it gives `Γ(V, W)`.

## Main results

* `Stacks.PuncturedSpectrum.puncturedSpectrum_le_iSup_specBasicOpen` — the standard opens of a
  generating family of the maximal ideal cover the punctured spectrum.
* `Stacks.PuncturedSpectrum.iSup_basicOpen_baseHom_eq_top` — hence the inverse images of those
  standard opens cover `V`: the closed fibre of `V` is empty.
* `Stacks.PuncturedSpectrum.isUnit_baseHomLE_of_le` — on an open contained in the standard open
  of the image of `x`, the image of `x` is a unit.
* `Stacks.PuncturedSpectrum.isZero_derivedTensor_sections_quotient` — the derived tensor product
  of the sections over such an open with `A ⧸ I` vanishes.

## Implementation notes

The opens of the cover are `V.basicOpen (baseHom f x)` for `x ∈ I`, which is the inverse image
of the standard open of `x` by `Stacks.PuncturedSpectrum.basicOpen_baseHom`; their affineness is
`Stacks.PuncturedSpectrum.isAffineOpen_basicOpen_baseHom`. A finite intersection of
them is again one of them, for the product of the elements, which still lies in `I`; the binary
case is `Stacks.PuncturedSpectrum.basicOpen_baseHom_mul` and is the induction step for a Čech
simplex of the cover.

The `A`-module structure on `Γ(V, W)` is the one induced by `f` and restriction, not the one
carried by any particular cohomological model; `Stacks.PuncturedSpectrum.baseAlgebraLE` names it
and `Stacks.PuncturedSpectrum.algebraMap_baseAlgebraLE` identifies its structure map.

### The step of Tag 0ECC that this covers

The proof of [Stacks, Tag 0ECC] uses the vanishing of `RΓ(V, 𝒪_V) ⊗^L_A A/𝔪`, which the source
gets from cohomology and base change applied to the empty closed fibre. The results here are the
input of the Čech form of that argument: the cover, its affineness, and the vanishing on each
member. What is still missing is the comparison, in the derived category of `A`-modules, between
`Stacks.LocalCohomology.derivedSectionsOverBase` and the Čech complex of this cover; no tag is
claimed.

## References

* [Stacks Project, Tag 0ECC](https://stacks.math.columbia.edu/tag/0ECC)
* [Stacks Project, Tag 0ECB](https://stacks.math.columbia.edu/tag/0ECB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.DerivedTensor

universe u

namespace Stacks.PuncturedSpectrum

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {V : Scheme.{u}}

/-! ### The induced ring map on an open -/

/-- The ring map `A → Γ(V, W)` determined by a morphism `f : V ⟶ Spec A` and an open `W ⊆ V`:
the map on global sections followed by restriction. -/
def baseHomLE (f : V ⟶ Spec (CommRingCat.of A)) (W : V.Opens) : A →+* Γ(V, W) :=
  (V.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom.comp (baseHom f)

/-- **`Γ(V, W)` as an `A`-algebra**, through `Stacks.PuncturedSpectrum.baseHomLE`. -/
@[instance_reducible]
def baseAlgebraLE (f : V ⟶ Spec (CommRingCat.of A)) (W : V.Opens) : Algebra A Γ(V, W) :=
  (baseHomLE f W).toAlgebra

/-- The structure map of `Stacks.PuncturedSpectrum.baseAlgebraLE` is
`Stacks.PuncturedSpectrum.baseHomLE`. -/
theorem algebraMap_baseAlgebraLE (f : V ⟶ Spec (CommRingCat.of A)) (W : V.Opens) :
    @algebraMap A Γ(V, W) _ _ (baseAlgebraLE f W) = baseHomLE f W := rfl

/-- `baseHomLE` on the whole of `V` is `baseHom`. -/
theorem baseHomLE_top (f : V ⟶ Spec (CommRingCat.of A)) : baseHomLE f ⊤ = baseHom f := by
  ext x
  change (V.presheaf.map (homOfLE (le_refl (⊤ : V.Opens))).op).hom _ = _
  rw [show (homOfLE (le_refl (⊤ : V.Opens))).op = 𝟙 (op (⊤ : V.Opens)) from rfl]
  simp

/-- `baseHomLE` is compatible with restriction to a smaller open. -/
theorem baseHomLE_of_le (f : V ⟶ Spec (CommRingCat.of A)) {W W' : V.Opens} (h : W' ≤ W) (x : A) :
    baseHomLE f W' x = (V.presheaf.map (homOfLE h).op).hom (baseHomLE f W x) := by
  change (V.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op).hom (baseHom f x) = _
  rw [show (homOfLE (le_top : W' ≤ ⊤)).op =
    (homOfLE (le_top : W ≤ ⊤)).op ≫ (homOfLE h).op from rfl]
  simp [baseHomLE]

/-! ### Invertibility on the standard open -/

/-- The image of `x` in the sections over the standard open of its image is a unit. -/
theorem isUnit_baseHomLE_basicOpen (f : V ⟶ Spec (CommRingCat.of A)) (x : A) :
    IsUnit (baseHomLE f (V.basicOpen (baseHom f x)) x) := by
  have h := RingedSpace.isUnit_res_basicOpen V.toRingedSpace (baseHom f x)
  change IsUnit ((V.presheaf.map (homOfLE (le_top :
    V.basicOpen (baseHom f x) ≤ ⊤)).op).hom (baseHom f x))
  exact h

/-- **On an open contained in the standard open of the image of `x`, the image of `x` is a
unit.** -/
theorem isUnit_baseHomLE_of_le (f : V ⟶ Spec (CommRingCat.of A)) {x : A} {W : V.Opens}
    (hW : W ≤ V.basicOpen (baseHom f x)) : IsUnit (baseHomLE f W x) := by
  rw [baseHomLE_of_le f hW x]
  exact (isUnit_baseHomLE_basicOpen f x).map (V.presheaf.map (homOfLE hW).op).hom

/-! ### The cover -/

/-- A finite intersection of two standard opens of images is the standard open of the image of
the product. -/
theorem basicOpen_baseHom_mul (f : V ⟶ Spec (CommRingCat.of A)) (x y : A) :
    V.basicOpen (baseHom f (x * y)) =
      V.basicOpen (baseHom f x) ⊓ V.basicOpen (baseHom f y) := by
  rw [map_mul, Scheme.basicOpen_mul]

/-- **The standard opens of a generating family of the maximal ideal cover the punctured
spectrum.** -/
theorem puncturedSpectrum_le_iSup_specBasicOpen [IsLocalRing A] {ι : Type*} (s : ι → A)
    (hs : Ideal.span (Set.range s) = IsLocalRing.maximalIdeal A) :
    LocalCohomology.puncturedSpectrum (CommRingCat.of A) ≤ ⨆ i, specBasicOpen A (s i) := by
  intro p hp
  by_contra hcon
  have hall : ∀ i, s i ∈ p.asIdeal := by
    intro i
    by_contra hi
    exact hcon (TopologicalSpace.Opens.mem_iSup.mpr
      ⟨i, (mem_specBasicOpen_iff (s i) p).mpr hi⟩)
  have hspan : IsLocalRing.maximalIdeal A ≤ p.asIdeal := by
    rw [← hs]
    exact Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)
  have hle : p.asIdeal ≤ IsLocalRing.maximalIdeal A :=
    IsLocalRing.le_maximalIdeal p.isPrime.ne_top
  exact hp (PrimeSpectrum.ext (le_antisymm hle hspan))

/-- **The closed fibre of `V` is empty, in the form of a cover.** If the structure morphism of
`V` factors through an open `W ⊆ Spec A` covered by the standard opens of a family `s`, then the
standard opens of the images of the `s i` cover `V`. -/
theorem iSup_basicOpen_baseHom_eq_top {f : V ⟶ Spec (CommRingCat.of A)}
    {W : (Spec (CommRingCat.of A)).Opens} (g : V ⟶ (W : Scheme)) (hg : g ≫ W.ι = f)
    {ι : Type*} (s : ι → A) (hs : W ≤ ⨆ i, specBasicOpen A (s i)) :
    (⨆ i, V.basicOpen (baseHom f (s i))) = ⊤ := by
  refine top_le_iff.mp fun v _ => ?_
  obtain ⟨i, hi⟩ :=
    TopologicalSpace.Opens.mem_iSup.mp (hs (mem_of_comp_ι_eq g hg v))
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩
  rw [basicOpen_baseHom]
  exact hi

/-- **In the situation of [Stacks, Tag 0ECB] the standard opens of a generating family of the
maximal ideal cover `V`.** -/
theorem iSup_basicOpen_baseHom_eq_top_puncturedSpectrum [IsLocalRing A]
    {f : V ⟶ Spec (CommRingCat.of A)}
    (g : V ⟶ (LocalCohomology.puncturedSpectrum (CommRingCat.of A) : Scheme))
    (hg : g ≫ (LocalCohomology.puncturedSpectrum (CommRingCat.of A)).ι = f)
    {ι : Type*} (s : ι → A) (hs : Ideal.span (Set.range s) = IsLocalRing.maximalIdeal A) :
    (⨆ i, V.basicOpen (baseHom f (s i))) = ⊤ :=
  iSup_basicOpen_baseHom_eq_top g hg s (puncturedSpectrum_le_iSup_specBasicOpen s hs)

/-- Each member of the cover is an affine open of `V`. -/
theorem isAffineOpen_basicOpen_baseHom_of_mem (I : Ideal A) {f : V ⟶ Spec (CommRingCat.of A)}
    (g : V ⟶ (LocalCohomology.complementZeroLocus A I : Scheme)) [IsAffineHom g]
    (hg : g ≫ (LocalCohomology.complementZeroLocus A I).ι = f) {x : A} (hx : x ∈ I) :
    IsAffineOpen (V.basicOpen (baseHom f x)) :=
  isAffineOpen_basicOpen_baseHom g hg (specBasicOpen_le_complementZeroLocus I hx)

/-- Each member of the cover is an affine open of `V`, for the punctured spectrum. -/
theorem isAffineOpen_basicOpen_baseHom_of_mem_maximalIdeal [IsLocalRing A]
    {f : V ⟶ Spec (CommRingCat.of A)}
    (g : V ⟶ (LocalCohomology.puncturedSpectrum (CommRingCat.of A) : Scheme)) [IsAffineHom g]
    (hg : g ≫ (LocalCohomology.puncturedSpectrum (CommRingCat.of A)).ι = f) {x : A}
    (hx : x ∈ IsLocalRing.maximalIdeal A) :
    IsAffineOpen (V.basicOpen (baseHom f x)) :=
  isAffineOpen_basicOpen_baseHom g hg (specBasicOpen_le_puncturedSpectrum hx)

/-! ### The vanishing on a member of the cover -/

/-- **The sections over an open on which an element of `I` is invertible are killed by `A ⧸ I`,
derived.** Every `Tor_i^A(Γ(V, W), A ⧸ I)` vanishes, not only the tensor product. -/
theorem isZero_derivedTensor_sections_quotient (I : Ideal A) (f : V ⟶ Spec (CommRingCat.of A))
    {x : A} (hx : x ∈ I) {W : V.Opens} (hW : W ≤ V.basicOpen (baseHom f x))
    [Algebra A Γ(V, W)] (halg : algebraMap A Γ(V, W) = baseHomLE f W) :
    IsZero (((canonicalDerivedTensorProductFunctor A).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A Γ(V, W)))).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ I)))) := by
  refine Stacks.DerivedTensor.isZero_derivedTensor_single_quotient_of_isUnit A I _ hx ?_
  refine Stacks.DerivedTensor.isIso_smul_id_of_isUnit_algebraMap A Γ(V, W) ?_
  rw [halg]
  exact isUnit_baseHomLE_of_le f hW

/-- `Stacks.PuncturedSpectrum.isZero_derivedTensor_sections_quotient` with the canonical
`A`-algebra structure on the sections supplied. -/
theorem isZero_derivedTensor_sections_quotient_baseAlgebra (I : Ideal A)
    (f : V ⟶ Spec (CommRingCat.of A)) {x : A} (hx : x ∈ I) {W : V.Opens}
    (hW : W ≤ V.basicOpen (baseHom f x)) :
    letI := baseAlgebraLE f W
    IsZero (((canonicalDerivedTensorProductFunctor A).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A Γ(V, W)))).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ I)))) :=
  let := baseAlgebraLE f W
  isZero_derivedTensor_sections_quotient I f hx hW (algebraMap_baseAlgebraLE f W)

end Stacks.PuncturedSpectrum

end
