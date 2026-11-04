module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOpenSections
public import StacksFrontier.AlgebraicGeometry.ProjAmple.Basic
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Locality
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistPowers.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistSection.NonvanishingEq
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Absolute
public import StacksFrontier.AlgebraicGeometry.TwistTensor.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `𝒪(d)` is an ample invertible sheaf on `Proj 𝒜` when the degree-`d` opens cover

For a general graded ring `𝒜` the twist `𝒪(1)` is neither invertible nor ample on `X = Proj 𝒜`:
a degree-one element need not exist, and the ratios that would trivialize the twists need not be
defined anywhere. What replaces degree one is a positive `d` with
`AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤`, that is, with the standard opens `D₊(f)` of the
homogeneous elements `f` of degree exactly `d` covering `X`. Such a `d` exists whenever `𝒜` is
Noetherian, and this file proves that for such a `d` the twist `𝒪(d)` is invertible, ample, and
has the twists `𝒪(dn)` as its tensor powers — the three statements the ample machinery of
[Stacks, Tag 0B5Q] consumes, each of which was previously available in this development only for
a ring generated in degree one.

The route is uniform: `degreeOpen 𝒜 d = ⊤` forces Tag 01MU's ratio locus `W_d` to be all of `X`,
because a degree-`d` element `f` contributes the pair `(f, 1)`; and on `W_d` every `d`-divisible
twist is invertible, every multiplication map `𝒪(dn) ⊗ 𝒪(dm) ⟶ 𝒪(dn + dm)` is an isomorphism,
and the nonvanishing locus of the section of `𝒪(d)` attached to `f ∈ 𝒜 d` is exactly `D₊(f)`
(Tag 01MV). Ampleness then needs only that `D₊(f)` is affine, which holds for any homogeneous `f`
of positive degree, and that `X` is quasi-compact, which is the Noetherian hypothesis.

## Main results

* `Stacks.AlgebraicGeometry.ProjAmpleDegree.isInvertible_twistingSheaf` and
  `isInvertibleModule_twistingSheaf`: **`𝒪(d)` is invertible**, in the two classes the ampleness
  API is indexed by — `AlgebraicGeometry.SheafOfModules.IsInvertible` at the
  `toRingedSpace.presheaf` spelling, and `Stacks.Ample.IsInvertibleModule`.
* `Stacks.AlgebraicGeometry.ProjAmpleDegree.nonvanishingOpen_homogeneousSection_eq_basicOpen`:
  the nonvanishing locus of `f / 1` is `D₊(f)`, for `f` homogeneous of degree `d`.
* `Stacks.AlgebraicGeometry.ProjAmpleDegree.isAmple_twistingSheaf`: **`𝒪(d)` is ample on
  `Proj 𝒜`** for `𝒜` Noetherian and `d` positive with `degreeOpen 𝒜 d = ⊤`.
* `Stacks.AlgebraicGeometry.ProjAmpleDegree.tensorPowModuleIsoTwistingSheaf`:
  **`𝒪(d) ^⊗ n ≅ 𝒪(dn)`** for every integer `n`, at the canonical integral tensor power
  `Stacks.Ample.tensorPowModule` of [Stacks, Tag 01CU], with
  `nonempty_tensorPowModule_iso_twistingSheaf` as its propositional form.

## Implementation notes

**No tag attribute is attached.** The statements here are the degree-`d` analogues of
`Stacks.ProjAmple.isAmple_twistingModule_one` and
`Stacks.AlgebraicGeometry.ProjTwistPowers.tensorPowModuleIsoTwistingSheaf`, to which the source
attaches no label either: Tag 01MW's ampleness clause is about an arbitrary quasi-compact open
subscheme of `Proj 𝒜`, and Tag 01CU says nothing about `Proj`.

**`Stacks.ProjTwistSection.twistingModule 𝒜 d` needs no bridge.** It is an `abbrev` for
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf 𝒜 d`, so every statement below is
already a statement about it.

**The degree index is carried as a hypothesis rather than computed.** Tag 01MV is stated at the
twist index `((n * d : ℕ) : ℤ)`, and at `n = 1` that is `1 * d`, which is not definitionally `d`
for a variable `d` — `Nat.mul` recurses on its second argument. Rewriting cannot repair this in
place, because the index occurs in the type of the section. The fix is
`mem_nonvanishingLocus_degreeSection_iff_of_eq`, which takes the index `k` as a variable with
`hk : k = 1 * d` and discharges it by `subst`; it is then instantiated at `k = d`. This is why
the degree-one machinery of `StacksFrontier/AlgebraicGeometry/ProjTwistSection/` is not reused: its
trivializing sections live at the index `n * d` and are pinned to `d = n = 1` for exactly this
reason, as its own implementation notes record.

## References

* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MV](https://stacks.math.columbia.edu/tag/01MV)
* [Stacks Project, Tag 01MW](https://stacks.math.columbia.edu/tag/01MW)
* [Stacks Project, Tag 01N5](https://stacks.math.columbia.edu/tag/01N5)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.AlgebraicGeometry.ProjAmpleDegree

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-! ### Invertibility of `𝒪(d)` -/

/-- **If the degree-`d` standard opens cover `Proj 𝒜` then Tag 01MU's ratio locus `W_d` is all of
`Proj 𝒜`.** A homogeneous `f` of degree `d` contributes the pair `(f, 1)`, whose degrees differ
by `d`, so `D₊(f) ⊆ W_d`; the union of those standard opens is `U_d`, assumed to be everything. -/
theorem ratioLocus_eq_top_of_degreeOpen_eq_top {d : ℕ}
    (htop : AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤) :
    ProjShared.ratioLocus 𝒜 d = ⊤ :=
  top_le_iff.mp (htop ▸ ProjDegreeOpenSections.degreeOpen_le_ratioLocus 𝒜 d)

/-- **`𝒪(d)` is invertible on `Proj 𝒜` when the degree-`d` standard opens cover**, in the class
`AlgebraicGeometry.SheafOfModules.IsInvertible` at the spelling ampleness is stated in.

This is `ProjInvertibleLocus.isInvertible_twistingSheaf_of_ratioLocus_eq_top` at `n = 1`, whose
conclusion is about `𝒪(d * n)`; only the substitution of `d` for `d * 1` is left. -/
@[ega "II 2.5.8" "special case", ega "II 2.6.1" "more general"]
theorem isInvertible_twistingSheaf {d : ℕ}
    (htop : AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤) :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj 𝒜).toRingedSpace.presheaf
      (structureSheafRing (AlgebraicGeometry.Proj 𝒜).toRingedSpace).property
      (twistingSheaf 𝒜 (d : ℤ)) := by
  have h := ProjInvertibleLocus.isInvertible_twistingSheaf_of_ratioLocus_eq_top 𝒜
    (ratioLocus_eq_top_of_degreeOpen_eq_top 𝒜 htop) 1
  rwa [mul_one] at h

/-- **`𝒪(d)` is invertible on `Proj 𝒜`**, in the other realisation of [Stacks, Tag 01CS] that
the tensor-power development of Tag 01CU is indexed by.

`isInvertible_twistingSheaf` proves the same thing by a dual-sheaf argument on the ratio locus;
the tensor powers need the statement assembled from a pointwise local trivialization, which is
what `TwistMapsInvertible` produces. The trivializing section on `D₊(pq)` is the ratio `p / q`
with `deg p = deg q + d`, read at the twist index `1 * d = d`. -/
@[ega "II 2.5.8" "special case", ega "II 2.6.1" "more general", ega "II 8.7.8" "special case"]
theorem isInvertibleModule_twistingSheaf {d : ℕ}
    (htop : AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤) :
    Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 (d : ℤ)) :=
  TwistMapsInvertible.isInvertibleModule_of_forall_exists_restrict_isoUnit _
    fun x => TwistMapsInvertible.exists_mem_restrict_isoUnit_twistingSheaf 𝒜 (d := d) (n := 1)
      (c := (d : ℤ)) (one_mul _)
      ((ratioLocus_eq_top_of_degreeOpen_eq_top 𝒜 htop).ge (TopologicalSpace.Opens.mem_top x))

/-! ### Ampleness of `𝒪(d)` -/

/-- Every point of `Proj 𝒜` lies in Tag 01MU's invertible locus `W_d` when the degree-`d`
standard opens cover: `U_d ⊆ W_d` unconditionally, and `U_d` is everything. -/
theorem mem_whereInvertible_of_degreeOpen_eq_top {d : ℕ}
    (htop : AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤) (x : AlgebraicGeometry.Proj 𝒜) :
    x ∈ ProjInvertibleLocus.whereInvertible 𝒜 d :=
  ProjDegreeOpenSections.degreeOpen_le_whereInvertible 𝒜 d
    (htop ▸ TopologicalSpace.Opens.mem_top x)

/-- **[Stacks, Tag 01MV] at `n = 1`, with the twist index carried as a variable.** At a point of
`W_d` the global section of `𝒪(k)` attached to a homogeneous element of degree `k = 1 * d` is
nonvanishing exactly on that element's standard open. Stating the index as a variable `k` with
`hk : k = 1 * d` is what makes the lemma usable at `k = d`: `1 * d` is not definitionally `d`. -/
theorem mem_nonvanishingLocus_degreeSection_iff_of_eq {d k : ℕ} (hk : k = 1 * d) (f : 𝒜 k)
    {x : ProjectiveSpectrum.top 𝒜} (hx : x ∈ ProjInvertibleLocus.whereInvertible 𝒜 d) :
    x ∈ Stacks.SheafOfModules.nonvanishingLocus
        (X := (AlgebraicGeometry.Proj 𝒜).toRingedSpace) (twistingSheaf 𝒜 (k : ℤ))
        (Stacks.SheafOfModules.sectionsOfTop _ (degreeSection 𝒜 k f)) ↔
      x ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) := by
  subst hk
  exact ProjInvertibleLocus.mem_nonvanishingLocus_degreeSection_iff 𝒜 d 1 f hx

/-- **The nonvanishing locus of `f / 1` is exactly `D₊(f)`, for `f` homogeneous of degree `d`**,
as soon as the degree-`d` standard opens cover `Proj 𝒜`.

This is the degree-`d` replacement for
`Stacks.ProjTwistSection.nonvanishingOpen_homogeneousSection_eq_basicOpen`, whose proof is pinned
at degree one by the trivializing sections it uses. Both inclusions come at once from
[Stacks, Tag 01MV], since the covering hypothesis puts every point in `W_d`. -/
@[ega "II 3.3.3" "affine base Y = Spec A₀"]
theorem nonvanishingOpen_homogeneousSection_eq_basicOpen {d : ℕ}
    [Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj 𝒜).toRingedSpace.presheaf
      (structureSheafRing (AlgebraicGeometry.Proj 𝒜).toRingedSpace).property
      (twistingSheaf 𝒜 (d : ℤ))]
    (htop : AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤) (f : A) (hf : f ∈ 𝒜 d) :
    Stacks.SheafOfModules.nonvanishingOpen (X := (AlgebraicGeometry.Proj 𝒜).toRingedSpace)
        (twistingSheaf 𝒜 (d : ℤ)) (Stacks.ProjTwistSection.homogeneousSection 𝒜 f hf)
      = AlgebraicGeometry.Proj.basicOpen 𝒜 f := by
  ext x
  exact mem_nonvanishingLocus_degreeSection_iff_of_eq 𝒜 (one_mul d).symm ⟨f, hf⟩
    (mem_whereInvertible_of_degreeOpen_eq_top 𝒜 htop x)

/-- `Proj 𝒜` is quasi-compact for `𝒜` Noetherian: it is a Noetherian scheme, and
quasi-compactness is one of the two halves of that. -/
theorem compactSpace_proj [IsNoetherianRing A] : CompactSpace (AlgebraicGeometry.Proj 𝒜) :=
  have := Stacks.AlgebraicGeometry.Proj.isNoetherian_proj 𝒜
  inferInstance

/-- **`𝒪(d)` is an ample invertible sheaf on `Proj 𝒜`** for `𝒜` Noetherian and `d` positive with
`AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤`.

Ampleness is read at exponent one, through
`AlgebraicGeometry.Scheme.Modules.isAmple_of_forall_exists_affine_nonvanishingOpen`. At a point
`x` the covering hypothesis supplies a homogeneous `g` of degree `d` with `x ∈ D₊(g)`; the global
section `g / 1` of `𝒪(d)` has nonvanishing locus exactly `D₊(g)` by
`nonvanishingOpen_homogeneousSection_eq_basicOpen`, and `D₊(g)` is affine because `g` is
homogeneous of positive degree. Quasi-compactness is the Noetherian hypothesis.

Since `Stacks.ProjTwistSection.twistingModule 𝒜 d` is an `abbrev` for `twistingSheaf 𝒜 d`, this
is also the ampleness statement at that spelling. -/
theorem isAmple_twistingSheaf [IsNoetherianRing A] {d : ℕ} (hd : 0 < d)
    (htop : AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤) :
    letI := isInvertible_twistingSheaf 𝒜 htop
    AlgebraicGeometry.Scheme.Modules.IsAmple (AlgebraicGeometry.Proj 𝒜)
      (twistingSheaf 𝒜 (d : ℤ)) := by
  let := isInvertible_twistingSheaf 𝒜 htop
  let : Stacks.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj 𝒜).toRingedSpace.presheaf
      (structureSheafRing (AlgebraicGeometry.Proj 𝒜).toRingedSpace).property
      (twistingSheaf 𝒜 (d : ℤ)) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr inferInstance
  refine AlgebraicGeometry.Scheme.Modules.isAmple_of_forall_exists_affine_nonvanishingOpen
    _ _ (compactSpace_proj 𝒜) fun x => ?_
  obtain ⟨g, hxg⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (htop ▸ TopologicalSpace.Opens.mem_top x :
      x ∈ AlgebraicGeometry.Proj.degreeOpen 𝒜 d)
  have key := nonvanishingOpen_homogeneousSection_eq_basicOpen 𝒜 htop (g : A) g.2
  exact ⟨Stacks.ProjTwistSection.homogeneousSection 𝒜 (g : A) g.2, key.ge hxg,
    Eq.mp (congrArg (IsAffineOpen (X := AlgebraicGeometry.Proj 𝒜)) key).symm
      (AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒜 (g : A) g.2 hd)⟩

/-! ### The tensor powers `𝒪(d) ^⊗ n ≅ 𝒪(dn)` -/

/-- Invertibility of `𝒪(d)` in the `Stacks.SheafOfModules.IsInvertible` class, at the sheaf
condition `ProjTwistPowers.projSheafCond` that the tensor-right functor is keyed on. Instance
search does not cross between the two realisations of [Stacks, Tag 01CS]; the crossing is
`Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`. -/
@[ega "II 2.6.1" "more general"]
theorem stacksIsInvertible_twistingSheaf {d : ℕ}
    (htop : AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤) :
    Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj 𝒜).presheaf
      (ProjTwistPowers.projSheafCond 𝒜) (twistingSheaf 𝒜 (d : ℤ)) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      (AlgebraicGeometry.Proj 𝒜).presheaf (ProjTwistPowers.projSheafCond 𝒜)
      (twistingSheaf 𝒜 (d : ℤ))).mpr (isInvertibleModule_twistingSheaf 𝒜 htop)

/-- **Tensoring on the right by `𝒪(d)` on `Proj 𝒜`**, the degree-`d` analogue of
`Stacks.AlgebraicGeometry.ProjTwistPowers.twistRight`. -/
def twistRightDeg (d : ℕ) :
    (AlgebraicGeometry.Proj 𝒜).Modules ⥤ (AlgebraicGeometry.Proj 𝒜).Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(AlgebraicGeometry.Proj 𝒜).presheaf,
    Presheaf.isSheaf_of_isSheaf_comp _ (AlgebraicGeometry.Proj 𝒜).presheaf
      (forget₂ CommRingCat RingCat) (ProjTwistPowers.projSheafCond 𝒜)⟩).flip.obj
    (twistingSheaf 𝒜 (d : ℤ))

/-- **Tensoring by `𝒪(d)` is an autoequivalence of `𝒪_X`-modules** when the degree-`d` standard
opens cover, because `𝒪(d)` is then invertible. -/
theorem isEquivalence_twistRightDeg {d : ℕ}
    (htop : AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤) :
    (twistRightDeg 𝒜 d).IsEquivalence :=
  let := stacksIsInvertible_twistingSheaf 𝒜 htop
  Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor _ _ _

/-- **Equation 01MO at `(dn, d)` as an isomorphism**, in the functor spelling: tensoring `𝒪(dn)`
on the right by `𝒪(d)` gives `𝒪(d(n + 1))`.

The available input is `TwistTensor.isIso_twistMultiplicationMap_of_ratioLocus_eq_top`, which
inverts the multiplication maps in the degrees `(d * n, d * m)` — exactly the multiples of `d`,
which is all the induction below needs. It is used at `m = 1`, where the second index is `d * 1`;
that is substituted for `d` after `revert`, since the index occurs in the type of the morphism.
The target is then `𝒪(dn + d)`, identified with `𝒪(d(n + 1))` by `eqToIso`. -/
def twistMulIsoDeg {d : ℕ} (htop : AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤) (n : ℤ) :
    (twistRightDeg 𝒜 d).obj (twistingSheaf 𝒜 ((d : ℤ) * n)) ≅
      twistingSheaf 𝒜 ((d : ℤ) * (n + 1)) :=
  @asIso _ _ _ _ (ProjInvertibleLocus.twistMultiplicationMap 𝒜 ((d : ℤ) * n) (d : ℤ))
      (by
        have key := TwistTensor.isIso_twistMultiplicationMap_of_ratioLocus_eq_top 𝒜
          (ratioLocus_eq_top_of_degreeOpen_eq_top 𝒜 htop) n 1
        revert key
        rw [mul_one]
        exact id) ≪≫
    eqToIso (congrArg (twistingSheaf 𝒜) (by ring))

variable (d : ℕ)
  [Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 (d : ℤ))]

/-- **The successor law for the tensor powers of `𝒪(d)`**, in the same functor spelling: the
addition law `Stacks.Ample.tensorPowModuleAddIso` at `(n, 1)`, with the second factor rewritten
from `𝒪(d) ^⊗ 1` to `𝒪(d)` by functoriality of the tensor product. -/
def twistPowSuccIsoDeg (n : ℤ) :
    (twistRightDeg 𝒜 d).obj
        (Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜)
          (twistingSheaf 𝒜 (d : ℤ)) n) ≅
      Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 (d : ℤ)) (n + 1) :=
  show Stacks.RelativeVeryAmple.tensorModules (AlgebraicGeometry.Proj 𝒜)
        (Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜)
          (twistingSheaf 𝒜 (d : ℤ)) n) (twistingSheaf 𝒜 (d : ℤ)) ≅
      Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 (d : ℤ)) (n + 1)
    from
  Stacks.RelativeVeryAmple.tensorModulesMapIso (AlgebraicGeometry.Proj 𝒜) (Iso.refl _)
      (Stacks.Ample.tensorPowModuleOneIso (AlgebraicGeometry.Proj 𝒜)
        (twistingSheaf 𝒜 (d : ℤ))).symm ≪≫
    Stacks.Ample.tensorPowModuleAddIso (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 (d : ℤ)) n 1

/-- **`𝒪(d) ^⊗ n ≅ 𝒪(dn)` on `Proj 𝒜` when the degree-`d` standard opens cover**, for every
integer `n`.

The two families `n ↦ 𝒪(d) ^⊗ n` and `n ↦ 𝒪(dn)` are orbits of the one autoequivalence
`twistRightDeg 𝒜 d` — the first by `twistPowSuccIsoDeg`, the second by `twistMulIsoDeg` — and
they agree at `n = 1`, so `ProjTwistPowers.nonempty_iso_of_shift` identifies them in every
degree, positive and negative alike. The conclusion is a `Nonempty` because the induction over
`ℤ` eliminates into a `Prop`; `tensorPowModuleIsoTwistingSheaf` is the chosen datum.

The instance argument is discharged by `isInvertibleModule_twistingSheaf 𝒜 htop`. -/
theorem nonempty_tensorPowModule_iso_twistingSheaf
    (htop : AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤) (n : ℤ) :
    Nonempty (Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜)
        (twistingSheaf 𝒜 (d : ℤ)) n ≅ twistingSheaf 𝒜 ((d : ℤ) * n)) :=
  let := isEquivalence_twistRightDeg 𝒜 htop
  ProjTwistPowers.nonempty_iso_of_shift (twistRightDeg 𝒜 d)
    (fun m => Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 (d : ℤ)) m)
    (fun m => twistingSheaf 𝒜 ((d : ℤ) * m))
    (fun m => twistPowSuccIsoDeg 𝒜 d m) (fun m => twistMulIsoDeg 𝒜 htop m) (k := 1)
    (Stacks.Ample.tensorPowModuleOneIso (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 (d : ℤ)) ≪≫
      eqToIso (congrArg (twistingSheaf 𝒜) (mul_one ((d : ℤ))).symm)) n

/-- **`𝒪(d) ^⊗ n ≅ 𝒪(dn)` as data**, chosen from `nonempty_tensorPowModule_iso_twistingSheaf`.
This is the degree-`d` form of the `htw` hypothesis that the two [Stacks, Tag 0B5Q] theorems of
`Stacks.AlgebraicGeometry.Tag0B5QAmpleRoute` bind. -/
def tensorPowModuleIsoTwistingSheaf
    (htop : AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤) (n : ℤ) :
    Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 (d : ℤ)) n ≅
      twistingSheaf 𝒜 ((d : ℤ) * n) :=
  (nonempty_tensorPowModule_iso_twistingSheaf 𝒜 d htop n).some

end Stacks.AlgebraicGeometry.ProjAmpleDegree

end
