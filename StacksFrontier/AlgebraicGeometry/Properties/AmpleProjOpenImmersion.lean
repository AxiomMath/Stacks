module

public import StacksFrontier.AlgebraicGeometry.CommonDegreeTwist.AffineSectionBasis
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.SectionExtension.AmpleConsumers
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A quasi-compact open subscheme of `Proj(S)` carries an ample twist

Let `S` be a graded ring and `j : X ⟶ Proj(S)` an open immersion of a quasi-compact scheme. Then
`j^* 𝒪(d)` is an invertible ample `𝒪_X`-module for some `d > 0`: take for `d` the common degree of
a finite cover of the image of `j` by standard opens, which exists because the image is
quasi-compact.

## Main results

* `Stacks.AlgebraicGeometry.ProjAmpleTwist.isAmple_restrictedTwist`: for `Y` an open of `Proj(S)`
  with quasi-compact underlying space covered by standard opens of one common positive degree
  `d`, the restriction `𝒪_Y(d)` is ample.
* `Stacks.AlgebraicGeometry.ProjAmpleTwist.exists_isAmple_pullback_twistingSheaf`:
  **Stacks Tag 01Q2.**

## The route

The affine nonvanishing opens of the twists `𝒪_Y(nd)` are a basis for the topology of `Y`
(Stacks Tag 01MW (7), `Stacks.AlgebraicGeometry.CommonDegreeTwist`), so in particular every point
of `Y` lies in an affine one; that is exactly the condition of Stacks Tag 01PS, *except* that it
is phrased over the twists rather than over the tensor powers of `𝒪_Y(d)`. The comparison
`(𝒪_Y(d))^{⊗ n} ≅ 𝒪_Y(nd)` is `nonempty_tensorPowModule_iso` below: an induction on `n` whose
step tensors by one more copy of `𝒪_Y(d)`, commutes the pullback past the tensor product
(Stacks Tag 01CD, `Stacks.RelativeVeryAmple.pullbackTensorModulesIso`) and then multiplies the
two twists together, the multiplication map being an isomorphism on `Y` by Stacks Tag 01MU.

From `Y` the statement is carried to `X` by Stacks Tag 0B3E,
`Stacks.SectionExtension.isAmple_pullbackModule`, along the isomorphism `X ≅ Y` onto the image,
and then transported along `(X ≅ Y)^* 𝒪_Y(d) ≅ j^* 𝒪(d)` by
`Stacks.RelativeVeryAmple.isAmple_congr`. Both steps are unconditional.

## Implementation notes

Only nonnegative tensor powers are compared, which is all `Stacks.Ample.IsAmple` can see.

The comparison of the powers with the twists is produced as a `Nonempty`, not as a family of
isomorphisms: ampleness is a proposition and uses only one degree at a time, so nothing is gained
by naming the isomorphism, and the recursion stays inside a proof.

Invertibility of a module is transported along an isomorphism through the two classes realising
Stacks Tag 01CS and the bridge between them,
`Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`: the transport
`Stacks.SheafOfModules.isInvertible_of_iso` is stated for the class Tag 01CU's tensor powers use,
and the ampleness theory uses the other one.

## References

* [Stacks Project, Tag 01Q2](https://stacks.math.columbia.edu/tag/01Q2)
* [Stacks Project, Tag 01MW](https://stacks.math.columbia.edu/tag/01MW)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.AlgebraicGeometry.CommonDegreeTwist
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.RelativeVeryAmple

namespace Stacks.AlgebraicGeometry.ProjAmpleTwist

universe u w

/-! ### Invertibility is an invariant of the isomorphism class -/

/-- **Invertibility of an `𝒪_X`-module depends only on its isomorphism class.** The transport is
available for the class Stacks Tag 01CU's tensor powers are stated with,
`Stacks.SheafOfModules.IsInvertible`; this reads it off for the class the ampleness theory uses.
-/
theorem isInvertibleModule_of_iso {X : Scheme.{u}} {N N' : X.Modules}
    [IsInvertibleModule X N] (e : N ≅ N') : IsInvertibleModule X N' := by
  have : Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) N :=
    Stacks.PowerFamilyBridge.instIsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) N
  exact (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) N').mp
    (Stacks.SheafOfModules.isInvertible_of_iso X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) e)

section Proj

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-! ### The divisible twists on a common-degree open -/

/-- **Stacks Tag 01MW (2).** A twist whose degree is a multiple of the common degree of the cover
restricts to an invertible module on the covered open. -/
theorem isInvertibleModule_restrictedTwist (Y : (AlgebraicGeometry.Proj 𝒮).Opens)
    (C : AlgebraicGeometry.Proj.CommonDegreeCover 𝒮 Y) {c : ℤ} (n : ℤ)
    (hc : c = (C.degree : ℤ) * n) :
    IsInvertibleModule Y.toScheme (restrictedTwist 𝒮 Y c) := by
  subst hc
  exact isInvertible_restrict_twistingSheaf_mul_degree 𝒮 Y C n

/-- **Stacks Tag 01MU on a common-degree open.** The multiplication map
`𝒪(dn) ⊗ 𝒪(dm) ⟶ 𝒪(dn + dm)` becomes an isomorphism after restriction to the covered open. -/
theorem isIso_pullback_twistMultiplicationMap (Y : (AlgebraicGeometry.Proj 𝒮).Opens)
    (C : AlgebraicGeometry.Proj.CommonDegreeCover 𝒮 Y) (n m : ℤ) :
    IsIso ((modulePullback Y.ι.toLRSHom.toShHom).map
      (twistMultiplicationMap 𝒮 ((C.degree : ℤ) * n) ((C.degree : ℤ) * m))) := by
  have hgood : IsGoodOpen 𝒮 C.degree Y :=
    (GoodOpenClose.isGoodOpen_iff_le_whereInvertible 𝒮 C.degree Y).mpr
      (le_whereInvertible 𝒮 Y C)
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback Y.ι)
    (twistMultiplicationMap 𝒮 ((C.degree : ℤ) * n) ((C.degree : ℤ) * m))).mp (hgood.2 n m)

/-! ### The tensor powers of the degree-`d` twist are the divisible twists -/

section Powers

variable (Y : (AlgebraicGeometry.Proj 𝒮).Opens)
  (C : AlgebraicGeometry.Proj.CommonDegreeCover 𝒮 Y)
  [IsInvertibleModule Y.toScheme (restrictedTwist 𝒮 Y (C.degree : ℤ))]

/-- The `(k+1)`-st tensor power of `𝒪_Y(d)` is `𝒪_Y(d(k+1))`. The inductive step tensors by one
more copy of `𝒪_Y(d)`, commutes the restriction past the tensor product by Stacks Tag 01CD and
multiplies the two twists, which is an isomorphism on `Y` by Stacks Tag 01MU. -/
private theorem nonempty_tensorPowModule_iso_aux : ∀ k : ℕ,
    Nonempty (tensorPowModule Y.toScheme (restrictedTwist 𝒮 Y (C.degree : ℤ))
        ((k + 1 : ℕ) : ℤ) ≅
      restrictedTwist 𝒮 Y ((C.degree : ℤ) * ((k + 1 : ℕ) : ℤ))) := by
  have tw {a b : ℤ} (h : a = b) : restrictedTwist 𝒮 Y a ≅ restrictedTwist 𝒮 Y b :=
    eqToIso (congrArg _ h)
  have one : tensorPowModule Y.toScheme (restrictedTwist 𝒮 Y (C.degree : ℤ)) 1 ≅
      restrictedTwist 𝒮 Y ((C.degree : ℤ) * 1) :=
    tensorPowModuleOneIso Y.toScheme (restrictedTwist 𝒮 Y (C.degree : ℤ)) ≪≫ tw (by ring)
  intro k
  induction k with
  | zero =>
      exact ⟨tensorPowModuleCongr Y.toScheme (restrictedTwist 𝒮 Y (C.degree : ℤ))
        (show ((0 + 1 : ℕ) : ℤ) = 1 from by norm_num) ≪≫ one ≪≫ tw (by push_cast; ring)⟩
  | succ k ih =>
      obtain ⟨e⟩ := ih
      have hmul := isIso_pullback_twistMultiplicationMap 𝒮 Y C ((k + 1 : ℕ) : ℤ) 1
      exact ⟨tensorPowModuleCongr Y.toScheme (restrictedTwist 𝒮 Y (C.degree : ℤ))
            (show ((k + 1 + 1 : ℕ) : ℤ) = ((k + 1 : ℕ) : ℤ) + 1 from by push_cast; ring) ≪≫
          (tensorPowModuleAddIso Y.toScheme (restrictedTwist 𝒮 Y (C.degree : ℤ))
            ((k + 1 : ℕ) : ℤ) 1).symm ≪≫
          tensorModulesMapIso Y.toScheme e one ≪≫
          (pullbackTensorModulesIso Y.ι
            (twistingSheaf 𝒮 ((C.degree : ℤ) * ((k + 1 : ℕ) : ℤ)))
            (twistingSheaf 𝒮 ((C.degree : ℤ) * 1))).symm ≪≫
          @asIso _ _ _ _ _ hmul ≪≫ tw (by push_cast; ring)⟩

/-- The `n`-th tensor power of `𝒪_Y(d)` is `𝒪_Y(nd)`, for `n ≥ 1`. -/
private theorem nonempty_tensorPowModule_iso (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (tensorPowModule Y.toScheme (restrictedTwist 𝒮 Y (C.degree : ℤ)) (n : ℤ) ≅
      restrictedTwist 𝒮 Y ((n * C.degree : ℕ) : ℤ)) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨e⟩ := nonempty_tensorPowModule_iso_aux 𝒮 Y C k
  exact ⟨e ≪≫ eqToIso (congrArg (restrictedTwist 𝒮 Y)
    (show (C.degree : ℤ) * ((k + 1 : ℕ) : ℤ) = (((k + 1) * C.degree : ℕ) : ℤ) from by
      push_cast; ring))⟩

/-- **Stacks Tag 01Q2 on the open subscheme.** If `Y` is an open of `Proj(S)` with quasi-compact
underlying space admitting a finite cover by standard opens defined by homogeneous elements of
one common positive degree `d`, then `𝒪_Y(d)` is ample. -/
theorem isAmple_restrictedTwist (hc : CompactSpace Y.toScheme) :
    IsAmple Y.toScheme (restrictedTwist 𝒮 Y (C.degree : ℤ)) := by
  refine (isAmple_iff Y.toScheme _).mpr ((isAmpleForPowers_iff Y.toScheme _).mpr ⟨hc, fun y => ?_⟩)
  obtain ⟨V, ⟨n, hn, sV, hVaff, hVeq⟩, hyV, -⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_affineNonvanishing_restrictedTwist 𝒮 Y C)
      (show y ∈ (⊤ : Y.toScheme.Opens) from Opens.mem_top y)
  obtain ⟨e⟩ := nonempty_tensorPowModule_iso 𝒮 Y C n hn
  refine ⟨n, hn, e.inv.app ⊤ sV, V, ?_, hyV, hVaff⟩
  rw [hVeq]
  exact (nonvanishingLocus_congr e.symm sV).symm

end Powers

/-! ### Stacks Tag 01Q2 -/

/-- The restriction of `𝒪(c)` to the image of an open immersion, pulled back to the source, is
the pullback of `𝒪(c)` along the open immersion itself. -/
noncomputable def opensRangeTwistIso {X : Scheme.{u}} (j : X ⟶ AlgebraicGeometry.Proj 𝒮)
    [IsOpenImmersion j] (c : ℤ) :
    (modulePullback (Scheme.Hom.isoOpensRange j).hom.toLRSHom.toShHom).obj
        (restrictedTwist 𝒮 j.opensRange c) ≅
      (modulePullback j.toLRSHom.toShHom).obj (twistingSheaf 𝒮 c) :=
  (Scheme.Modules.pullbackComp (Scheme.Hom.isoOpensRange j).hom j.opensRange.ι).app
      (twistingSheaf 𝒮 c) ≪≫
    (Scheme.Modules.pullbackCongr (Scheme.Hom.isoOpensRange_hom_ι j)).app (twistingSheaf 𝒮 c)

/-- **Stacks Project, Tag 01Q2.** Let `X` be a quasi-compact scheme and `S` a graded ring, and
assume there is an open immersion `j : X ⟶ Proj(S)`. Then `j^* 𝒪(d)` is an invertible ample
`𝒪_X`-module for some `d > 0`. -/
@[stacks 01Q2, ega "II 8.14.4" "invertible for some d"]
theorem exists_isAmple_pullback_twistingSheaf {X : Scheme.{u}} [CompactSpace X]
    (j : X ⟶ AlgebraicGeometry.Proj 𝒮) [IsOpenImmersion j] :
    ∃ d : ℕ, 0 < d ∧ ∃ h : IsInvertibleModule X
        ((modulePullback j.toLRSHom.toShHom).obj (twistingSheaf 𝒮 (d : ℤ))),
      @IsAmple X ((modulePullback j.toLRSHom.toShHom).obj (twistingSheaf 𝒮 (d : ℤ))) h := by
  classical
  have hcompact : IsCompact (j.opensRange : Set (AlgebraicGeometry.Proj 𝒮)) := by
    rw [← Scheme.Hom.image_top_eq_opensRange j]
    simpa using isCompact_univ.image j.continuous
  obtain ⟨d, hd, t, ht, hcover⟩ :=
    AlgebraicGeometry.Proj.exists_common_degree_finite_basicOpen_cover 𝒮 j.opensRange hcompact
  set C : AlgebraicGeometry.Proj.CommonDegreeCover 𝒮 j.opensRange :=
    ⟨d, hd, t, ht, hcover.symm⟩ with hC
  have hinvY : IsInvertibleModule (j.opensRange).toScheme
      (restrictedTwist 𝒮 j.opensRange (C.degree : ℤ)) :=
    isInvertibleModule_restrictedTwist 𝒮 j.opensRange C 1 (by ring)
  have hcY : CompactSpace (j.opensRange).toScheme := isCompact_iff_compactSpace.mp hcompact
  have hAmpleY : IsAmple (j.opensRange).toScheme
      (restrictedTwist 𝒮 j.opensRange (C.degree : ℤ)) :=
    isAmple_restrictedTwist 𝒮 j.opensRange C hcY
  have hAmpleX : IsAmple X
      ((modulePullback (Scheme.Hom.isoOpensRange j).hom.toLRSHom.toShHom).obj
        (restrictedTwist 𝒮 j.opensRange (C.degree : ℤ))) :=
    Stacks.SectionExtension.isAmple_pullbackModule (Scheme.Hom.isoOpensRange j).hom
      (restrictedTwist 𝒮 j.opensRange (C.degree : ℤ)) hAmpleY
      (Or.inr (Or.inl ⟨‹CompactSpace X›, inferInstance⟩))
  have hinvX : IsInvertibleModule X
      ((modulePullback j.toLRSHom.toShHom).obj (twistingSheaf 𝒮 (C.degree : ℤ))) :=
    isInvertibleModule_of_iso (opensRangeTwistIso 𝒮 j (C.degree : ℤ))
  exact ⟨C.degree, C.degree_pos, hinvX,
    (isAmple_congr _ _ (opensRangeTwistIso 𝒮 j (C.degree : ℤ))).mp hAmpleX⟩

end Proj

end Stacks.AlgebraicGeometry.ProjAmpleTwist

end
