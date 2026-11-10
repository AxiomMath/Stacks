module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.UnramifiedCharacterizations
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherentFrom
import StacksCore.Tactic.StacksAttribute

/-!
# The local closed-immersion criterion for unramifiedness at a point

Let `Y` be a locally Noetherian scheme, `f : X ⟶ Y` a morphism locally of finite type and `x` a
point of `X`. Condition (3) of Stacks Tag 024P asks for open neighbourhoods `U` of `x` and `V` of
`f x` and a factorization of `f|_U : U ⟶ V` through a closed immersion `i : U ⟶ 𝔸ⁿ_V` whose
defining ideal has the property that the differentials of its germs at `i x` generate
`Ω_{𝔸ⁿ_V/V, i x}`. This file adds that condition to the characterizations of unramifiedness at a
point, completing Tag 024P.

## Main definitions

* `AlgebraicGeometry.IdealDifferentialsGenerateAt` is the generation property: the differentials
  of the ideal of a morphism `i` generate the stalk of the relative differentials of `g` at the
  image point.
* `AlgebraicGeometry.HasDifferentialPresentationAt` is condition (3) of Tag 024P.

## Main results

* `AlgebraicGeometry.stalkwiseUnramifiedAt_iff_hasDifferentialPresentationAt` is the equivalence
  of condition (3) with unramifiedness at the point, and
  `AlgebraicGeometry.stalkwiseUnramifiedAt_tfae₄` is the resulting four-term equivalence, which
  is Tag 024P in full.
* `Stacks.KaehlerDifferential.span_D_ker_eq_top_iff_subsingleton` is the underlying algebra: for a
  surjection `A ⟶ B` of `R`-algebras, the differentials of the kernel generate `Ω[A⁄R]` exactly
  when `Ω[B⁄R]` vanishes.

## Implementation notes

The ideal `𝓘_{i x}` of the source's condition (3) is realized as `RingHom.ker (i.stalkMap x)`.
For a closed immersion `i` the defining quasi-coherent ideal sheaf is `ker (𝒪_W ⟶ i_* 𝒪_U)`, and
taking stalks at a point `p = i x` of the image is exact, so its stalk at `p` is the kernel of
`i`'s map of local rings; the quasi-coherence demanded by the source is automatic for a closed
immersion and therefore carries no information. The stalk `Ω_{𝔸ⁿ_V/V, i x}` is realized as
`Ω[𝒪_{𝔸ⁿ_V, i x} ⁄ 𝒪_{V, π (i x)}]`: the two are identified, compatibly with the universal
derivation, by `Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv` and
`Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv_germ_d`, which sends
the germ at `i x` of `d s` to the universal differential of the germ of `s`.

The commutative triangle of the source is recorded as
`i ≫ (AffineSpace.over _ V).hom = f.resLE V U hUV`, that is, `i` followed by the structure
morphism of `𝔸ⁿ_V` is the restriction of `f` to `U` over `V`, which is exactly what the source's
diagram asserts. The closed immersion needed for the implication (2) ⟹ (3) is
`AlgebraicGeometry.exists_isClosedImmersion_affineSpace_resLE`, a presentation of the sections
over an affine open of the source as a quotient of a polynomial algebra over the sections on an
affine open of the target.

Both implications are proved by one computation at the level of local rings. The three local rings
`𝒪_{V, π (i x)} ⟶ 𝒪_{𝔸ⁿ_V, i x} ⟶ 𝒪_{U, x}` form a scalar tower in which the second map is
surjective because `i` is a closed immersion, so
`Stacks.KaehlerDifferential.span_D_ker_eq_top_iff_subsingleton` applies; the resulting vanishing of
`Ω[𝒪_{U,x} ⁄ 𝒪_{V, π (i x)}]` is compared with unramifiedness of `f` at `x` by cancelling the two
isomorphisms `U.ι.stalkMap x` and `V.ι.stalkMap (π (i x))` against
`RingHom.FormallyUnramified.respectsIso`. The locally Noetherian hypothesis is carried only
because `AlgebraicGeometry.StalkwiseUnramifiedAt` is stated under it: the source uses it to make
`Ω_{B/A}` a finite module and then shrinks `X` until that module vanishes identically, and none of
that is needed once the argument is run at the stalk, where
`Stacks.KaehlerDifferential.span_D_ker_eq_top_iff_subsingleton` applies with no finiteness
assumption.

## References

* [Stacks Project, Tag 024P](https://stacks.math.columbia.edu/tag/024P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.KaehlerDifferential

variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
  [Algebra R B] [IsScalarTower R A B]

/-- **The differentials of the kernel span the kernel of `Ω[A⁄R] → Ω[B⁄R]`.** If `A → B` is a
surjection of `R`-algebras with kernel `I` and `Ω[B⁄R]` vanishes, then the differentials `d a`
for `a ∈ I` generate `Ω[A⁄R]`. -/
theorem span_D_ker_eq_top_of_subsingleton
    (hsurj : Function.Surjective (algebraMap A B)) [Subsingleton Ω[B⁄R]] :
    Submodule.span A (_root_.KaehlerDifferential.D R A ''
      (RingHom.ker (algebraMap A B) : Set A)) = ⊤ := by
  set I := RingHom.ker (algebraMap A B) with hI
  set N := Submodule.span A (_root_.KaehlerDifferential.D R A '' (I : Set A)) with hN
  have hD (a : A) (ha : a ∈ I) : _root_.KaehlerDifferential.D R A a ∈ N :=
    Submodule.subset_span ⟨a, ha, rfl⟩
  have hmul (a : A) (ha : a ∈ I) (w : Ω[A⁄R]) : a • w ∈ N := by
    have hw : w ∈ Submodule.span A (Set.range (_root_.KaehlerDifferential.D R A)) := by
      rw [_root_.KaehlerDifferential.span_range_derivation]
      trivial
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨b, rfl⟩ := hw
      have hab := N.sub_mem (hD (a * b) (I.mul_mem_right b ha)) (N.smul_mem b (hD a ha))
      simpa only [Derivation.leibniz, add_sub_cancel_right] using hab
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [smul_add] using N.add_mem ihx ihy
    | smul b w hw ih => simpa only [smul_comm a b w] using N.smul_mem b ih
  have hker (w : Ω[A⁄R]) (hw : (1 : B) ⊗ₜ[A] w = 0) : w ∈ N := by
    have he := rTensor_exact Ω[A⁄R]
      (LinearMap.exact_subtype_ker_map (Algebra.linearMap A B)) hsurj
    have hh : (Algebra.linearMap A B).rTensor Ω[A⁄R] ((1 : A) ⊗ₜ[A] w) = 0 := by simpa using hw
    obtain ⟨z, hz⟩ := (he _).mp hh
    have hzN : (TensorProduct.lid A Ω[A⁄R])
        (((Algebra.linearMap A B).ker.subtype.rTensor Ω[A⁄R]) z) ∈ N := by
      clear hz
      induction z using TensorProduct.inductionOn with
      | tmul a w => exact hmul a.1 a.2 w
      | add z z' hz hz' => simpa only [map_add] using N.add_mem hz hz'
    simpa only [hz, TensorProduct.lid_tmul, one_smul] using hzN
  apply top_unique
  intro w _
  have he := _root_.KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B hsurj
  obtain ⟨c, hc⟩ := (he ((1 : B) ⊗ₜ[A] w)).mp (Subsingleton.elim _ _)
  obtain ⟨a, rfl⟩ := I.toCotangent_surjective c
  rw [_root_.KaehlerDifferential.kerCotangentToTensor_toCotangent] at hc
  have hw : w - _root_.KaehlerDifferential.D R A a.1 ∈ N :=
    hker _ (by rw [TensorProduct.tmul_sub, hc, sub_self])
  exact (N.sub_mem_iff_left (hD a a.2)).mp hw

/-- **The differentials of the kernel generate exactly when the quotient has no differentials.**
For a surjection `A → B` of `R`-algebras with kernel `I`, the differentials `d a` for `a ∈ I`
generate `Ω[A⁄R]` if and only if `Ω[B⁄R]` is trivial. -/
theorem span_D_ker_eq_top_iff_subsingleton (hsurj : Function.Surjective (algebraMap A B)) :
    Submodule.span A (_root_.KaehlerDifferential.D R A ''
        (RingHom.ker (algebraMap A B) : Set A)) = ⊤ ↔ Subsingleton Ω[B⁄R] := by
  refine ⟨fun hspan ↦ ?_, fun _ ↦ span_D_ker_eq_top_of_subsingleton R A B hsurj⟩
  have hle : Submodule.span A (_root_.KaehlerDifferential.D R A ''
      (RingHom.ker (algebraMap A B) : Set A)) ≤
      LinearMap.ker (_root_.KaehlerDifferential.map R R A B) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    have ha' : algebraMap A B a = 0 := ha
    simp [LinearMap.mem_ker, ha']
  rw [hspan, top_le_iff, LinearMap.ker_eq_top] at hle
  refine ⟨fun y z ↦ ?_⟩
  obtain ⟨y', rfl⟩ := _root_.KaehlerDifferential.map_surjective_of_surjective R R A B hsurj y
  obtain ⟨z', rfl⟩ := _root_.KaehlerDifferential.map_surjective_of_surjective R R A B hsurj z
  rw [hle]
  rfl

end Stacks.KaehlerDifferential

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **The differentials of the ideal of `i` generate the relative differentials of `g` at
`i z`.** For morphisms `i : U ⟶ W` and `g : W ⟶ V`, this is the condition that the differentials
of the germs at `i z` of the ideal defining `i` generate the stalk of `Ω_{W/V}` at `i z`, where
that stalk is read as the Kähler differentials of `g`'s map of local rings and the stalk of the
ideal as the kernel of `i`'s map of local rings. -/
def IdealDifferentialsGenerateAt {U W V : Scheme.{u}} (g : W ⟶ V) (i : U ⟶ W) (z : U) : Prop :=
  let : Algebra ↥(V.presheaf.stalk (g (i z))) ↥(W.presheaf.stalk (i z)) :=
    (g.stalkMap (i z)).hom.toAlgebra
  Submodule.span ↥(W.presheaf.stalk (i z))
    (KaehlerDifferential.D ↥(V.presheaf.stalk (g (i z))) ↥(W.presheaf.stalk (i z)) ''
      (RingHom.ker (i.stalkMap z).hom : Set ↥(W.presheaf.stalk (i z)))) = ⊤

/-- **Condition (3) of Stacks Tag 024P.** There are open neighbourhoods `U` of `x` and `V` of
`f x` and a commutative triangle `U ⟶ 𝔸ⁿ_V ⟶ V` over `V` whose second leg is the restriction of
`f`, in which the first map is a closed immersion whose defining ideal has differentials
generating `Ω_{𝔸ⁿ_V/V}` at the image of `x`. -/
def HasDifferentialPresentationAt (f : X ⟶ Y) (x : X) : Prop :=
  ∃ (U : X.Opens) (hxU : x ∈ U) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (n : ℕ)
      (i : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.toScheme),
    IsClosedImmersion i ∧
      i ≫ (AffineSpace.over (ULift.{u} (Fin n)) V.toScheme).hom = f.resLE V U hUV ∧
      IdealDifferentialsGenerateAt
        (AffineSpace.over (ULift.{u} (Fin n)) V.toScheme).hom i ⟨x, hxU⟩

/-- **The map of local rings of a composite is formally unramified exactly when the generation
condition holds.** For `i : U ⟶ W` surjective on stalks and `g : W ⟶ V`, formal unramifiedness of
the map of local rings of `i ≫ g` at `z` is the statement that the differentials of
`ker (i.stalkMap z)` generate `Ω_{W/V}` at `i z`. -/
theorem formallyUnramified_comp_stalkMap_iff {U W V : Scheme.{u}} (i : U ⟶ W) (g : W ⟶ V)
    [SurjectiveOnStalks i] (z : U) :
    ((i ≫ g).stalkMap z).hom.FormallyUnramified ↔ IdealDifferentialsGenerateAt g i z := by
  let : Algebra ↥(V.presheaf.stalk (g (i z))) ↥(W.presheaf.stalk (i z)) :=
    (g.stalkMap (i z)).hom.toAlgebra
  let : Algebra ↥(W.presheaf.stalk (i z)) ↥(U.presheaf.stalk z) :=
    (i.stalkMap z).hom.toAlgebra
  let : Algebra ↥(V.presheaf.stalk (g (i z))) ↥(U.presheaf.stalk z) :=
    ((i ≫ g).stalkMap z).hom.toAlgebra
  have : IsScalarTower ↥(V.presheaf.stalk (g (i z))) ↥(W.presheaf.stalk (i z))
      ↥(U.presheaf.stalk z) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((i ≫ g).stalkMap z).hom = (i.stalkMap z).hom.comp (g.stalkMap (i z)).hom
    exact congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp i g z)
  have hsurj : Function.Surjective
      (algebraMap ↥(W.presheaf.stalk (i z)) ↥(U.presheaf.stalk z)) :=
    i.stalkMap_surjective z
  exact ⟨fun h ↦ (Stacks.KaehlerDifferential.span_D_ker_eq_top_iff_subsingleton _ _ _ hsurj).mpr
      ((Algebra.formallyUnramified_iff _ _).mp (RingHom.formallyUnramified_algebraMap.mp h)),
    fun h ↦ RingHom.formallyUnramified_algebraMap.mpr ((Algebra.formallyUnramified_iff _ _).mpr
      ((Stacks.KaehlerDifferential.span_D_ker_eq_top_iff_subsingleton _ _ _ hsurj).mp h))⟩

/-- The map of local rings of an open immersion is an isomorphism. -/
theorem isIso_opens_ι_stalkMap (U : X.Opens) (z : U) : IsIso (U.ι.stalkMap z) := by
  rw [← Scheme.Opens.stalkIso_inv]
  exact (U.stalkIso z).symm.isIso_hom

/-- **Unramifiedness at `x` is the generation condition, for any factorization of a restriction
of `f` through a morphism surjective on stalks.** If `i : U ⟶ W` is surjective on stalks and
`i ≫ g` is the restriction of `f` to `U` over `V`, then `f` is unramified at `x` exactly when the
differentials of `ker (i.stalkMap x)` generate the relative differentials of `g` at `i x`. -/
theorem stalkwiseUnramifiedAt_iff_idealDifferentialsGenerateAt (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] {x : X} {U : X.Opens} (hxU : x ∈ U)
    {V : Y.Opens} (hUV : U ≤ f ⁻¹ᵁ V) {W : Scheme.{u}} (i : U.toScheme ⟶ W)
    [SurjectiveOnStalks i] (g : W ⟶ V.toScheme) (htri : i ≫ g = f.resLE V U hUV) :
    StalkwiseUnramifiedAt f x ↔ IdealDifferentialsGenerateAt g i ⟨x, hxU⟩ := by
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  set z : U.toScheme := ⟨x, hxU⟩
  have hcomm : (i ≫ g) ≫ V.ι = U.ι ≫ f := by
    rw [htri, Scheme.Hom.resLE_comp_ι]
  have e1 : ((U.ι ≫ f).stalkMap z).hom = (U.ι.stalkMap z).hom.comp (f.stalkMap x).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp U.ι f z)
  have e3 : (((i ≫ g) ≫ V.ι).stalkMap z).hom =
      ((i ≫ g).stalkMap z).hom.comp (V.ι.stalkMap ((i ≫ g) z)).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp (i ≫ g) V.ι z)
  have step1 : StalkwiseUnramifiedAt f x ↔ ((U.ι ≫ f).stalkMap z).hom.FormallyUnramified := by
    rw [e1]
    exact RingHom.formallyUnramified_algebraMap.symm.trans
      (@RingHom.RespectsIso.cancel_right_isIso _ RingHom.FormallyUnramified.respectsIso
        _ _ _ (f.stalkMap x) (U.ι.stalkMap z) (isIso_opens_ι_stalkMap U z)).symm
  have step2 : ((U.ι ≫ f).stalkMap z).hom.FormallyUnramified ↔
      (((i ≫ g) ≫ V.ι).stalkMap z).hom.FormallyUnramified := by rw [hcomm]
  have step3 : (((i ≫ g) ≫ V.ι).stalkMap z).hom.FormallyUnramified ↔
      ((i ≫ g).stalkMap z).hom.FormallyUnramified := by
    rw [e3]
    exact @RingHom.RespectsIso.cancel_left_isIso _ RingHom.FormallyUnramified.respectsIso
      _ _ _ (V.ι.stalkMap ((i ≫ g) z)) ((i ≫ g).stalkMap z)
      (isIso_opens_ι_stalkMap V ((i ≫ g) z))
  exact step1.trans (step2.trans (step3.trans (formallyUnramified_comp_stalkMap_iff i g z)))

/-- **Stacks Project, Tag 024P, condition (3).** For a morphism locally of finite type to a
locally Noetherian scheme, unramifiedness at `x` is equivalent to the existence of a local closed
immersion into an affine space over an open of the target whose defining ideal has generating
differentials at the image of `x`. -/
@[stacks 024P "equivalence of conditions (1) and (3)"]
theorem stalkwiseUnramifiedAt_iff_hasDifferentialPresentationAt (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] (x : X) :
    StalkwiseUnramifiedAt f x ↔ HasDifferentialPresentationAt f x := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨V, hV, hfxV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Y) (x := f x) (U := ⊤) trivial
    obtain ⟨U, hU, hxU, hUsub⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := f ⁻¹ᵁ V) hfxV
    have hUV : U ≤ f ⁻¹ᵁ V := hUsub
    obtain ⟨n, i, hi, hbase⟩ :=
      exists_isClosedImmersion_affineSpace_resLE f ⟨V, hV⟩ ⟨U, hU⟩ hUV
    exact ⟨U, hxU, V, hUV, n, i, hi, hbase,
      (stalkwiseUnramifiedAt_iff_idealDifferentialsGenerateAt f hxU hUV i _ hbase).mp h⟩
  · rintro ⟨U, hxU, V, hUV, n, i, hi, hbase, hspan⟩
    exact (stalkwiseUnramifiedAt_iff_idealDifferentialsGenerateAt f hxU hUV i _ hbase).mpr hspan

/-- **Stacks Project, Tag 024P.** Let `Y` be a locally Noetherian scheme, `f : X ⟶ Y` a morphism
locally of finite type and `x` a point of `X`. The following are equivalent: `f` is unramified at
`x`; the stalk at `x` of the sheaf of relative differentials of `f` vanishes; `f` restricts near
`x` to a closed immersion into an affine space over an open of `Y` whose defining ideal has
generating differentials at the image of `x`; and the diagonal `Δ_{X/Y}` is a local isomorphism
at `x`. -/
@[stacks 024P "equivalence of conditions (1), (2), (3) and (4)"]
theorem stalkwiseUnramifiedAt_tfae₄ (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    (x : X) :
    List.TFAE [
      StalkwiseUnramifiedAt f x,
      Subsingleton ((Scheme.Hom.relativeDifferentials f).presheaf.stalk x),
      HasDifferentialPresentationAt f x,
      ∃ U : X.Opens, x ∈ U ∧ IsOpenImmersion (U.ι ≫ pullback.diagonal f)] := by
  have h := stalkwiseUnramifiedAt_tfae f x
  tfae_have 1 ↔ 2 := h.out 1 2
  tfae_have 1 ↔ 3 := stalkwiseUnramifiedAt_iff_hasDifferentialPresentationAt f x
  tfae_have 1 ↔ 4 := h.out 1 3
  tfae_finish

end AlgebraicGeometry

end
