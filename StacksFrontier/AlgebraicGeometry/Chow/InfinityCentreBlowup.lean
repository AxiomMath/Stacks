module

public import StacksFrontier.AlgebraicGeometry.Blowup.CartierCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.IsoOffCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.InverseImageCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.RegularPullback
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafComapMap
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Difference
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ProjectiveLineBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.InfinityCartier
public import StacksFrontier.AlgebraicGeometry.PicSurjectiveFinite.Basic

/-!
# Blowing up at infinity

Let `X` be a scheme and `Z ⊆ X` the closed subscheme cut out by a quasi-coherent ideal sheaf
`ℐ`. The *centre at infinity* is the closed subscheme `∞(Z) ⊆ 𝐏¹_X`, the image of `Z` under the
infinity section `∞ : X ⟶ 𝐏¹_X`, and the *blowup at infinity* is the blowup

  `b : W ⟶ 𝐏¹_X`

of `𝐏¹_X` in `∞(Z)`. It carries the exceptional divisor `E ⊆ W` and the fibre at infinity
`W_∞ ⊆ W`, the inverse image of the divisor at infinity of `𝐏¹_X`. This file constructs `W`
together with the two closed immersions into it that the source attaches to it: the blowup `X'`
of `X` in `Z`, which sits over the infinity section, and the projective line `𝐏¹_Z` of the
centre.

## Main definitions

* `Stacks.Chow.infinityCentreIdeal` — the ideal of the centre `∞(Z) ⊆ 𝐏¹_X`.
* `Stacks.Chow.blowupAtInfinity` and `Stacks.Chow.blowupAtInfinityToLine` — the scheme `W` and
  its structure morphism `b : W ⟶ 𝐏¹_X`; `Stacks.Chow.blowupAtInfinityToBase` is `W ⟶ X`.
* `Stacks.Chow.exceptionalIdealAtInfinity` and `Stacks.Chow.fibreIdealAtInfinity` — the ideals
  of `E ⊆ W` and of `W_∞ ⊆ W`.
* `Stacks.Chow.blowUpToBlowupAtInfinity` — the closed immersion `X' ⟶ W`.
* `Stacks.Chow.lineToBlowupAtInfinity` — the closed immersion `𝐏¹_Z ⟶ W`.
* `Stacks.Chow.isomorphismLocusAtInfinity` — the open `𝐀¹_X ∪ 𝐏¹_{X ∖ Z}` of `𝐏¹_X`.

## Main results

* `AlgebraicGeometry.isClosedImmersion_blowUpLift` — if the inverse image of the centre along a
  closed immersion `f : T ⟶ S` is an effective Cartier divisor, then the classifying morphism
  `T ⟶ Bl_ℐ S` of `f` is a closed immersion.
* `Stacks.Chow.blowUpToBlowupAtInfinity_comp` and
  `Stacks.Chow.blowUpToBlowupAtInfinity_comp_toBase` — the commutative square of the
  construction: `X' ⟶ W ⟶ 𝐏¹_X` is `X' ⟶ X ⟶ 𝐏¹_X`.
* `Stacks.Chow.comap_exceptionalIdealAtInfinity` — assertion (3): the inverse image of `E` on
  `X'` is the exceptional divisor of `X' ⟶ X`.
* `Stacks.Chow.fibreIdealAtInfinity_le_exceptionalIdealAtInfinity`,
  `Stacks.Chow.isEffectiveCartierDivisor_fibreIdealAtInfinity` and
  `Stacks.Chow.exists_isEffectiveCartierDivisor_fibreIdealAtInfinity_eq` — `E ⊆ W_∞`, the fibre
  at infinity is an effective Cartier divisor on `W`, and `W_∞ = D + E` for a third effective
  Cartier divisor `D`.
* `Stacks.Chow.lineToBlowupAtInfinity_comp` — assertion (8), the triangle: the composite of
  `𝐏¹_Z ⟶ W` with `b` is the inclusion `𝐏¹_Z ⟶ 𝐏¹_X`.
* `Stacks.Chow.isIso_blowupAtInfinityToLine_restrict` — assertion (1): `b` is an isomorphism
  over `𝐀¹_X ∪ 𝐏¹_{X ∖ Z}`.

## Implementation notes

`𝐏¹_X` is `Stacks.Chow.relativeProjectiveLine X`, the base change of `𝐏¹_ℤ`, and `∞` is
`Stacks.Chow.lineInfinitySection X`, a closed immersion because it is a section of a separated
morphism. The centre is the pushforward `ℐ.map ∞`, which is the ideal sheaf of the closed
subscheme `∞(Z)`; that it restricts to `ℐ` along `∞` is
`AlgebraicGeometry.Scheme.IdealSheafData.comap_map_of_isClosedImmersion`, and this single
identity is what drives everything below.

Both closed immersions into `W` are produced by the universal property of the blowup
(`AlgebraicGeometry.blowUpLift`, Stacks 0806) rather than as strict transforms, so each has a
body and satisfies its triangle by `AlgebraicGeometry.blowUpLift_comp`. That they are closed
immersions is Stacks 080E: the classifying morphism of a closed immersion `f : T ⟶ S` along
which the centre pulls back to an effective Cartier divisor agrees, by uniqueness, with the
composite of the inverse of `Bl_{ℐ·𝒪_T} T ⟶ T` (an isomorphism by Stacks 0807) with the closed
immersion `Bl_{ℐ·𝒪_T} T ⟶ T ×_S Bl_ℐ S ⟶ Bl_ℐ S` of
`AlgebraicGeometry.strictTransformBlowUpι`. For `X' ⟶ W` the pullback of the centre is the
exceptional divisor of `X' ⟶ X`; for `𝐏¹_Z ⟶ W` it is the divisor at infinity of `𝐏¹_Z`.

### Where the remaining assertions are

Assertions (2) and (4) of the source — the divisor `D` with `W_∞ = D + E` is `X'` — are
`Stacks.Chow.isEffectiveCartierDivisor_strictTransformIdealAtInfinity` and
`Stacks.Chow.fibreIdealAtInfinity_eq_mul_strictTransformIdealAtInfinity` in
`StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreDivisor`, which also proves
`W_∞ ∖ X' = E ∖ X'`. The blowup at infinity as a modification `W ⟶ X ×_S 𝐏¹_S` in the sense of
Stacks 0F9J is `StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreModification`. Assertion (5),
`E = Proj_Z(𝒞_{Z/X,*}[S])`, is `Stacks.Chow.exceptionalDivisorIsoConormalPolynomialProj` in
`StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreExceptionalPolynomial`; assertion (6),
`X' ∩ E = Proj_Z(𝒞_{Z/X,*})`, is
`Stacks.Chow.strictTransformOnExceptionalIsoProjectivizedNormalCone` in
`StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreProjectivizedNormalCone`; assertion (7),
`E ∖ X' = E ∖ (X' ∩ E) = Spec_Z(𝒞_{Z/X,*}) = C_ZX`, is
`Stacks.Chow.normalConeToExceptionalDivisor_spec` in
`StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreNormalConeIso` (also Stacks 0FBH); and assertion
(8) in full, with the base change of `𝐏¹_Z ⟶ W` by `∞`, is `Stacks.Chow.lineToBlowupAtInfinity_spec`
in `StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreLineAtInfinity` (also Stacks 0FE9).

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
* [Stacks Project, Tag 0807](https://stacks.math.columbia.edu/tag/0807)
* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 080E as a property of the classifying morphism.** Let `ℐ` be a quasi-coherent ideal
sheaf on `S`, let `f : T ⟶ S` be a closed immersion and let `𝒥` be the inverse image of `ℐ` on
`T`. Then the morphism `Bl_𝒥 T ⟶ Bl_ℐ S` over `S` supplied by the universal property of the
blowup is a closed immersion.

The strict transform of `T` is `Bl_𝒥 T` and it is a closed subscheme of `T ×_S Bl_ℐ S`
(`AlgebraicGeometry.strictTransformBlowUpι`), whose projection to `Bl_ℐ S` is a closed immersion
because `f` is. Uniqueness of the morphism over `S` identifies the resulting composite with the
classifying morphism. -/
theorem isClosedImmersion_blowUpLift_comp {T S : Scheme.{u}} (f : T ⟶ S) [IsClosedImmersion f]
    (ℐ : S.IdealSheafData) (𝒥 : T.IdealSheafData) (hcomap : ℐ.comap f = 𝒥)
    (hf : Stacks.Blowup.IsCartierOver ℐ (Over.mk (blowUpToBase 𝒥 ≫ f))) :
    IsClosedImmersion (blowUpLift ℐ (blowUpToBase 𝒥 ≫ f) hf) := by
  subst hcomap
  have h1 : pullback.snd f (blowUpToBase ℐ) ≫ blowUpToBase ℐ =
      pullback.fst f (blowUpToBase ℐ) ≫ f := pullback.condition.symm
  have h2 : strictTransformBlowUpι f ℐ ≫ pullback.fst f (blowUpToBase ℐ) =
      pullback.fst (𝟙 T) (blowUpToBase (ℐ.comap f)) := strictTransformBlowUpι_fst f ℐ
  have h3 : pullback.fst (𝟙 T) (blowUpToBase (ℐ.comap f)) =
      pullback.snd (𝟙 T) (blowUpToBase (ℐ.comap f)) ≫ blowUpToBase (ℐ.comap f) := by
    rw [← pullback.condition, Category.comp_id]
  have hw : (inv (pullback.snd (𝟙 T) (blowUpToBase (ℐ.comap f))) ≫
      strictTransformBlowUpι f ℐ ≫ pullback.snd f (blowUpToBase ℐ)) ≫ blowUpToBase ℐ =
      blowUpToBase (ℐ.comap f) ≫ f := by
    simp only [Category.assoc, h1]
    rw [← Category.assoc (strictTransformBlowUpι f ℐ), h2, h3]
    simp
  rw [← blowUpLift_unique ℐ (blowUpToBase (ℐ.comap f) ≫ f) hf _ hw]
  infer_instance

/-- If the inverse image of `ℐ` along `f` is `𝒥`, an effective Cartier divisor, then `f` is
Cartier over `ℐ`. -/
private theorem isCartierOver_mk_of_comap_eq {T S : Scheme.{u}} (f : T ⟶ S)
    (ℐ : S.IdealSheafData) (𝒥 : T.IdealSheafData) (h : ℐ.comap f = 𝒥)
    (h𝒥 : Stacks.Divisors.IsEffectiveCartierDivisor 𝒥) :
    Stacks.Blowup.IsCartierOver ℐ (Over.mk f) := by
  subst h
  exact h𝒥

/-- **The classifying morphism of a closed immersion is a closed immersion.** Let `ℐ` be a
quasi-coherent ideal sheaf on `S` and let `f : T ⟶ S` be a closed immersion along which `ℐ`
pulls back to an effective Cartier divisor on `T`. Then the morphism `T ⟶ Bl_ℐ S` over `S`
supplied by the universal property of the blowup is a closed immersion.

The blowup of `T` in `ℐ·𝒪_T` is `T` itself by Stacks 0807, so this is
`AlgebraicGeometry.isClosedImmersion_blowUpLift_comp` composed with an isomorphism. -/
theorem isClosedImmersion_blowUpLift {T S : Scheme.{u}} (f : T ⟶ S) [IsClosedImmersion f]
    (ℐ : S.IdealSheafData) (hf : Stacks.Blowup.IsCartierOver ℐ (Over.mk f)) :
    IsClosedImmersion (blowUpLift ℐ f hf) := by
  have : IsIso (blowUpToBase (ℐ.comap f)) :=
    Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor _ hf
  have hf' : Stacks.Blowup.IsCartierOver ℐ (Over.mk (blowUpToBase (ℐ.comap f) ≫ f)) :=
    isCartierOver_mk_of_comap_eq _ _ _ (Scheme.IdealSheafData.comap_comp _ _ _)
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (ℐ.comap f))
  have : IsClosedImmersion (blowUpLift ℐ (blowUpToBase (ℐ.comap f) ≫ f) hf') :=
    isClosedImmersion_blowUpLift_comp f ℐ (ℐ.comap f) rfl hf'
  have hw : (inv (blowUpToBase (ℐ.comap f)) ≫
      blowUpLift ℐ (blowUpToBase (ℐ.comap f) ≫ f) hf') ≫ blowUpToBase ℐ = f := by
    rw [Category.assoc, blowUpLift_comp, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [← blowUpLift_unique ℐ f hf _ hw]
  infer_instance

end AlgebraicGeometry

namespace Stacks.Chow

variable {X : Scheme.{u}} (ℐ : X.IdealSheafData)

/-! ### The centre at infinity -/

/-- The centre `∞(Z) ⊆ 𝐏¹_X` of the blowup at infinity: the closed subscheme of `𝐏¹_X` obtained
by pushing the closed subscheme `Z ⊆ X` of `ℐ` forward along the infinity section
`∞ : X ⟶ 𝐏¹_X`. -/
def infinityCentreIdeal : (relativeProjectiveLine X).IdealSheafData :=
  ℐ.map (lineInfinitySection X)

/-- The centre `∞(Z)` restricts to `Z` along the infinity section: the inverse image of the
ideal of `∞(Z)` along `∞ : X ⟶ 𝐏¹_X` is `ℐ`. -/
@[simp]
theorem comap_infinityCentreIdeal_lineInfinitySection :
    (infinityCentreIdeal ℐ).comap (lineInfinitySection X) = ℐ :=
  Scheme.IdealSheafData.comap_map_of_isClosedImmersion ℐ (lineInfinitySection X)

/-- The centre `∞(Z)` is contained in the divisor at infinity `(𝐏¹_X)_∞`. -/
theorem lineInfinityDivisor_le_infinityCentreIdeal :
    lineInfinityDivisor X ≤ infinityCentreIdeal ℐ :=
  (Scheme.IdealSheafData.map_bot (lineInfinitySection X)).ge.trans
    (Scheme.IdealSheafData.map_mono (lineInfinitySection X) bot_le)

/-- The centre `∞(Z)` lies over `Z`: its support is contained in the inverse image of the
support of `ℐ` under `𝐏¹_X ⟶ X`. -/
theorem coe_support_infinityCentreIdeal_subset :
    ((infinityCentreIdeal ℐ).support : Set (relativeProjectiveLine X)) ⊆
      (relativeProjectiveLine X ↘ X) ⁻¹' (ℐ.support : Set X) := by
  have hcl : IsClosed ((relativeProjectiveLine X ↘ X) ⁻¹' (ℐ.support : Set X)) :=
    ℐ.support.isClosed.preimage (relativeProjectiveLine X ↘ X).continuous
  have himg : (lineInfinitySection X) '' (ℐ.support : Set X) ⊆
      (relativeProjectiveLine X ↘ X) ⁻¹' (ℐ.support : Set X) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, lineInfinitySection_comp]
    simpa using hz
  calc ((infinityCentreIdeal ℐ).support : Set (relativeProjectiveLine X))
      = closure ((lineInfinitySection X) '' (ℐ.support : Set X)) := by
        rw [infinityCentreIdeal, Scheme.IdealSheafData.support_map]
        rfl
    _ ⊆ _ := hcl.closure_subset_iff.mpr himg

/-! ### The blowup at infinity -/

/-- **The deformation space `W` of Stacks 0FBG**: the blowup of `𝐏¹_X` in the centre `∞(Z)`. -/
@[stacks 0FBG "the scheme W, the blowup of 𝐏¹_X in the centre ∞(Z)"]
def blowupAtInfinity : Scheme.{u} :=
  blowUp (infinityCentreIdeal ℐ)

/-- **The structure morphism `b : W ⟶ 𝐏¹_X`** of the blowup at infinity. -/
@[stacks 0FBG "the structure morphism b : W ⟶ 𝐏¹_X of the blowup at infinity"]
def blowupAtInfinityToLine : blowupAtInfinity ℐ ⟶ relativeProjectiveLine X :=
  blowUpToBase (infinityCentreIdeal ℐ)

/-- The morphism `W ⟶ X`, the composite of `b` with the structure morphism of `𝐏¹_X`. -/
def blowupAtInfinityToBase : blowupAtInfinity ℐ ⟶ X :=
  blowupAtInfinityToLine ℐ ≫ (relativeProjectiveLine X ↘ X)

/-- The ideal of the exceptional divisor `E ⊆ W`: the inverse image of the centre `∞(Z)`
along `b`. -/
@[stacks 0FBG "the exceptional divisor E ⊆ W of the blowup at infinity"]
def exceptionalIdealAtInfinity : (blowupAtInfinity ℐ).IdealSheafData :=
  exceptionalIdeal (infinityCentreIdeal ℐ)

/-- The ideal of the fibre at infinity `W_∞ ⊆ W`: the inverse image along `b` of the divisor at
infinity `(𝐏¹_X)_∞`. -/
@[stacks 0FBG "the fibre at infinity W_∞ ⊆ W, the inverse image of (𝐏¹_X)_∞ under b"]
def fibreIdealAtInfinity : (blowupAtInfinity ℐ).IdealSheafData :=
  (lineInfinityDivisor X).comap (blowupAtInfinityToLine ℐ)

/-- The exceptional divisor of the blowup at infinity is an effective Cartier divisor on `W`. -/
theorem isEffectiveCartierDivisor_exceptionalIdealAtInfinity :
    Stacks.Divisors.IsEffectiveCartierDivisor (exceptionalIdealAtInfinity ℐ) :=
  Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (infinityCentreIdeal ℐ)

/-- `E` is contained in `W_∞`: the centre `∞(Z)` contains the divisor at infinity, so its
inverse image along `b` does too. -/
@[stacks 0FBG "E ⊆ W_∞ as closed subschemes of W"]
theorem fibreIdealAtInfinity_le_exceptionalIdealAtInfinity :
    fibreIdealAtInfinity ℐ ≤ exceptionalIdealAtInfinity ℐ :=
  Scheme.IdealSheafData.comap_mono (blowupAtInfinityToLine ℐ)
    (lineInfinityDivisor_le_infinityCentreIdeal ℐ)

/-- The fibre at infinity `W_∞` is an effective Cartier divisor on `W`: the divisor at infinity
of `𝐏¹_X` is one, and the inverse image of an effective Cartier divisor under a blowup is again
one. -/
@[stacks 0FBG "W_∞ is an effective Cartier divisor on W"]
theorem isEffectiveCartierDivisor_fibreIdealAtInfinity :
    Stacks.Divisors.IsEffectiveCartierDivisor (fibreIdealAtInfinity ℐ) :=
  AlgebraicGeometry.isPullbackDefined_blowUpToBase (infinityCentreIdeal ℐ)
    (lineInfinityDivisor X) (lineInfinityDivisor_isEffectiveCartierDivisor X)

/-- **The fibre at infinity decomposes as `W_∞ = D + E`.** Both `E` and `W_∞` are effective
Cartier divisors on `W` and `E ⊆ W_∞`, so `W_∞` is the sum of `E` and a third effective Cartier
divisor `D`, written in the ideal-sheaf presentation `ℐ_{W_∞} = ℐ_E · ℐ_D`. That `D` is the
divisor `X'` is `Stacks.Chow.eq_strictTransformIdealAtInfinity_of_mul_eq`. -/
@[stacks 0FBG "W_∞ is the sum of E and a second effective Cartier divisor on W"]
theorem exists_isEffectiveCartierDivisor_fibreIdealAtInfinity_eq :
    ∃ D : (blowupAtInfinity ℐ).IdealSheafData,
      Stacks.Divisors.IsEffectiveCartierDivisor D ∧
        fibreIdealAtInfinity ℐ = exceptionalIdealAtInfinity ℐ * D :=
  AlgebraicGeometry.exists_isEffectiveCartierDivisor_mul_eq_of_le
    (exceptionalIdealAtInfinity ℐ) (fibreIdealAtInfinity ℐ)
    (isEffectiveCartierDivisor_exceptionalIdealAtInfinity ℐ)
    (isEffectiveCartierDivisor_fibreIdealAtInfinity ℐ)
    (fibreIdealAtInfinity_le_exceptionalIdealAtInfinity ℐ)

/-! ### The blowup of `X` in `Z` as a closed subscheme of `W` -/

/-- On the blowup `X'` of `X` in `Z`, the inverse image of the centre `∞(Z)` along
`X' ⟶ X ⟶ 𝐏¹_X` is the exceptional divisor of `X' ⟶ X`, hence an effective Cartier divisor. -/
theorem isCartierOver_infinityCentreIdeal_blowUpToBase :
    Stacks.Blowup.IsCartierOver (infinityCentreIdeal ℐ)
      (Over.mk (blowUpToBase ℐ ≫ lineInfinitySection X)) :=
  isCartierOver_mk_of_comap_eq _ _ _
    (by rw [Scheme.IdealSheafData.comap_comp, comap_infinityCentreIdeal_lineInfinitySection])
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal ℐ)

/-- **The closed immersion `X' ⟶ W`** of the commutative square of Stacks 0FBG: the blowup `X'`
of `X` in `Z` is the classifying morphism of `X' ⟶ X ⟶ 𝐏¹_X` for the centre `∞(Z)`. -/
@[stacks 0FBG "the closed immersion X' ⟶ W of the square, X' the blowup of X in Z"]
def blowUpToBlowupAtInfinity : blowUp ℐ ⟶ blowupAtInfinity ℐ :=
  blowUpLift (infinityCentreIdeal ℐ) (blowUpToBase ℐ ≫ lineInfinitySection X)
    (isCartierOver_infinityCentreIdeal_blowUpToBase ℐ)

/-- The morphism `X' ⟶ W` from the blowup of `X` in `Z` to the blowup at infinity is a closed
immersion. -/
instance isClosedImmersion_blowUpToBlowupAtInfinity :
    IsClosedImmersion (blowUpToBlowupAtInfinity ℐ) :=
  isClosedImmersion_blowUpLift_comp (lineInfinitySection X) (infinityCentreIdeal ℐ) ℐ
    (comap_infinityCentreIdeal_lineInfinitySection ℐ)
    (isCartierOver_infinityCentreIdeal_blowUpToBase ℐ)

/-- The square of Stacks 0FBG commutes: `X' ⟶ W ⟶ 𝐏¹_X` equals `X' ⟶ X ⟶ 𝐏¹_X`. -/
@[stacks 0FBG "commutativity of the square X' ⟶ W ⟶ 𝐏¹_X = X' ⟶ X ⟶ 𝐏¹_X"]
theorem blowUpToBlowupAtInfinity_comp :
    blowUpToBlowupAtInfinity ℐ ≫ blowupAtInfinityToLine ℐ =
      blowUpToBase ℐ ≫ lineInfinitySection X :=
  blowUpLift_comp (infinityCentreIdeal ℐ) (blowUpToBase ℐ ≫ lineInfinitySection X)
    (isCartierOver_infinityCentreIdeal_blowUpToBase ℐ)

/-- `X' ⟶ W` is a morphism over `X`. -/
theorem blowUpToBlowupAtInfinity_comp_toBase :
    blowUpToBlowupAtInfinity ℐ ≫ blowupAtInfinityToBase ℐ = blowUpToBase ℐ := by
  rw [blowupAtInfinityToBase, ← Category.assoc, blowUpToBlowupAtInfinity_comp, Category.assoc,
    lineInfinitySection_comp, Category.comp_id]

/-- **Stacks 0FBG, assertion (3).** The inverse image of the exceptional divisor `E ⊆ W` on
`X'` is the exceptional divisor of the blowup `X' ⟶ X` of `X` in `Z`; that is, `X' ∩ E` is the
exceptional divisor of `X' ⟶ X`. -/
@[stacks 0FBG "(3): X' ∩ E is the exceptional divisor of X' ⟶ X"]
theorem comap_exceptionalIdealAtInfinity :
    (exceptionalIdealAtInfinity ℐ).comap (blowUpToBlowupAtInfinity ℐ) = exceptionalIdeal ℐ := by
  change ((infinityCentreIdeal ℐ).comap (blowupAtInfinityToLine ℐ)).comap
    (blowUpToBlowupAtInfinity ℐ) = _
  rw [← Scheme.IdealSheafData.comap_comp, blowUpToBlowupAtInfinity_comp,
    Scheme.IdealSheafData.comap_comp, comap_infinityCentreIdeal_lineInfinitySection]

/-! ### The projective line of the centre as a closed subscheme of `W` -/

/-- `𝐏¹_Z ⟶ 𝐏¹_X` is a closed immersion when `Z ⟶ X` is: it is the base change of `Z ⟶ X`
along the structure morphism of `𝐏¹_X`. -/
instance isClosedImmersion_projectiveLineBaseChange {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    [IsClosedImmersion g] : IsClosedImmersion (projectiveLineBaseChange g) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_projectiveLineBaseChange g) ‹_›

/-- The intersection of the centre `∞(Z)` with `𝐏¹_Z` is the divisor at infinity of `𝐏¹_Z`:
pulling the ideal of `∞(Z)` back along `𝐏¹_Z ⟶ 𝐏¹_X` gives `(𝐏¹_Z)_∞`. -/
theorem comap_infinityCentreIdeal_projectiveLineBaseChange :
    (infinityCentreIdeal ℐ).comap (projectiveLineBaseChange ℐ.subschemeι) =
      lineInfinityDivisor ℐ.subscheme := by
  have hsec : lineInfinitySection ℐ.subscheme ≫ projectiveLineBaseChange ℐ.subschemeι =
      ℐ.subschemeι ≫ lineInfinitySection X :=
    absoluteConstantSection_comp_projectiveLineBaseChange integralInfinitySection ℐ.subschemeι
  have hker : infinityCentreIdeal ℐ =
      (lineInfinityDivisor ℐ.subscheme).map (projectiveLineBaseChange ℐ.subschemeι) := by
    change (ℐ.subschemeι ≫ lineInfinitySection X).ker = _
    rw [← hsec, Scheme.Hom.ker_comp]
    rfl
  rw [hker,
    Scheme.IdealSheafData.comap_map_of_isClosedImmersion (lineInfinityDivisor ℐ.subscheme)
      (projectiveLineBaseChange ℐ.subschemeι)]

/-- The inverse image of the centre `∞(Z)` on `𝐏¹_Z` is an effective Cartier divisor: it is the
divisor at infinity of `𝐏¹_Z`. -/
theorem isCartierOver_infinityCentreIdeal_projectiveLineBaseChange :
    Stacks.Blowup.IsCartierOver (infinityCentreIdeal ℐ)
      (Over.mk (projectiveLineBaseChange ℐ.subschemeι)) :=
  isCartierOver_mk_of_comap_eq _ _ _ (comap_infinityCentreIdeal_projectiveLineBaseChange ℐ)
    (lineInfinityDivisor_isEffectiveCartierDivisor ℐ.subscheme)

/-- **Stacks 0FBG, assertion (8), the morphism.** The closed immersion `𝐏¹_Z ⟶ W`: the
classifying morphism for the centre `∞(Z)` of the inclusion `𝐏¹_Z ⟶ 𝐏¹_X`, along which `∞(Z)`
pulls back to the divisor at infinity of `𝐏¹_Z`. -/
@[stacks 0FBG "(8): the closed immersion 𝐏¹_Z ⟶ W"]
def lineToBlowupAtInfinity :
    relativeProjectiveLine ℐ.subscheme ⟶ blowupAtInfinity ℐ :=
  blowUpLift (infinityCentreIdeal ℐ) (projectiveLineBaseChange ℐ.subschemeι)
    (isCartierOver_infinityCentreIdeal_projectiveLineBaseChange ℐ)

/-- The morphism `𝐏¹_Z ⟶ W` to the blowup at infinity is a closed immersion. -/
instance isClosedImmersion_lineToBlowupAtInfinity :
    IsClosedImmersion (lineToBlowupAtInfinity ℐ) :=
  isClosedImmersion_blowUpLift _ _ _

/-- **Stacks 0FBG, assertion (8), the triangle.** The composite of `𝐏¹_Z ⟶ W` with `b` is the
inclusion morphism `𝐏¹_Z ⟶ 𝐏¹_X`. -/
@[stacks 0FBG "(8): the composite of 𝐏¹_Z ⟶ W with b is the inclusion 𝐏¹_Z ⟶ 𝐏¹_X"]
theorem lineToBlowupAtInfinity_comp :
    lineToBlowupAtInfinity ℐ ≫ blowupAtInfinityToLine ℐ =
      projectiveLineBaseChange ℐ.subschemeι :=
  blowUpLift_comp (infinityCentreIdeal ℐ) (projectiveLineBaseChange ℐ.subschemeι)
    (isCartierOver_infinityCentreIdeal_projectiveLineBaseChange ℐ)

/-! ### `b` is an isomorphism over `𝐀¹_X ∪ 𝐏¹_{X ∖ Z}` -/

/-- The open `𝐀¹_X ∪ 𝐏¹_{X ∖ Z}` of `𝐏¹_X`: the union of the affine chart with the inverse
image of the complement of `Z`. -/
def isomorphismLocusAtInfinity : (relativeProjectiveLine X).Opens :=
  (affineChart X).opensRange ⊔ (relativeProjectiveLine X ↘ X) ⁻¹ᵁ ℐ.support.compl

/-- `𝐀¹_X ∪ 𝐏¹_{X ∖ Z}` misses the centre `∞(Z)`: the affine chart is disjoint from the whole
divisor at infinity, and a point of `𝐏¹_X` lying over `X ∖ Z` cannot lie in `∞(Z)`. -/
theorem isomorphismLocusAtInfinity_le_compl_support :
    isomorphismLocusAtInfinity ℐ ≤ (infinityCentreIdeal ℐ).support.compl := by
  refine sup_le (fun p hp => ?_) (fun p hp => ?_)
  · obtain ⟨x, rfl⟩ := hp
    have hcomap : (infinityCentreIdeal ℐ).comap (affineChart X) = ⊤ :=
      top_le_iff.mp ((comap_lineInfinityDivisor_affineChart X).ge.trans
        (Scheme.IdealSheafData.comap_mono (affineChart X)
          (lineInfinityDivisor_le_infinityCentreIdeal ℐ)))
    have hsupp := Scheme.IdealSheafData.support_comap (infinityCentreIdeal ℐ) (affineChart X)
    rw [hcomap] at hsupp
    intro hmem
    have : x ∈ ((⊤ : (affineLineOver X).IdealSheafData).support :
        Set (affineLineOver X)) := by
      rw [hsupp]
      exact hmem
    simp at this
  · intro hmem
    exact hp (coe_support_infinityCentreIdeal_subset ℐ hmem)

/-- **Stacks 0FBG, assertion (1).** The blowup at infinity is an isomorphism over
`𝐀¹_X ∪ 𝐏¹_{X ∖ Z}`: that open misses the centre, and a blowup is an isomorphism over the
complement of its centre. -/
@[stacks 0FBG "(1): b is an isomorphism over 𝐀¹_X ∪ 𝐏¹_{X ∖ Z}"]
theorem isIso_blowupAtInfinityToLine_restrict :
    IsIso (blowupAtInfinityToLine ℐ ∣_ isomorphismLocusAtInfinity ℐ) := by
  have : IsIso (blowupAtInfinityToLine ℐ ∣_ (infinityCentreIdeal ℐ).support.compl) :=
    AlgebraicGeometry.isIso_blowUpToBase_restrict_compl_support (infinityCentreIdeal ℐ)
  exact Stacks.PicFinite.isIso_morphismRestrict_of_le _
    (isomorphismLocusAtInfinity_le_compl_support ℐ)

end Stacks.Chow

end
