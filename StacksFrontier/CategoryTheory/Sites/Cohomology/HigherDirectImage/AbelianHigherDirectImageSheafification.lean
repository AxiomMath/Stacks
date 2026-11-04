module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The higher direct image of an abelian sheaf is the sheafified cohomology presheaf

Let `u : 𝒟 ⥤ 𝒞` be a continuous functor between sites, so that it induces the direct image
`f_* = u^s : Sh(𝒞, 𝒜) ⥤ Sh(𝒟, 𝒜)` on sheaves with values in an abelian category `𝒜`. This file
proves, for every `p : ℕ`, the natural isomorphism

`R^p f_* ≅ a (V ↦ H^p(u(V), -))`

of functors `Sh(𝒞, 𝒜) ⥤ Sh(𝒟, 𝒜)`, where `a` is sheafification of `𝒜`-valued presheaves on `𝒟`.
This is [Stacks, Tag 072W] for sheaves of abelian groups rather than for sheaves of modules over
a ringed site, and as a genuine natural isomorphism rather than an unnamed one.

The cohomology presheaf is realised here as the right derived functor of the composite
`Sh(𝒞, 𝒜) ⥤ PSh(𝒟, 𝒜)` that sends a sheaf `F` to the presheaf `V ↦ F(u(V))`
(`pushforwardCohomologyPresheaf`); `pushforwardCohomologyPresheaf_comp_evaluation` identifies that
composite, evaluated at `V`, with the sections functor `Γ(u(V), -)`, and
`pushforwardCohomologyPresheafEvaluationIso` upgrades that to the identification of the value of
the derived presheaf at `V` with `H^p(u(V), -)`.

## Main results

All in the namespace `Stacks.Cohomology.SheafifiedHigherDirectImage`.

* `rightDerivedPushforwardIso`: the isomorphism above, `R^p f_* ≅ (R^p of the cohomology
  presheaf) ⋙ a`.
* `pushforwardCohomologyPresheafEvaluationIso`: the value of the cohomology presheaf at `V` is
  `H^p(u(V), -)`.
* `isZero_sheafify_rightDerived_sheafToPresheaf`: **the higher cohomology presheaf of a site has
  vanishing sheafification** ([Stacks, Tag 01FW]), the case `u = 𝟭` of the above.
* `isZero_rightDerived_pushforward_of_cohomologyPresheafIso`: consequently `R^p f_* F = 0` for
  `p > 0` as soon as the `p`-th cohomology presheaf of `F` for `u` is isomorphic to the `p`-th
  cohomology presheaf of some sheaf on the target site.

## Implementation notes

**What `a` contributes, and why the forgetful functor cannot be used instead.** The isomorphism is
obtained by writing `f_*` as `(f_* ⋙ forget) ⋙ a` — using that `forget` is fully faithful, so the
counit of `a ⊣ forget` is invertible — and then pulling the *exact* functor `a` out of the right
derived functor with `CategoryTheory.Functor.rightDerivedCompIso`. Running the argument with
`forget` in place of `a` would need `forget` to preserve homology, which is false: `forget` is a
right adjoint and does not preserve finite colimits. Sheafification is a left adjoint and left
exact, so it preserves both finite limits and finite colimits; this is
`preservesHomology_presheafToSheaf`, whose colimit half comes from
`Adjunction.leftAdjoint_preservesColimits` rather than from any ambient instance.

**Relation to what the repository already has.**
`StacksFrontier/CategoryTheory/Sites/Cohomology/HigherDirectImage/SheafifiedCohomologyPresheaf.lean`
carries the `@[stacks 072W]` statement for `SheafOfModules` over a ringed site.
`StacksFrontier/CategoryTheory/Sites/Cohomology/HigherDirectImage/FilteredColimits.lean` assembles
the same composite as here for abelian sheaves, but inside the proof of
`isIso_colimit_post_rightDerived_sheafPushforwardContinuous` and only for
*small* sites with coefficients in `Ab`; neither form applies to a site whose underlying category
is not small, such as a slice of the locally quasi-compact Zariski site, which is what the
statements here are for.

**`Nat`-indexed derived functors.** Everything is stated for Mathlib's `Functor.rightDerived`;
`Stacks.DerivedIndexing.isZero_rightDerived_obj_iff` transports the vanishing statements to the
`ℤ`-indexed `Functor.rightDerivedPlus`.

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.SheafifiedHigherDirectImage

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology D} {K : GrothendieckTopology C}
  (A : Type*) [Category* A] [Abelian A] [HasSheafify J A] [HasSheafify K A]
  (u : D ⥤ C) [u.IsContinuous J K]

section Pushforward

/-- **The cohomology presheaf of the direct image, before sheafification.** It sends a sheaf `F`
on `𝒞` to the presheaf `V ↦ F(u(V))` on `𝒟`; its `p`-th right derived functor is the presheaf
`V ↦ H^p(u(V), F)` of [Stacks, Tag 072W]. -/
def pushforwardCohomologyPresheaf : Sheaf K A ⥤ (Dᵒᵖ ⥤ A) :=
  sheafToPresheaf K A ⋙ (Functor.whiskeringLeft _ _ A).obj u.op

/-- The cohomology presheaf functor `F ↦ (V ↦ F(u(V)))` is additive. -/
instance additive_pushforwardCohomologyPresheaf :
    (pushforwardCohomologyPresheaf (K := K) A u).Additive where
  map_add := rfl

omit [Abelian A] [HasSheafify K A] in
/-- The cohomology presheaf, evaluated at an object `V` of `𝒟`, is the sections functor over
`u(V)`: this is the pointwise formula `(f_* F)(V) = F(u(V))` for a continuous `u`. -/
theorem pushforwardCohomologyPresheaf_comp_evaluation (V : D) :
    pushforwardCohomologyPresheaf (K := K) A u ⋙ (evaluation Dᵒᵖ A).obj (op V) =
      (sheafSections K A).obj (op (u.obj V)) :=
  rfl

/-- **Sheafification of `𝒜`-valued presheaves preserves homology.** It preserves finite limits
because it is left exact, and all colimits because it is a left adjoint. -/
theorem preservesHomology_presheafToSheaf : (presheafToSheaf J A).PreservesHomology := by
  have hzero : (presheafToSheaf J A).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  have hcolim : PreservesFiniteColimits (presheafToSheaf J A) := by
    have hbig := (sheafificationAdjunction J A).leftAdjoint_preservesColimits
    exact ⟨fun _ _ _ => hbig.preservesColimitsOfShape⟩
  exact Functor.preservesHomologyOfExact _

attribute [local instance] preservesHomology_presheafToSheaf

/-- Sheafifying the cohomology presheaf returns the direct image: the underlying presheaf of
`f_* F` is already a sheaf, so the counit of `a ⊣ forget` is invertible there. -/
@[sga "4 VIII 5.1" "q = 0"]
def pushforwardCohomologyPresheafCompSheafification :
    pushforwardCohomologyPresheaf (K := K) A u ⋙ presheafToSheaf J A ≅
      u.sheafPushforwardContinuous A J K :=
  Functor.isoWhiskerLeft (u.sheafPushforwardContinuous A J K)
      (asIso (sheafificationAdjunction J A).counit) ≪≫
    (u.sheafPushforwardContinuous A J K).rightUnitor

variable [EnoughInjectives (Sheaf K A)]

/-- **[Stacks, Tag 072W] for sheaves of abelian groups.** The `p`-th higher direct image along a
continuous functor is the sheafification of the cohomology presheaf `V ↦ H^p(u(V), -)`, naturally
in the sheaf. -/
@[ega "0 12.2.1" "more general",
  sga "4 V 5.1" "Clause 1), special case",
  sga "4 VIII 5.1" "more general"]
def rightDerivedPushforwardIso (p : ℕ) :
    (u.sheafPushforwardContinuous A J K).rightDerived p ≅
      (pushforwardCohomologyPresheaf (K := K) A u).rightDerived p ⋙ presheafToSheaf J A :=
  (Functor.rightDerivedIsoOfNatIso
      (pushforwardCohomologyPresheafCompSheafification A u) p).symm ≪≫
    Functor.rightDerivedCompIso (pushforwardCohomologyPresheaf (K := K) A u)
      (presheafToSheaf J A) p

/-- **The cohomology presheaf computes cohomology over `u(V)`.** The value at `V` of the `p`-th
right derived functor of `pushforwardCohomologyPresheaf` is `H^p(u(V), -)`, because evaluation of
presheaves at `V` is exact.

The source is spelled as the right derived functor of the composite rather than of
`(sheafSections K A).obj (op (u.obj V))`; by `pushforwardCohomologyPresheaf_comp_evaluation`
those two functors are equal, and the composite spelling is the one whose additivity is
available from the additivity of its two factors. -/
def pushforwardCohomologyPresheafEvaluationIso (p : ℕ) (V : D) :
    (pushforwardCohomologyPresheaf (K := K) A u ⋙ (evaluation Dᵒᵖ A).obj (op V)).rightDerived p ≅
      (pushforwardCohomologyPresheaf (K := K) A u).rightDerived p ⋙
        (evaluation Dᵒᵖ A).obj (op V) :=
  letI : ((evaluation Dᵒᵖ A).obj (op V)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  Functor.rightDerivedCompIso (pushforwardCohomologyPresheaf (K := K) A u)
    ((evaluation Dᵒᵖ A).obj (op V)) p

end Pushforward

section Vanishing

variable [EnoughInjectives (Sheaf J A)]

/-- The higher right derived functors of the identity vanish: an injective resolution is a
resolution, so the complex computing them is exact in positive degrees. -/
theorem isZero_rightDerived_identity_obj (p : ℕ) (hp : 0 < p) (F : Sheaf J A) :
    IsZero (((𝟭 (Sheaf J A)).rightDerived p).obj F) := by
  let I := injectiveResolution F
  refine IsZero.of_iso ?_ (I.isoRightDerivedObj (𝟭 (Sheaf J A)) p)
  have := I.quasiIso
  exact (HomologicalComplex.isZero_single_obj_homology (j := 0) (c := ComplexShape.up ℕ)
    F p (by omega)).of_iso (asIso (HomologicalComplex.homologyMap I.ι p)).symm

/-- **[Stacks, Tag 01FW]: the higher cohomology presheaf of a site sheafifies to zero.** For
`p > 0` the sheafification of the presheaf `U ↦ H^p(U, F)` is the zero sheaf. This is
`rightDerivedPushforwardIso` for the identity functor, whose direct image is the identity and
whose higher derived functors therefore vanish. -/
@[sga "4 V 3.1" "special case"]
theorem isZero_sheafify_rightDerived_sheafToPresheaf (p : ℕ) (hp : 0 < p) (F : Sheaf J A) :
    IsZero ((presheafToSheaf J A).obj (((sheafToPresheaf J A).rightDerived p).obj F)) :=
  (isZero_rightDerived_identity_obj (A := A) p hp F).of_iso
    ((rightDerivedPushforwardIso A (𝟭 D) p).app F).symm

variable [EnoughInjectives (Sheaf K A)]

/-- **`R^p f_* F` vanishes as soon as its cohomology presheaf comes from the target site.** If the
`p`-th cohomology presheaf of `F` for `u` is isomorphic to the `p`-th cohomology presheaf of a
sheaf `G` on the target site, then `R^p f_* F = 0` for `p > 0`, both sheafifications being zero by
[Stacks, Tag 01FW].

This is the shape in which the vanishing of a higher direct image is actually obtained: the Stacks
argument identifies the presheaf `V ↦ H^p(u(V), F)` with a presheaf `V ↦ H^p(V, G)` on the target
site, and this lemma turns that identification into the vanishing. -/
theorem isZero_rightDerived_pushforward_of_cohomologyPresheafIso (p : ℕ) (hp : 0 < p)
    (F : Sheaf K A) (G : Sheaf J A)
    (e : ((pushforwardCohomologyPresheaf (K := K) A u).rightDerived p).obj F ≅
      ((sheafToPresheaf J A).rightDerived p).obj G) :
    IsZero (((u.sheafPushforwardContinuous A J K).rightDerived p).obj F) :=
  (isZero_sheafify_rightDerived_sheafToPresheaf (A := A) p hp G).of_iso
    ((rightDerivedPushforwardIso A u p).app F ≪≫ (presheafToSheaf J A).mapIso e)

end Vanishing

end Stacks.Cohomology.SheafifiedHigherDirectImage

end
