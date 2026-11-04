module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectSumSeparated
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyGradedReesBaseChange
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.GradedBaseChange
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.GradedRingAction
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.CanonicalMorphism
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.AffineAlgebraHom
public import StacksFrontier.AlgebraicGeometry.RelativeSpecClosedImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeSpecOpenRestriction.RelativeSpecBaseChange

/-!
# The structure morphism `f' : X' ⟶ Spec B` of [Stacks, Tag 0897], and its properness

[Stacks, Tag 0897] base changes a proper `f : X ⟶ Spec A` along `Spec B ⟶ Spec A` and works on
`X' = Spec(B) ×_{Spec A} X`, whose structure morphism `f' : X' ⟶ Spec B` is proper because
properness is stable under base change. In the formalisation `X'` is built instead as the
relative spectrum `Spec_X(𝓑)` of the sheaf of graded algebras
(`Stacks.AlgebraicGeometry.GradedProperCohomology.GradedQcohAlgebra.relSpec`), so the comparison
with the honest base change has to be produced. **This file produces it, and with it the proper
`f'`**, out of one datum: the global homogeneous sections of `𝓑` named by the homogeneous
elements of `B`.

## The shape of the argument

Write `g : Spec B ⟶ Spec A` for the structure morphism of the `A`-algebra `B` and
`𝔅 = g_* 𝒪_{Spec B}` for its pushed-forward structure sheaf, a quasi-coherent sheaf of
commutative `𝒪_{Spec A}`-algebras. Then

* `Spec_{Spec A}(𝔅) ≅ Spec B` over `Spec A` is [Stacks, Tag 01S8]
  (`Stacks.AffineAlgebraEquivalence.overRelativeSpecIso`), so the honest base change
  `Spec(B) ×_{Spec A} X` is the relative spectrum over `X` of the algebra pullback `f^* 𝔅` by
  [Stacks, Tag 01LX] part (2) — that is `baseChangeRelativeSpecIso`;
* a morphism of algebra sheaves `ψ : f^* 𝔅 ⟶ 𝓐` therefore induces
  `X' = Spec_X(𝓐) ⟶ Spec(B) ×_{Spec A} X`, a closed immersion as soon as `ψ` is locally
  surjective ([Stacks, Tag 01S8] via
  `Stacks.RelativeSpecClosedImmersion.isClosedImmersion_relativeSpecMapOfAlgebraHom`) — that is
  `relSpecToPullback` and `isClosedImmersion_relSpecToPullback`;
* and then `f' = (that closed immersion) ≫ pr₁` is proper, by
  `Stacks.Cohomology.FormalFunctions.isProper_comp_pullbackFst_of_isClosedImmersion`.

`ψ` itself is the adjoint transpose, across
`Stacks.AffineAlgebraEquivalence.algebraPullbackPushforwardAdjunction`, of a morphism of algebra
sheaves `β : 𝔅 ⟶ f_* 𝓐` on the *affine* base `Spec A`. There a morphism out of a quasi-coherent
algebra sheaf is exactly a ring map on global sections compatible with the two structure maps
(`Stacks.RelativeSpec.AlgebraSheaf.algebraHom`), and the ring map is
`HomogeneousSections.secRingHom`: a homogeneous `b ∈ 𝒜ₖ` goes to the degree-`k` inclusion of the
global section it names.

## Main definitions

* `HomogeneousSections.secRingHom`: **the ring map `B →+* Γ(𝓐, W)`** attached to the
  homogeneous-sections datum, over an arbitrary open `W` of `X`.
* `HomogeneousSections.baseAlgebraHom`: **`β : 𝔅 ⟶ f_* 𝓐`.**
* `HomogeneousSections.basePullbackHom`: **`ψ : f^* 𝔅 ⟶ 𝓐`**, its adjoint transpose.
* `GradedQcohAlgebra.relSpecToPullback`: the induced morphism
  `X' ⟶ Spec(B) ×_{Spec A} X`.
* `HomogeneousSections.structureHom`: **`f' : X' ⟶ Spec B`.**

## Main results

* `HomogeneousSections.secRingHom_coe`: the ring map on a homogeneous element. This is the only
  description of it, and every computation with `β`, `ψ` and `f'` goes through it.
* `HomogeneousSections.basePullbackHom_app_unit`: **the handle on `ψ`** — on the unit image of a
  global section of `𝔅` it is `β` on that section. This is the entry point for its local
  surjectivity.
* `HomogeneousSections.isProper_structureHom`: **`f' : X' ⟶ Spec B` is proper**, granted the
  local surjectivity of `ψ`.

## Implementation notes

The compatibility of `β` with the two structure maps is *not* a consequence of the
`HomogeneousSections` laws: that datum says nothing about the `A`-algebra structure of `B`, and
`β` is a morphism of `𝒪_{Spec A}`-algebras. It appears here as the hypothesis `hunit` of
`HomogeneousSections.IsStructureCompatible`, and is discharged for `𝓑 = f^* B̃` in
`StacksFrontier.AlgebraicGeometry.GradedProperCohomology.PullbackBaseAlgebra`.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
* [Stacks Project, Tag 01W4](https://stacks.math.columbia.edu/tag/01W4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open scoped DirectSum AlgebraicGeometry

universe v₁ u₁ u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

/-- Transport of a homogeneous local section along an equality of degrees does not change its
image in the ungraded realization: the transport is the identity once the equality is
substituted. -/
theorem ungradedIncl_castHom {X : Scheme.{u}}
    (𝓑 : _root_.SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf) {i j : ℤ} (h : i = j)
    (U : (Opens ↥X)ᵒᵖ) (x : (𝓑.piece i).val.obj U) :
    𝓑.ungradedIncl j (_root_.SheafOfModules.castHom 𝓑.piece h U x) = 𝓑.ungradedIncl i x := by
  subst h; rfl

/-- **A ring map between the sections of two algebra sheaves, as a morphism of commutative
rings.** It is stated for an arbitrary algebra sheaf, whose carrier does not reduce, because for a
concrete one instance search does not find the commutative ring structure on the sections. -/
def sectionsCommRingHom {Y : Scheme.{u}} (P Q : AlgebraSheaf.{u} Y) (U V : Y.Opens)
    (φ : ↥(AlgebraSheaf.sections P U) →+* ↥(AlgebraSheaf.sections Q V)) :
    AlgebraSheaf.sections P U ⟶ AlgebraSheaf.sections Q V :=
  CommRingCat.ofHom φ

/-- **The structure morphism `Spec B ⟶ Spec A` of an `A`-algebra `B`**, along which
[Stacks, Tag 0897]'s proof base changes `f : X ⟶ Spec A`. -/
abbrev algebraSpecToBase (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] :
    Spec (.of B) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

namespace HomogeneousSections

variable {X : Scheme.{u}} {𝓑 : _root_.SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
  {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {𝒜 : ℕ → Submodule A B} [_root_.GradedAlgebra 𝒜]

/-! ### The ring map `B →+* Γ(𝓐, W)` -/

variable (D : GradedQcohAlgebra X) (S : HomogeneousSections D.alg 𝒜)

/-- **The degree-`k` inclusion, into the sections of the algebra sheaf `𝓐`, of the global
section of `𝓑ₖ` named by a homogeneous element of degree `k`.** -/
def secIncl {k : ℕ} (b : ↥(𝒜 k)) (W : (Opens ↥X)ᵒᵖ) :
    ↥(AlgebraSheaf.sections D.sheaf W.unop) :=
  D.alg.ungradedIncl (k : ℤ) ((S.sec b).eval W)

/-- `secIncl` is additive in the homogeneous element. -/
theorem secIncl_add {k : ℕ} (b b' : ↥(𝒜 k)) (W : (Opens ↥X)ᵒᵖ) :
    secIncl D S (b + b') W = secIncl D S b W + secIncl D S b' W := by
  show D.alg.ungradedIncl (k : ℤ) ((S.sec (b + b')).eval W) = _
  rw [S.eval_add b b' W]
  exact D.alg.ungradedIncl_add (k : ℤ) W _ _

/-- `secIncl` sends the unit of the graded algebra `𝒜` to `1`. -/
theorem secIncl_one (W : (Opens ↥X)ᵒᵖ) :
    secIncl D S (GradedMonoid.GOne.one (A := fun n : ℕ => ↥(𝒜 n))) W = 1 := by
  show D.alg.ungradedIncl 0
      ((S.sec (GradedMonoid.GOne.one (A := fun n : ℕ => ↥(𝒜 n)))).eval W) = 1
  rw [S.eval_one W]
  exact D.alg.ungradedIncl_one W

/-- `secIncl` sends the graded product of homogeneous elements to the product of their images. -/
theorem secIncl_mul {k l : ℕ} (b : ↥(𝒜 k)) (b' : ↥(𝒜 l)) (W : (Opens ↥X)ᵒᵖ) :
    secIncl D S (GradedMonoid.GMul.mul (A := fun n : ℕ => ↥(𝒜 n)) b b') W =
      secIncl D S b W * secIncl D S b' W := by
  have key : D.alg.ungradedIncl ((k + l : ℕ) : ℤ)
        ((S.sec (GradedMonoid.GMul.mul (A := fun n : ℕ => ↥(𝒜 n)) b b')).eval W) =
      D.alg.ungradedIncl (l : ℤ) ((S.sec b').eval W) *
        D.alg.ungradedIncl (k : ℤ) ((S.sec b).eval W) := by
    rw [← S.castHom_mul b b' W,
      ungradedIncl_castHom D.alg
        (by push_cast; ring : (l : ℤ) + (k : ℤ) = ((k + l : ℕ) : ℤ)) W _]
    exact (D.alg.ungradedIncl_mul (l : ℤ) (k : ℤ) ((S.sec b').eval W) ((S.sec b).eval W)).symm
  refine Eq.trans (show _ = secIncl D S b' W * secIncl D S b W from key) ?_
  exact mul_comm (secIncl D S b' W) (secIncl D S b W)

/-- The degree-`k` part of the ring map, as an additive map. -/
def secInclAddHom (k : ℕ) (W : (Opens ↥X)ᵒᵖ) :
    ↥(𝒜 k) →+ ↥(AlgebraSheaf.sections D.sheaf W.unop) :=
  AddMonoidHom.mk' (fun b => secIncl D S b W) fun b b' => secIncl_add D S b b' W

/-- The ring map out of the homogeneous decomposition of `B`. -/
def secRingHomDirectSum (W : (Opens ↥X)ᵒᵖ) :
    (⨁ k : ℕ, ↥(𝒜 k)) →+* ↥(AlgebraSheaf.sections D.sheaf W.unop) where
  toFun := DirectSum.toAddMonoid (fun k => secInclAddHom D S k W)
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    rw [DirectSum.one_def,
      DirectSum.toAddMonoid_of (fun k => secInclAddHom D S k W) 0
        (GradedMonoid.GOne.one (A := fun n : ℕ => ↥(𝒜 n)))]
    exact secIncl_one D S W
  map_mul' z z' := by
    induction z using DirectSum.induction_on with
    | zero => rw [zero_mul, map_zero, zero_mul]
    | of k b =>
        induction z' using DirectSum.induction_on with
        | zero => rw [mul_zero, map_zero, mul_zero]
        | of l b' =>
            rw [DirectSum.of_mul_of,
              DirectSum.toAddMonoid_of (fun j => secInclAddHom D S j W),
              DirectSum.toAddMonoid_of (fun j => secInclAddHom D S j W),
              DirectSum.toAddMonoid_of (fun j => secInclAddHom D S j W)]
            exact secIncl_mul D S b b' W
        | add w w' hw hw' => rw [mul_add, map_add, map_add, hw, hw', mul_add]
    | add w w' hw hw' => rw [add_mul, map_add, map_add, hw, hw', add_mul]

/-- **The ring map `B →+* Γ(𝓐, W)`**: the decomposition of `B` into its homogeneous parts,
followed by the inclusions of the global sections they name. -/
def secRingHom (W : (Opens ↥X)ᵒᵖ) : B →+* ↥(AlgebraSheaf.sections D.sheaf W.unop) :=
  (secRingHomDirectSum D S W).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom

/-- **The only description of the ring map**: on a homogeneous element of degree `k` it is the
degree-`k` inclusion of the global section that element names. -/
theorem secRingHom_coe {k : ℕ} (b : ↥(𝒜 k)) (W : (Opens ↥X)ᵒᵖ) :
    secRingHom D S W (b : B) = secIncl D S b W := by
  show secRingHomDirectSum D S W (DirectSum.decompose 𝒜 (b : B)) = _
  rw [DirectSum.decompose_coe]
  exact DirectSum.toAddMonoid_of (fun j => secInclAddHom D S j W) k b

/-! ### `β : 𝔅 ⟶ f_* 𝓐` and its adjoint transpose `ψ : f^* 𝔅 ⟶ 𝓐` -/

variable (f : X ⟶ Spec (.of A))

/-- The ring map on global sections out of which `β` is built: the identification
`Γ(Spec B, ⊤) ≅ B` followed by `HomogeneousSections.secRingHom`. -/
def baseSectionsHom :
    AlgebraSheaf.sections (pushforwardAlgebra (algebraSpecToBase A B)) ⊤ ⟶
      AlgebraSheaf.sections ((algebraPushforward f).obj D.sheaf) ⊤ :=
  sectionsCommRingHom (pushforwardAlgebra (algebraSpecToBase A B))
    ((algebraPushforward f).obj D.sheaf) ⊤ ⊤
    ((secRingHom D S (op (f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens)))).comp
      (Scheme.ΓSpecIso (.of B)).hom.hom)

/-- **The compatibility of `HomogeneousSections.baseSectionsHom` with the two structure maps.**
It is what makes `β` a morphism of sheaves of `𝒪_{Spec A}`-algebras rather than merely of
sheaves of rings, and it is *not* a consequence of the `HomogeneousSections` laws: those say
nothing about the `A`-algebra structure of `B`. -/
def IsStructureCompatible : Prop :=
  (pushforwardAlgebra (algebraSpecToBase A B)).unitTop ≫ baseSectionsHom D S f =
    ((algebraPushforward f).obj D.sheaf).unitTop

/-- **`β : 𝔅 ⟶ f_* 𝓐`**, the morphism of sheaves of commutative `𝒪_{Spec A}`-algebras out of the
pushed-forward structure sheaf of `Spec B ⟶ Spec A`. The base `Spec A` is affine and `𝔅` is
quasi-coherent, so a morphism out of it is exactly a ring map on global sections compatible with
the two structure maps. -/
def baseAlgebraHom (hsc : IsStructureCompatible D S f) :
    pushforwardAlgebra (algebraSpecToBase A B) ⟶ (algebraPushforward f).obj D.sheaf :=
  AlgebraSheaf.algebraHom _ _ hsc

/-- `β` on global sections is `HomogeneousSections.baseSectionsHom`. -/
theorem baseAlgebraHom_right_app_top (hsc : IsStructureCompatible D S f) :
    (baseAlgebraHom D S f hsc).right.hom.app (op ⊤) = baseSectionsHom D S f :=
  AlgebraSheaf.algebraHom_right_app_top _ _ hsc

/-- **`ψ : f^* 𝔅 ⟶ 𝓐`, the adjoint transpose of `β`**, where `f^*` is the *algebra* pullback
`f⁻¹(−) ⊗_{f⁻¹𝒪} 𝒪_X` — the pullback a relative spectrum over `X` consumes and the one
[Stacks, Tag 01LX] part (2) produces. -/
def basePullbackHom (hsc : IsStructureCompatible D S f) :
    (algebraPullback f).obj (pushforwardAlgebra (algebraSpecToBase A B)) ⟶ D.sheaf :=
  ((algebraPullbackPushforwardAdjunction f).homEquiv _ _).symm (baseAlgebraHom D S f hsc)

/-- **The adjunction identity defining `ψ`**: the unit of the base-change adjunction for algebra
sheaves followed by the pushforward of `ψ` is `β`. -/
theorem unit_comp_map_basePullbackHom (hsc : IsStructureCompatible D S f) :
    (algebraPullbackPushforwardAdjunction f).unit.app
          (pushforwardAlgebra (algebraSpecToBase A B)) ≫
        (algebraPushforward f).map (basePullbackHom D S f hsc) =
      baseAlgebraHom D S f hsc :=
  (Adjunction.homEquiv_unit (algebraPullbackPushforwardAdjunction f)
      (pushforwardAlgebra (algebraSpecToBase A B)) D.sheaf
      (basePullbackHom D S f hsc)).symm.trans
    (Equiv.apply_symm_apply
      ((algebraPullbackPushforwardAdjunction f).homEquiv
        (pushforwardAlgebra (algebraSpecToBase A B)) D.sheaf) _)

/-- **The handle on `ψ`**: on the unit image of a global section of `𝔅` it is `β` on that
section. This is the entry point for the local surjectivity of `ψ`: by
`HomogeneousSections.secRingHom_coe` the right-hand side on a homogeneous `b ∈ 𝒜ₖ` is the
degree-`k` inclusion of the global section `b` names. -/
theorem basePullbackHom_app_unit (hsc : IsStructureCompatible D S f)
    (c : AlgebraSheaf.sections (pushforwardAlgebra (algebraSpecToBase A B)) ⊤) :
    (basePullbackHom D S f hsc).right.hom.app
        (op (f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens)))
        (((algebraPullbackPushforwardAdjunction f).unit.app
          (pushforwardAlgebra (algebraSpecToBase A B))).right.hom.app (op ⊤) c) =
      baseSectionsHom D S f c := by
  have h := congrArg (fun t : pushforwardAlgebra (algebraSpecToBase A B) ⟶
      (algebraPushforward f).obj D.sheaf => ConcreteCategory.hom (t.right.hom.app (op ⊤)) c)
    (unit_comp_map_basePullbackHom D S f hsc)
  rw [baseAlgebraHom_right_app_top] at h
  exact h

end HomogeneousSections

/-! ### `Spec(B) ×_{Spec A} X = Spec_X(f^* 𝔅)`, and the structure morphism of `X'` -/

variable {X : Scheme.{u}} {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (f : X ⟶ Spec (.of A))

/-- **`f^* 𝔅 ≅ pr₂_* 𝒪_{Spec(B) ×_{Spec A} X}`**: the base-change comparison of
[Stacks, Tag 01SA], an isomorphism because `g : Spec B ⟶ Spec A` is affine. -/
def baseChangePullbackAlgebraIso :
    (algebraPullback f).obj (pushforwardAlgebra (algebraSpecToBase A B)) ≅
      pushforwardAlgebra ((Over.pullback f).obj (Over.mk (algebraSpecToBase A B))).hom :=
  haveI := isIso_baseChangeAlgebraHom f (Over.mk (algebraSpecToBase A B))
  asIso (baseChangeAlgebraHom f (Over.mk (algebraSpecToBase A B)))

/-- The base-change comparison cancels against its inverse. -/
theorem baseChangeAlgebraHom_comp_baseChangePullbackAlgebraIso_inv :
    baseChangeAlgebraHom f (Over.mk (algebraSpecToBase A B)) ≫
        (baseChangePullbackAlgebraIso B f).inv =
      𝟙 _ :=
  have := isIso_baseChangeAlgebraHom f (Over.mk (algebraSpecToBase A B))
  (asIso (baseChangeAlgebraHom f (Over.mk (algebraSpecToBase A B)))).hom_inv_id

/-- **The honest base change `Spec(B) ×_{Spec A} X` is `Spec_X(f^* 𝔅)`**, the relative spectrum
over `X` of the algebra pullback of `𝔅 = g_* 𝒪_{Spec B}`, as an isomorphism over `X` whose
algebra map is the base-change comparison — which is what makes the ring map of the structure
morphism below computable. -/
def baseChangeRelativeSpecIso :
    ((Over.pullback f).obj (Over.mk (algebraSpecToBase A B)) : Over X) ≅
      Over.mk (relativeSpecToBase
        ((algebraPullback f).obj (pushforwardAlgebra (algebraSpecToBase A B)))) :=
  relativeSpecOverIsoOfAlgebraIso
    ((Over.pullback f).obj (Over.mk (algebraSpecToBase A B))).hom
    ((algebraPullback f).obj (pushforwardAlgebra (algebraSpecToBase A B)))
    (baseChangePullbackAlgebraIso B f).symm

/-- The inverse of the comparison is the morphism `fromRelativeSpecOfAlgebraIso` of
[Stacks, Tag 01S8], whose algebra map is computed. -/
theorem baseChangeRelativeSpecIso_inv :
    (baseChangeRelativeSpecIso B f).inv =
      fromRelativeSpecOfAlgebraIso
        ((Over.pullback f).obj (Over.mk (algebraSpecToBase A B))).hom
        ((algebraPullback f).obj (pushforwardAlgebra (algebraSpecToBase A B)))
        (baseChangePullbackAlgebraIso B f).symm :=
  rfl

namespace GradedQcohAlgebra

/-- The morphism `X' = Spec_X(𝓐) ⟶ Spec(B) ×_{Spec A} X` over `X` attached to a morphism of
algebra sheaves `ψ : f^* 𝔅 ⟶ 𝓐`: the relative spectrum of `ψ`, followed by the identification of
`Spec_X(f^* 𝔅)` with the base change. -/
def relSpecToPullbackOver (D : GradedQcohAlgebra X)
    (ψ : (algebraPullback f).obj (pushforwardAlgebra (algebraSpecToBase A B)) ⟶ D.sheaf) :
    (Over.mk (relativeSpecToBase D.sheaf) : Over X) ⟶
      (Over.pullback f).obj (Over.mk (algebraSpecToBase A B)) :=
  relativeSpecMapOfAlgebraHom
      ((algebraPullback f).obj (pushforwardAlgebra (algebraSpecToBase A B))) D.sheaf ψ ≫
    (baseChangeRelativeSpecIso B f).inv

/-- `GradedQcohAlgebra.relSpecToPullbackOver` on underlying schemes. -/
def relSpecToPullback (D : GradedQcohAlgebra X)
    (ψ : (algebraPullback f).obj (pushforwardAlgebra (algebraSpecToBase A B)) ⟶ D.sheaf) :
    D.relSpec.left ⟶ pullback (algebraSpecToBase A B) f :=
  (relSpecToPullbackOver B f D ψ).left

/-- **A locally surjective `ψ : f^* 𝔅 ⟶ 𝓐` exhibits `X' = Spec_X(𝓐)` as a closed subscheme of
the honest base change `Spec(B) ×_{Spec A} X`.** -/
theorem isClosedImmersion_relSpecToPullback (D : GradedQcohAlgebra X)
    (ψ : (algebraPullback f).obj (pushforwardAlgebra (algebraSpecToBase A B)) ⟶ D.sheaf)
    (hψ : CategoryTheory.Sheaf.IsLocallySurjective ψ.right) :
    _root_.AlgebraicGeometry.IsClosedImmersion (relSpecToPullback B f D ψ) :=
  have hci := Stacks.RelativeSpecClosedImmersion.isClosedImmersion_relativeSpecMapOfAlgebraHom
    ((algebraPullback f).obj (pushforwardAlgebra (algebraSpecToBase A B))) D.sheaf ψ hψ
  have hiso : IsIso (baseChangeRelativeSpecIso B f).inv.left :=
    show IsIso ((Over.forget X).map (baseChangeRelativeSpecIso B f).inv) from
      inferInstance
  @_root_.AlgebraicGeometry.IsClosedImmersion.comp _ _ _ _ _ hci inferInstance

/-! #### The ring map of the structure morphism on global sections -/

attribute [local irreducible] baseChangePullbackAlgebraIso

/-- The algebra map of the comparison, split at its two factors. -/
theorem pushforwardAlgebraMap_relSpecToPullbackOver_comp (D : GradedQcohAlgebra X)
    (ψ : (algebraPullback f).obj (pushforwardAlgebra (algebraSpecToBase A B)) ⟶ D.sheaf) :
    pushforwardAlgebraMap (relSpecToPullbackOver B f D ψ) =
      pushforwardAlgebraMap ((baseChangeRelativeSpecIso B f).inv) ≫
        pushforwardAlgebraMap (relativeSpecMapOfAlgebraHom
          ((algebraPullback f).obj (pushforwardAlgebra (algebraSpecToBase A B)))
          D.sheaf ψ) :=
  pushforwardAlgebraMap_comp _ _

/-- The algebra map of the identification of the base change with `Spec_X(f^* 𝔅)`. -/
theorem pushforwardAlgebraMap_baseChangeRelativeSpecIso_inv :
    pushforwardAlgebraMap ((baseChangeRelativeSpecIso B f).inv) =
      (baseChangePullbackAlgebraIso B f).symm.hom ≫
        (pushforwardAlgebraIso ((algebraPullback f).obj
          (pushforwardAlgebra (algebraSpecToBase A B)))).inv :=
  (congrArg (fun u => pushforwardAlgebraMap u) (baseChangeRelativeSpecIso_inv B f)).trans
    (pushforwardAlgebraMap_fromRelativeSpecOfAlgebraIso _ _ _)

/-- **The algebra map of the comparison is `ψ`**, between the two identifications. -/
theorem pushforwardAlgebraMap_relSpecToPullbackOver (D : GradedQcohAlgebra X)
    (ψ : (algebraPullback f).obj (pushforwardAlgebra (algebraSpecToBase A B)) ⟶ D.sheaf) :
    pushforwardAlgebraMap (relSpecToPullbackOver B f D ψ) =
      (baseChangePullbackAlgebraIso B f).inv ≫ ψ ≫ (pushforwardAlgebraIso D.sheaf).inv := by
  rw [pushforwardAlgebraMap_relSpecToPullbackOver_comp,
    pushforwardAlgebraMap_baseChangeRelativeSpecIso_inv,
    pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]

/-- The ring map of the comparison on global sections is the `⊤`-component of its algebra map. -/
theorem appTop_relSpecToPullback (D : GradedQcohAlgebra X)
    (ψ : (algebraPullback f).obj (pushforwardAlgebra (algebraSpecToBase A B)) ⟶ D.sheaf) :
    (pushforwardAlgebraMap (relSpecToPullbackOver B f D ψ)).right.hom.app (op ⊤) =
      (relSpecToPullback B f D ψ).appTop := by
  rw [pushforwardAlgebraMap_app (relSpecToPullbackOver B f D ψ) ⊤
    (preimage_le_preimage_preimage _ _)]
  exact (relSpecToPullback B f D ψ).appLE_eq_app

/-- **The ring map of the comparison on global sections** is `ψ`, between the two
identifications. -/
theorem appTop_relSpecToPullback_eq (D : GradedQcohAlgebra X)
    (ψ : (algebraPullback f).obj (pushforwardAlgebra (algebraSpecToBase A B)) ⟶ D.sheaf) :
    (relSpecToPullback B f D ψ).appTop =
      (baseChangePullbackAlgebraIso B f).inv.right.hom.app (op ⊤) ≫
        ψ.right.hom.app (op ⊤) ≫
        (pushforwardAlgebraIso D.sheaf).inv.right.hom.app (op ⊤) := by
  rw [← appTop_relSpecToPullback, pushforwardAlgebraMap_relSpecToPullbackOver]
  rfl

/-- The canonical map attached to the fibre-product projection is the adjunct of the base-change
comparison; this is how that comparison was defined. -/
theorem homEquiv_baseChangeAlgebraHom :
    pushforwardAlgebraMap (baseChangeProjection f (Over.mk (algebraSpecToBase A B))) =
      (algebraPullbackPushforwardAdjunction f).homEquiv _ _
        (baseChangeAlgebraHom f (Over.mk (algebraSpecToBase A B))) :=
  (((algebraPullbackPushforwardAdjunction f).homEquiv
      (pushforwardAlgebra (Over.mk (algebraSpecToBase A B)).hom)
      (pushforwardAlgebra
        ((Over.pullback f).obj (Over.mk (algebraSpecToBase A B))).hom)).apply_symm_apply
    (pushforwardAlgebraMap (baseChangeProjection f (Over.mk (algebraSpecToBase A B))))).symm

/-- **The ring map of the projection `Spec(B) ×_{Spec A} X ⟶ Spec B` on global sections**: the
unit of the algebra-pullback adjunction, followed by the base-change comparison. -/
theorem appTop_pullbackFst :
    (pullback.fst (Over.mk (algebraSpecToBase A B)).hom f).appTop =
      ((algebraPullbackPushforwardAdjunction f).unit.app
          (pushforwardAlgebra (Over.mk (algebraSpecToBase A B)).hom)).right.hom.app (op ⊤) ≫
        (baseChangeAlgebraHom f (Over.mk (algebraSpecToBase A B))).right.hom.app (op ⊤) := by
  rw [← pushforwardAlgebraMap_baseChangeProjection_app_top f
    (Over.mk (algebraSpecToBase A B)), homEquiv_baseChangeAlgebraHom,
    Adjunction.homEquiv_unit]
  rfl

/-- A cancellation of four composable morphisms, proved in an abstract category: at the concrete
types below `simp` and `rw` cannot associate the composites, because the underlying space of a
scheme has two spellings. -/
private theorem comp_cancel {C : Type u₁} [Category.{v₁} C] {w x y t : C}
    (u : w ⟶ x) (bc : x ⟶ y) (pinv : y ⟶ x) (rest : x ⟶ t) (h : bc ≫ pinv = 𝟙 x) :
    (u ≫ bc) ≫ (pinv ≫ rest) = u ≫ rest := by
  rw [Category.assoc, ← Category.assoc bc pinv rest, h, Category.id_comp]

/-- **The ring map of `f' : X' ⟶ Spec B` on global sections**, reduced to the algebra-pullback
unit followed by `ψ`. This is the form `HomogeneousSections.basePullbackHom_app_unit`
computes. -/
theorem appTop_structureHom_eq (D : GradedQcohAlgebra X)
    (ψ : (algebraPullback f).obj (pushforwardAlgebra (algebraSpecToBase A B)) ⟶ D.sheaf) :
    (relSpecToPullback B f D ψ ≫
        pullback.fst (Over.mk (algebraSpecToBase A B)).hom f).appTop =
      ((algebraPullbackPushforwardAdjunction f).unit.app
          (pushforwardAlgebra (algebraSpecToBase A B))).right.hom.app (op ⊤) ≫
        ψ.right.hom.app (op ⊤) ≫
        (pushforwardAlgebraIso D.sheaf).inv.right.hom.app (op ⊤) := by
  have h1 : (baseChangeAlgebraHom f (Over.mk (algebraSpecToBase A B))).right.hom.app (op ⊤) ≫
      (baseChangePullbackAlgebraIso B f).inv.right.hom.app (op ⊤) = 𝟙 _ :=
    congrArg (fun φ : (algebraPullback f).obj
        (pushforwardAlgebra (algebraSpecToBase A B)) ⟶
        (algebraPullback f).obj (pushforwardAlgebra (algebraSpecToBase A B)) =>
      φ.right.hom.app (op (⊤ : X.Opens)))
      (baseChangeAlgebraHom_comp_baseChangePullbackAlgebraIso_inv B f)
  rw [Scheme.Hom.comp_appTop, appTop_pullbackFst, appTop_relSpecToPullback_eq]
  exact comp_cancel _ _ _ _ h1

end GradedQcohAlgebra

namespace HomogeneousSections

variable {X : Scheme.{u}} {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {𝒜 : ℕ → Submodule A B} [_root_.GradedAlgebra 𝒜] (D : GradedQcohAlgebra X)
  (S : HomogeneousSections D.alg 𝒜) (f : X ⟶ Spec (.of A))

/-- **`f' : X' ⟶ Spec B`, the structure morphism of [Stacks, Tag 0897]'s base change.** -/
def structureHom (hsc : IsStructureCompatible D S f) : D.relSpec.left ⟶ Spec (.of B) :=
  GradedQcohAlgebra.relSpecToPullback B f D (basePullbackHom D S f hsc) ≫
    pullback.fst (algebraSpecToBase A B) f

/-- **`f' : X' ⟶ Spec B` is proper**, granted the local surjectivity of `ψ`. A closed subscheme
of a base change along a proper morphism is proper over the new base ([Stacks, Tag 01W4]). -/
theorem isProper_structureHom (hsc : IsStructureCompatible D S f)
    (hψ : CategoryTheory.Sheaf.IsLocallySurjective (basePullbackHom D S f hsc).right)
    (hf : _root_.AlgebraicGeometry.IsProper f) :
    _root_.AlgebraicGeometry.IsProper (structureHom D S f hsc) :=
  Stacks.Cohomology.FormalFunctions.isProper_comp_pullbackFst_of_isClosedImmersion
    (algebraSpecToBase A B) hf
    (GradedQcohAlgebra.relSpecToPullback B f D (basePullbackHom D S f hsc))
    (GradedQcohAlgebra.isClosedImmersion_relSpecToPullback B f D
      (basePullbackHom D S f hsc) hψ)

end HomogeneousSections

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
