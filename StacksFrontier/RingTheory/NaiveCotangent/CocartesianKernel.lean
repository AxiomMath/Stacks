module

public import Mathlib.RingTheory.Extension.Cotangent.BaseChange
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Defs
public import StacksFrontier.RingTheory.NaiveCotangent.ConormalFiniteProjective
public import StacksFrontier.RingTheory.NaiveCotangent.DerivedBaseChange
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# The kernel of base change on `H⁻¹` of the naive cotangent complex

Let `A → B` be a local complete intersection and let `A → A'` be arbitrary. Write
`B' = A' ⊗[A] B` for the pushout, and assume `A' → B'` is again a local complete intersection.
This file proves that the kernel of the base-change map on degree `-1` homology of the naive
cotangent complex is a finite projective `B'`-module.

## Main results

* `NaiveCotangent.finite_projective_ker_naiveCotangent_baseChange_homology_negOne`
  (Stacks 0FV1).

## Implementation notes

In the two-term model of the naive cotangent complex, degree `-1` homology is the kernel of the
conormal-to-cotangent-space differential, so the kernel of the induced map on `H⁻¹` is the kernel
of the conormal comparison restricted to the source cycles. That is how the conclusion is stated:
no choice of homology model is needed.

The proof runs the argument for an arbitrary finite polynomial presentation `P` of `B` over `A`,
where the conormal module is finite projective because the presentation ideal is Koszul-regular
hence quasi-regular, and then transports the conclusion to the canonical presentation
`Algebra.Generators.self`. The transport is by an explicit split, built from the two comparison
homomorphisms between the presentations: on cycles the two composites agree with the identity,
because two homomorphisms of extensions induce conormal maps differing by a factor through the
differential.

The cocartesian square is represented by its canonical pushout `A' ⊗[A] B`; the `B`-algebra
structure on it is `Algebra.TensorProduct.rightAlgebra`, introduced locally in the statement so
that no global instance is imposed.

## References

* [The Stacks Project, Lemma 15.88.2 (0FV1)](https://stacks.math.columbia.edu/tag/0FV1)
-/

open TensorProduct

namespace NaiveCotangent

universe u v w

/-- The kernel of a surjection from a finite projective module onto a projective module is
finite projective, being a direct summand of the source. -/
@[sga "6 I 1.3" "more general"]
private lemma finite_projective_ker_of_surjective
    {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Finite R M] [Module.Projective R M]
    [Module.Projective R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Module.Finite R (LinearMap.ker f) ∧ Module.Projective R (LinearMap.ker f) := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  let r : M →ₗ[R] LinearMap.ker f :=
    (LinearMap.id - s.comp f).codRestrict _ (by
      intro x
      show f (x - s (f x)) = 0
      simpa using sub_eq_zero.mpr (LinearMap.congr_fun hs (f x)).symm)
  have hr (x : LinearMap.ker f) : r x = x := by
    apply Subtype.ext
    show x.1 - s (f x.1) = x.1
    simp
  exact ⟨Module.Finite.of_surjective r (fun x => ⟨x, hr x⟩),
    Module.Projective.of_split (LinearMap.ker f).subtype r (LinearMap.ext hr)⟩

/-- The comparison of two two-term complexes, one with finite projective conormal term, has
finite projective kernel on cycles as soon as the degree-zero comparison is bijective, the
degree-zero map identifies the images of the differentials, and cycles lift. -/
private lemma finite_projective_ker_on_cycles
    {R M N M' N' : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [Module R M] [Module R N] [Module R M'] [Module R N']
    [Module.Finite R M] [Module.Projective R M] [Module.Projective R M']
    (d : M →ₗ[R] N) (d' : M' →ₗ[R] N') (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (hsq : d'.comp f = g.comp d) (hg : Function.Bijective g)
    (hzero : ∀ x, g x ∈ LinearMap.range d' ↔ x ∈ LinearMap.range d)
    (hone : ∀ y, d' y = 0 → ∃ x, d x = 0 ∧ f x = y) :
    Module.Finite R (LinearMap.ker (f.domRestrict (LinearMap.ker d))) ∧
      Module.Projective R (LinearMap.ker (f.domRestrict (LinearMap.ker d))) := by
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hg.2 (d' y)
    obtain ⟨z, hz⟩ := (hzero x).mp (hx ▸ LinearMap.mem_range_self d' y)
    have hd : d' (y - f z) = 0 := by
      rw [map_sub, show d' (f z) = g (d z) from LinearMap.congr_fun hsq z, hz, hx, sub_self]
    obtain ⟨w, _, hw⟩ := hone _ hd
    exact ⟨w + z, by rw [map_add, hw, sub_add_cancel]⟩
  have hle : LinearMap.ker f ≤ LinearMap.ker d := by
    intro x hx
    apply hg.1
    simpa only [LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero] using
      (LinearMap.congr_fun hsq x).symm
  let e : LinearMap.ker (f.domRestrict (LinearMap.ker d)) ≃ₗ[R] LinearMap.ker f :=
    Submodule.comapSubtypeEquivOfLe hle
  obtain ⟨_, _⟩ := finite_projective_ker_of_surjective f hf
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

/-- Stacks 0FV1 for a chosen finite polynomial presentation and its base change. -/
private lemma finite_projective_baseChange_presentation_kernel
    {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Finite ι] (P : Algebra.Generators R S ι)
    (h : RingHom.IsLocalCompleteIntersection (algebraMap R S)) :
    let S' := T ⊗[R] S
    let : Algebra S S' := Algebra.TensorProduct.rightAlgebra
    RingHom.IsLocalCompleteIntersection (algebraMap T S') →
    let c := (P.baseChangeFromBaseChange T).comp (P.toExtension.toBaseChange T)
    let d := AlgebraTensorModule.lTensor S' S' P.toExtension.cotangentComplex
    let f := (Algebra.Extension.Cotangent.map c).liftBaseChange S'
    Module.Finite S' (LinearMap.ker (f.domRestrict (LinearMap.ker d))) ∧
      Module.Projective S' (LinearMap.ker (f.domRestrict (LinearMap.ker d))) := by
  let S' := T ⊗[R] S
  let : Algebra S S' := Algebra.TensorProduct.rightAlgebra
  dsimp only
  intro h'
  obtain ⟨_, _⟩ :=
    Algebra.Generators.cotangent_finite_projective_of_isLocalCompleteIntersection P h
  obtain ⟨_, _⟩ :=
    Algebra.Generators.cotangent_finite_projective_of_isLocalCompleteIntersection
      (P.baseChange T) h'
  have H := naiveCotangentComplex_baseChange_homology (T := T) P
  exact finite_projective_ker_on_cycles _ _ _ _ H.1
    (cotangentSpace_baseChange_bijective P) H.2.2.1 H.2.2.2.1

/-- Two maps of modules differing by a factor through `d` agree after tensoring, on cycles. -/
private lemma tensor_eq_on_cycles
    {R T M N Q : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R Q]
    (d : M →ₗ[R] N) (f g : M →ₗ[R] Q) (h : N →ₗ[R] Q)
    (hfg : f - g = h.comp d) (x : T ⊗[R] M)
    (hx : AlgebraTensorModule.lTensor T T d x = 0) :
    AlgebraTensorModule.lTensor T T f x = AlgebraTensorModule.lTensor T T g x := by
  have H := congrArg (AlgebraTensorModule.lTensor T T) hfg
  rw [map_sub, AlgebraTensorModule.lTensor_comp] at H
  simpa only [LinearMap.sub_apply, LinearMap.comp_apply, hx, map_zero, sub_eq_zero] using
    LinearMap.congr_fun H x

/-- The same statement for the base-change lifts of the two maps. -/
private lemma lift_eq_on_cycles
    {R T M N Q : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R Q] [Module T Q] [IsScalarTower R T Q]
    (d : M →ₗ[R] N) (f g : M →ₗ[R] Q) (h : N →ₗ[R] Q)
    (hfg : f - g = h.comp d) (x : T ⊗[R] M)
    (hx : AlgebraTensorModule.lTensor T T d x = 0) :
    f.liftBaseChange T x = g.liftBaseChange T x := by
  have H : f.liftBaseChange T - g.liftBaseChange T =
      (h.liftBaseChange T).comp (AlgebraTensorModule.lTensor T T d) := by
    apply AlgebraTensorModule.ext
    intro t m
    have Hm := LinearMap.congr_fun hfg m
    simp only [LinearMap.sub_apply, LinearMap.comp_apply] at Hm
    simp only [LinearMap.sub_apply, LinearMap.liftBaseChange_tmul,
      LinearMap.comp_apply, AlgebraTensorModule.lTensor_tmul, ← smul_sub, Hm]
  simpa only [LinearMap.sub_apply, LinearMap.comp_apply, hx, map_zero, sub_eq_zero] using
    LinearMap.congr_fun H x

/-- The conormal map of a homomorphism of extensions carries cycles to cycles. -/
private lemma tensor_cotangent_map_cycles
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] {P Q : Algebra.Extension R S} (a : P.Hom Q)
    (x : T ⊗[S] P.Cotangent)
    (hx : AlgebraTensorModule.lTensor T T P.cotangentComplex x = 0) :
    AlgebraTensorModule.lTensor T T Q.cotangentComplex
      (AlgebraTensorModule.lTensor T T (Algebra.Extension.Cotangent.map a) x) = 0 := by
  have H : (AlgebraTensorModule.lTensor T T Q.cotangentComplex).comp
        (AlgebraTensorModule.lTensor T T (Algebra.Extension.Cotangent.map a)) =
      (AlgebraTensorModule.lTensor T T (Algebra.Extension.CotangentSpace.map a)).comp
        (AlgebraTensorModule.lTensor T T P.cotangentComplex) := by
    apply AlgebraTensorModule.ext
    intro t z
    simp only [LinearMap.comp_apply, AlgebraTensorModule.lTensor_tmul,
      Algebra.Extension.CotangentSpace.map_cotangentComplex]
  simpa only [LinearMap.comp_apply, hx, map_zero] using LinearMap.congr_fun H x

/-- On cycles, the conormal maps of two opposite homomorphisms of extensions are mutually
inverse. -/
private lemma tensor_cotangent_map_comp_on_cycles
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] {P Q : Algebra.Extension R S}
    (a : P.Hom Q) (b : Q.Hom P) (x : T ⊗[S] P.Cotangent)
    (hx : AlgebraTensorModule.lTensor T T P.cotangentComplex x = 0) :
    AlgebraTensorModule.lTensor T T (Algebra.Extension.Cotangent.map b)
      (AlgebraTensorModule.lTensor T T (Algebra.Extension.Cotangent.map a) x) = x := by
  have H := tensor_eq_on_cycles P.cotangentComplex
    (Algebra.Extension.Cotangent.map (b.comp a))
    (Algebra.Extension.Cotangent.map (Algebra.Extension.Hom.id P))
    ((b.comp a).sub (Algebra.Extension.Hom.id P))
    (Algebra.Extension.Cotangent.map_sub_map _ _) x hx
  simpa only [Algebra.Extension.Cotangent.map_comp,
    LinearMap.restrictScalars_self, AlgebraTensorModule.lTensor_comp,
    Algebra.Extension.Cotangent.map_id, AlgebraTensorModule.lTensor_id,
    LinearMap.comp_apply, LinearMap.id_apply] using H

section Comparison

variable {R S R' S' : Type*}
  [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
  [Algebra R S] [Algebra R' S'] [Algebra R R'] [Algebra S S'] [Algebra R S']
  [IsScalarTower R R' S'] [IsScalarTower R S S']
  {P Q : Algebra.Extension R S} {P' Q' : Algebra.Extension R' S'}

/-- On cycles, the square of conormal comparison maps attached to two presentations on each
side of a base change commutes. -/
private lemma lift_cotangent_naturality_on_cycles
    (a : P.Hom Q) (a' : P'.Hom Q') (c : P.Hom P') (e : Q.Hom Q')
    (x : S' ⊗[S] P.Cotangent)
    (hx : AlgebraTensorModule.lTensor S' S' P.cotangentComplex x = 0) :
    (Algebra.Extension.Cotangent.map e).liftBaseChange S'
        (AlgebraTensorModule.lTensor S' S' (Algebra.Extension.Cotangent.map a) x) =
      Algebra.Extension.Cotangent.map a'
        ((Algebra.Extension.Cotangent.map c).liftBaseChange S' x) := by
  have hleft : (Algebra.Extension.Cotangent.map (e.comp a)).liftBaseChange S' =
      ((Algebra.Extension.Cotangent.map e).liftBaseChange S').comp
        (AlgebraTensorModule.lTensor S' S' (Algebra.Extension.Cotangent.map a)) := by
    apply AlgebraTensorModule.ext
    intro t z
    simp only [LinearMap.liftBaseChange_tmul, LinearMap.comp_apply,
      AlgebraTensorModule.lTensor_tmul, Algebra.Extension.Cotangent.map_comp,
      LinearMap.restrictScalars_apply]
  have hright : (Algebra.Extension.Cotangent.map (a'.comp c)).liftBaseChange S' =
      (Algebra.Extension.Cotangent.map a').comp
        ((Algebra.Extension.Cotangent.map c).liftBaseChange S') := by
    apply AlgebraTensorModule.ext
    intro t z
    simp only [LinearMap.liftBaseChange_tmul, LinearMap.comp_apply,
      Algebra.Extension.Cotangent.map_comp, LinearMap.restrictScalars_apply, map_smul]
  have H := lift_eq_on_cycles P.cotangentComplex
    (Algebra.Extension.Cotangent.map (e.comp a))
    (Algebra.Extension.Cotangent.map (a'.comp c))
    ((e.comp a).sub (a'.comp c))
    (Algebra.Extension.Cotangent.map_sub_map _ _) x hx
  rwa [hleft, hright] at H

/-- A homomorphism of extensions compatible with the base-change comparisons induces a linear map
between the kernels on cycles. -/
private lemma exists_ker_map
    (a : P.Hom Q) (a' : P'.Hom Q') (c : P.Hom P') (e : Q.Hom Q') :
    let dP := AlgebraTensorModule.lTensor S' S' P.cotangentComplex
    let dQ := AlgebraTensorModule.lTensor S' S' Q.cotangentComplex
    let fP := (Algebra.Extension.Cotangent.map c).liftBaseChange S'
    let fQ := (Algebra.Extension.Cotangent.map e).liftBaseChange S'
    ∃ g : LinearMap.ker (fP.domRestrict (LinearMap.ker dP)) →ₗ[S']
        LinearMap.ker (fQ.domRestrict (LinearMap.ker dQ)),
      ∀ x, (g x).1.1 =
        AlgebraTensorModule.lTensor S' S' (Algebra.Extension.Cotangent.map a) x.1.1 := by
  intro dP dQ fP fQ
  let s := AlgebraTensorModule.lTensor S' S' (Algebra.Extension.Cotangent.map a)
  have hs (x : LinearMap.ker (fP.domRestrict (LinearMap.ker dP))) : fQ (s x.1.1) = 0 := by
    rw [lift_cotangent_naturality_on_cycles a a' c e _ x.1.2]
    show Algebra.Extension.Cotangent.map a' (fP x.1.1) = 0
    rw [show fP x.1.1 = 0 from x.2, map_zero]
  exact ⟨{ toFun := fun x => ⟨⟨s x.1.1, tensor_cotangent_map_cycles a _ x.1.2⟩, hs x⟩
           map_add' _ _ := Subtype.ext <| Subtype.ext <| map_add s _ _
           map_smul' _ _ := Subtype.ext <| Subtype.ext <| map_smul s _ _ }, fun _ => rfl⟩

/-- Finite projectivity of the kernel on cycles transports between presentations, along the
split built from a pair of opposite comparison homomorphisms. -/
private lemma finite_projective_ker_transport
    (a : P.Hom Q) (b : Q.Hom P) (a' : P'.Hom Q') (b' : Q'.Hom P')
    (c : P.Hom P') (e : Q.Hom Q') :
    let dP := AlgebraTensorModule.lTensor S' S' P.cotangentComplex
    let dQ := AlgebraTensorModule.lTensor S' S' Q.cotangentComplex
    let fP := (Algebra.Extension.Cotangent.map c).liftBaseChange S'
    let fQ := (Algebra.Extension.Cotangent.map e).liftBaseChange S'
    Module.Finite S' (LinearMap.ker (fP.domRestrict (LinearMap.ker dP))) →
    Module.Projective S' (LinearMap.ker (fP.domRestrict (LinearMap.ker dP))) →
    Module.Finite S' (LinearMap.ker (fQ.domRestrict (LinearMap.ker dQ))) ∧
      Module.Projective S' (LinearMap.ker (fQ.domRestrict (LinearMap.ker dQ))) := by
  intro dP dQ fP fQ _ _
  obtain ⟨sK, hsK⟩ := exists_ker_map a a' c e
  obtain ⟨rK, hrK⟩ := exists_ker_map b b' e c
  have H x : sK (rK x) = x := Subtype.ext <| Subtype.ext <| by
    rw [hsK, hrK]
    exact tensor_cotangent_map_comp_on_cycles b a x.1.1 x.1.2
  exact ⟨Module.Finite.of_surjective sK (fun x => ⟨rK x, H x⟩),
    Module.Projective.of_split rK sK (LinearMap.ext H)⟩

end Comparison

/-- **Stacks 0FV1.** In a pushout square of rings, if both parallel maps are local complete
intersections, then the kernel of the base-change map on degree `-1` homology of the naive
cotangent complex is a finite projective module over the pushout. -/
@[stacks 0FV1]
public theorem finite_projective_ker_naiveCotangent_baseChange_homology_negOne
    {A : Type u} {B : Type v} {A' : Type w}
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
    (h : RingHom.IsLocalCompleteIntersection (algebraMap A B)) :
    let B' := A' ⊗[A] B
    letI : Algebra B B' := Algebra.TensorProduct.rightAlgebra
    RingHom.IsLocalCompleteIntersection (algebraMap A' B') →
      let P := Algebra.Generators.self A B
      let P' := Algebra.Generators.self A' B'
      let comparison := (P.defaultHom P').toExtensionHom
      let d := AlgebraTensorModule.lTensor B' B' P.toExtension.cotangentComplex
      let f := (Algebra.Extension.Cotangent.map comparison).liftBaseChange B'
      Module.Finite B' (LinearMap.ker (f.domRestrict (LinearMap.ker d))) ∧
        Module.Projective B' (LinearMap.ker (f.domRestrict (LinearMap.ker d))) := by
  let B' := A' ⊗[A] B
  let : Algebra B B' := Algebra.TensorProduct.rightAlgebra
  dsimp only
  intro h'
  obtain ⟨n, ⟨P⟩⟩ :=
    Algebra.FiniteType.iff_exists_generators.mp (RingHom.finiteType_algebraMap.mp h.1)
  obtain ⟨hf, hp⟩ := finite_projective_baseChange_presentation_kernel P h h'
  let Pc := Algebra.Generators.self A B
  let Pc' := Algebra.Generators.self A' B'
  let P' := P.baseChange A'
  exact finite_projective_ker_transport
    (P.defaultHom Pc).toExtensionHom (Pc.defaultHom P).toExtensionHom
    (P'.defaultHom Pc').toExtensionHom (Pc'.defaultHom P').toExtensionHom
    ((P.baseChangeFromBaseChange A').comp (P.toExtension.toBaseChange A'))
    (Pc.defaultHom Pc').toExtensionHom hf hp

end NaiveCotangent
