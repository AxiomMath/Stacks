module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebrasPieces
public import StacksFrontier.RingTheory.Flat.SquareZeroBaseChange
public import StacksFrontier.RingTheory.Module.Projective.NilpotentIdeal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A lifted presentation of a graded deformation is an isomorphism

Let `P` be a graded `k`-algebra with finite-dimensional graded pieces, let `A` be an Artinian
local algebra with residue field `k` and let `X` be a deformation of `P` over `A`: a graded
`A`-algebra, finite projective in each degree, with an identification of its reduction with
`P`. A *lifted presentation* of `X` is a map of graded `A`-algebras `φ : S → X` which, in each
degree, becomes a surjection onto the corresponding piece of `P` whose kernel lies inside
`𝔪 S_d`. This file proves that such a `φ` is bijective, and that two deformations sharing one
lifted presentation are isomorphic in the fibre of the deformation category over `A`.

The mechanism is Nakayama's lemma for a nilpotent ideal in both directions, degree by degree.
The maximal ideal `𝔪` of `A` is nilpotent because `A` is Artinian local, and the comparison
`X_d → P_d` with the special fibre is surjective with kernel `𝔪 X_d`, which is what
`Deformation.Examples.ProjectiveGradedAlgebra.homPiece_isBaseChange` says once the kernel of a
base change along a surjection is read off by
`IsBaseChange.ker_eq_ker_algebraMap_smul_top`. So `φ_d` is surjective modulo a nilpotent ideal,
hence surjective, and its kernel lies in `𝔪 S_d`, which together with flatness of `X_d` — free
from the projectivity of a deformation — forces it to vanish. Both halves are
`LinearMap.bijective_of_isNilpotent_of_ker_le_smul_top`.

## Main results

* `LinearMap.bijective_of_isNilpotent_of_comp_bijective`: a map into a flat module which becomes
  a surjection with small kernel after composing with a map whose kernel is `I • ⊤` is bijective.
* `IsBaseChange.of_bijective_of_surjective_algebraMap`: a bijective comparison along a surjection
  of base rings is a base change.
* `Deformation.Examples.decompose_apply_gradedMap`, `bijective_of_bijective_gradedPieces` and
  `mem_gradedPiece_of_injective`: a graded additive map commutes with homogeneous components, is
  bijective as soon as it is bijective in each degree, and, when injective, detects homogeneity.
* `Deformation.Examples.nonempty_fiber_iso_of_iso`: an isomorphism whose projection is the
  comparison of two fibre memberships is an isomorphism of the fibre.
* `Deformation.Examples.ProjectiveGradedAlgebra.surjective_homPieceMap` and `ker_homPieceMap`:
  the comparison of the `d`-th graded piece of a deformation with that of its special fibre is
  surjective with kernel `𝔪 X_d`.
* `Deformation.Examples.ProjectiveGradedAlgebra.bijective_of_gradedPresentation`: a lifted
  presentation of a deformation is bijective, and bijective in each degree.
* `Deformation.Examples.ProjectiveGradedAlgebra.exists_gradedRingEquiv_of_bijective_presentations`:
  two deformations with a common bijective presentation are related by a bijective graded ring
  map.
* `Deformation.Examples.ProjectiveGradedAlgebra.exists_iso_of_gradedRingEquiv`,
  `exists_iso_over_of_gradedRingEquiv` and `nonempty_fiber_iso_of_gradedRingEquiv`: such a map is
  an isomorphism of graded algebras, of the deformation category, and of the fibre over the
  common base.

## Implementation notes

The hypotheses of the presentation criterion are stated with the special-fibre comparison map
`H.map` and membership in the graded pieces, not with the degreewise comparison
`homPieceMap`: the latter carries a tower of `Algebra` and `IsScalarTower` instances in its very
type, and keeping it out of the statements is what makes them usable without reproducing that
tower at each call site.

Two graded algebras over one base are not in general given with syntactically equal bases, so the
comparison morphism is built over `eqToHom` of an equality of bases rather than over an identity.
This is why `IsBaseChange.of_bijective_of_surjective_algebraMap` is stated for a surjection of
base rings instead of using `IsBaseChange.ofEquiv`: `eqToHom` of an equality of objects of `𝒞_Λ`
is not the identity ring map, and no `cases` on the equality — which would force unpacking the
whole graded-algebra structure — is then needed anywhere.

The graded lemmas are stated for an additive map between graded modules over *two different*
base rings, since that is the shape the comparison of two deformations has before their bases are
identified.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u v w m

/-- A map `f` into a flat module over a commutative ring with a nilpotent ideal `I` is
bijective as soon as there is a map `π` with kernel exactly `I • ⊤` for which `π ∘ f` is
surjective with kernel inside `I • ⊤`.

This is `LinearMap.bijective_of_isNilpotent_of_ker_le_smul_top` in the form a deformation
supplies its input: the reduction of a module over a square-zero or nilpotent extension is not
given as a quotient but as the special fibre, together with a surjection onto it whose kernel is
`I` times the module. -/
public theorem LinearMap.bijective_of_isNilpotent_of_comp_bijective
    {R : Type*} [CommRing R] {I : Ideal R} {S M N : Type*}
    [AddCommGroup S] [Module R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Flat R M] (hI : IsNilpotent I) (f : S →ₗ[R] M) (π : M →ₗ[R] N)
    (hπ : LinearMap.ker π = I • (⊤ : Submodule R M))
    (hsurj : Function.Surjective (π ∘ₗ f))
    (hker : LinearMap.ker (π ∘ₗ f) ≤ I • (⊤ : Submodule R S)) :
    Function.Bijective f := by
  refine LinearMap.bijective_of_isNilpotent_of_ker_le_smul_top hI f ?_
    ((LinearMap.ker_le_ker_comp f π).trans hker)
  intro y
  obtain ⟨x, rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective y
  obtain ⟨s, hs⟩ := hsurj (π x)
  refine ⟨s, ?_⟩
  have hmem : f s - x ∈ I • (⊤ : Submodule R M) := by
    rw [← hπ, LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact hs
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq]
  exact hmem

/-- A bijective comparison along a surjection of base rings is a base change: the surjection
forces the kernel ideal to annihilate both modules, and a bijection between modules on which it
acts trivially is the extension of scalars.

This is `IsBaseChange.ofEquiv` with the identity of the base ring replaced by any surjection,
which is the form in which a morphism of deformations over one base is recognised: its base
morphism is an isomorphism, and its underlying map is bijective. -/
public theorem IsBaseChange.of_bijective_of_surjective_algebraMap
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N]
    (hRS : Function.Surjective (algebraMap R S)) {f : M →ₗ[R] N}
    (hf : Function.Bijective f) : IsBaseChange S f := by
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ g
  let e := LinearEquiv.ofBijective f hf
  have hfe : ∀ m : M, e m = f m := fun _ ↦ rfl
  have hef : ∀ m : M, e.symm (f m) = m := fun m ↦ by rw [← hfe m, e.symm_apply_apply]
  have hfe' : ∀ n : N, f (e.symm n) = n := fun n ↦ by rw [← hfe, e.apply_symm_apply]
  refine ⟨{ toFun := fun n ↦ g (e.symm n)
            map_add' := fun a b ↦ by rw [map_add, map_add]
            map_smul' := ?_ }, ?_, ?_⟩
  · intro s n
    obtain ⟨r, rfl⟩ := hRS s
    show g (e.symm (algebraMap R S r • n)) = algebraMap R S r • g (e.symm n)
    rw [algebraMap_smul, algebraMap_smul, map_smul, map_smul]
  · refine LinearMap.ext fun m ↦ ?_
    show g (e.symm (f m)) = g m
    rw [hef m]
  · intro h hh
    refine LinearMap.ext fun n ↦ ?_
    have key : h (f (e.symm n)) = g (e.symm n) :=
      congrArg (fun F : M →ₗ[R] Q ↦ F (e.symm n)) hh
    show h n = g (e.symm n)
    rw [← key, hfe' n]

namespace Deformation.Examples

/-- A graded linear map commutes with taking homogeneous components. -/
public theorem decompose_apply_gradedMap
    {R R' S Q : Type*} [CommRing R] [CommRing R'] [AddCommGroup S] [Module R S]
    [AddCommGroup Q] [Module R' Q]
    (𝒮 : ℕ → Submodule R S) (𝒬 : ℕ → Submodule R' Q)
    [DirectSum.Decomposition 𝒮] [DirectSum.Decomposition 𝒬]
    (f : S →+ Q) (hf : ∀ (d : ℕ) (x : S), x ∈ 𝒮 d → f x ∈ 𝒬 d) (x : S) (d : ℕ) :
    ((DirectSum.decompose 𝒬 (f x) d : Q)) = f (DirectSum.decompose 𝒮 x d) := by
  induction x using DirectSum.Decomposition.inductionOn 𝒮 with
  | zero => simp
  | @homogeneous i s =>
      by_cases hid : i = d
      · subst hid
        rw [DirectSum.decompose_of_mem_same 𝒮 s.2,
          DirectSum.decompose_of_mem_same 𝒬 (hf i s.1 s.2)]
      · rw [DirectSum.decompose_of_mem_ne 𝒮 s.2 hid,
          DirectSum.decompose_of_mem_ne 𝒬 (hf i s.1 s.2) hid]
        simp
  | add x y hx hy =>
      rw [map_add, DirectSum.decompose_add, DirectSum.decompose_add]
      rw [DFinsupp.add_apply, DFinsupp.add_apply, Submodule.coe_add, Submodule.coe_add,
        map_add, hx, hy]

/-- A graded linear map which is bijective on each graded piece is bijective. -/
public theorem bijective_of_bijective_gradedPieces
    {R R' S Q : Type*} [CommRing R] [CommRing R'] [AddCommGroup S] [Module R S]
    [AddCommGroup Q] [Module R' Q]
    (𝒮 : ℕ → Submodule R S) (𝒬 : ℕ → Submodule R' Q)
    [DirectSum.Decomposition 𝒮] [DirectSum.Decomposition 𝒬]
    (f : S →+ Q) (hf : ∀ (d : ℕ) (x : S), x ∈ 𝒮 d → f x ∈ 𝒬 d)
    (hbij : ∀ d : ℕ, Function.Bijective fun s : 𝒮 d ↦ (⟨f s, hf d s.1 s.2⟩ : 𝒬 d)) :
    Function.Bijective f := by
  constructor
  · intro x y hxy
    rw [← sub_eq_zero, ← map_sub] at hxy
    have hzero : ∀ d : ℕ, DirectSum.decompose 𝒮 (x - y) d = 0 := by
      intro d
      have h0 : (f (DirectSum.decompose 𝒮 (x - y) d : S) : Q) = f ((0 : 𝒮 d) : S) := by
        rw [← decompose_apply_gradedMap 𝒮 𝒬 f hf, hxy]
        simp
      exact (hbij d).injective (Subtype.ext h0)
    have hd : DirectSum.decompose 𝒮 (x - y) = DirectSum.decompose 𝒮 0 := by
      rw [DirectSum.decompose_zero]
      exact DFinsupp.ext hzero
    rw [← sub_eq_zero]
    exact (DirectSum.decompose 𝒮).injective hd
  · intro q
    induction q using DirectSum.Decomposition.inductionOn 𝒬 with
    | zero => exact ⟨0, map_zero f⟩
    | @homogeneous i t =>
        obtain ⟨s, hs⟩ := (hbij i).surjective t
        exact ⟨s.1, congrArg Subtype.val hs⟩
    | add q q' hq hq' =>
        obtain ⟨s, hs⟩ := hq
        obtain ⟨s', hs'⟩ := hq'
        exact ⟨s + s', by rw [map_add, hs, hs']⟩

/-- An injective graded linear map detects homogeneity: if the image of `x` lies in the `d`-th
piece of the target, then `x` lies in the `d`-th piece of the source. -/
public theorem mem_gradedPiece_of_injective
    {R R' S Q : Type*} [CommRing R] [CommRing R'] [AddCommGroup S] [Module R S]
    [AddCommGroup Q] [Module R' Q]
    (𝒮 : ℕ → Submodule R S) (𝒬 : ℕ → Submodule R' Q)
    [DirectSum.Decomposition 𝒮] [DirectSum.Decomposition 𝒬]
    (f : S →+ Q) (hf : ∀ (d : ℕ) (x : S), x ∈ 𝒮 d → f x ∈ 𝒬 d)
    (hinj : Function.Injective f) {d : ℕ} {x : S} (hx : f x ∈ 𝒬 d) : x ∈ 𝒮 d := by
  have hzero : ∀ i : ℕ, i ≠ d → DirectSum.decompose 𝒮 x i = 0 := by
    intro i hi
    refine Subtype.ext (hinj ?_)
    rw [← decompose_apply_gradedMap 𝒮 𝒬 f hf,
      DirectSum.decompose_of_mem_ne 𝒬 hx (Ne.symm hi)]
    simp
  have hsingle : DirectSum.decompose 𝒮 x =
      DirectSum.of (fun i ↦ ↥(𝒮 i)) d (DirectSum.decompose 𝒮 x d) := by
    refine DFinsupp.ext fun i ↦ ?_
    by_cases hi : i = d
    · subst hi
      rw [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ hi, hzero i hi]
  have hxeq : x = ((DirectSum.decompose 𝒮 x d : ↥(𝒮 d)) : S) := by
    have h := congrArg (DirectSum.decompose 𝒮).symm hsingle
    rw [Equiv.symm_apply_apply, DirectSum.decompose_symm_of] at h
    exact h
  rw [hxeq]
  exact (DirectSum.decompose 𝒮 x d).2

/-- The inverse of a graded additive equivalence sends the `d`-th piece of the target into the
`d`-th piece of the source. -/
private theorem symm_mem_gradedPiece_of_addEquiv
    {R R' S Q : Type*} [CommRing R] [CommRing R'] [AddCommGroup S] [Module R S]
    [AddCommGroup Q] [Module R' Q]
    (𝒮 : ℕ → Submodule R S) (𝒬 : ℕ → Submodule R' Q)
    [DirectSum.Decomposition 𝒮] [DirectSum.Decomposition 𝒬]
    (e : S ≃+ Q) (he : ∀ (d : ℕ) (x : S), x ∈ 𝒮 d → e x ∈ 𝒬 d) {d : ℕ} {y : Q}
    (hy : y ∈ 𝒬 d) : e.symm y ∈ 𝒮 d :=
  mem_gradedPiece_of_injective 𝒮 𝒬 e.toAddMonoidHom he e.injective (by simpa using hy)

/-- An isomorphism of the ambient category whose projection is the comparison isomorphism of the
two identifications of the images of its ends is an isomorphism of the fibre.

This is the shape in which `CategoryTheory.IsHomLift.of_fac'` is used: two objects of a fibre
have the same isomorphism class exactly when such an isomorphism exists, and an isomorphism of
the ambient category is not one of the fibre until its projection has been computed. -/
public theorem nonempty_fiber_iso_of_iso {𝒳 : Type*} [Category* 𝒳] {𝒮 : Type*} [Category* 𝒮]
    (p : 𝒳 ⥤ 𝒮) {A : 𝒮} (x y : p.Fiber A) (i : x.val ≅ y.val)
    (hhom : p.map i.hom = eqToHom (x.property.trans y.property.symm))
    (hinv : p.map i.inv = eqToHom (y.property.trans x.property.symm)) :
    Nonempty (x ≅ y) := by
  have hLift : p.IsHomLift (𝟙 A) i.hom := by
    apply IsHomLift.of_fac' p (𝟙 A) i.hom x.property y.property
    rw [hhom, Category.id_comp, ← eqToHom_trans]
  have hLift' : p.IsHomLift (𝟙 A) i.inv := by
    apply IsHomLift.of_fac' p (𝟙 A) i.inv y.property x.property
    rw [hinv, Category.id_comp, ← eqToHom_trans]
  refine ⟨{ hom := ⟨i.hom, hLift⟩, inv := ⟨i.inv, hLift'⟩, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · exact Functor.Fiber.hom_ext i.hom_inv_id
  · exact Functor.Fiber.hom_ext i.inv_hom_id

namespace ProjectiveGradedAlgebra

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The algebra map underlying the comparison of two equal base algebras is bijective. -/
private theorem bijective_eqToHom_hom {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (hb : A = B) :
    Function.Bijective (eqToHom hb).hom := by
  cases hb
  rw [eqToHom_refl, ArtinianLocalAlgCat.id_hom]
  exact Function.bijective_id

/-- The comparisons of two equal base algebras in the two directions undo each other. -/
private theorem eqToHom_hom_eqToHom_symm_hom {A B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hb : A = B) (b : B) : (eqToHom hb).hom ((eqToHom hb.symm).hom b) = b := by
  cases hb
  rfl

/-- A bijective graded ring map between graded algebras whose bases are identified by an
equality is a base-change morphism over that identification: along an isomorphism of bases, the
base-change condition is exactly bijectivity. -/
private def homOfGradedRingEquiv
    {X Y : ProjectiveGradedAlgebra.{u, v, w, m} Λ k}
    (hb : X.base = Y.base) (e : X.carrier ≃+* Y.carrier)
    (hsmul : ∀ (r : ↑X.base) (x : X.carrier), e (r • x) = (eqToHom hb).hom r • e x)
    (hmem : ∀ (d : ℕ) (x : X.carrier), x ∈ X.grading d → e x ∈ Y.grading d) : X ⟶ Y where
  base := eqToHom hb
  map := e.toRingHom
  map_smul := hsmul
  map_mem := hmem
  isBaseChange := by
    let : Algebra (↑X.base) (↑Y.base) := (eqToHom hb).hom.toAlgebra
    let : Module (↑X.base) Y.carrier := Module.compHom Y.carrier (eqToHom hb).hom.toRingHom
    let : IsScalarTower (↑X.base) (↑Y.base) Y.carrier :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    exact IsBaseChange.of_bijective_of_surjective_algebraMap
      (bijective_eqToHom_hom hb).surjective (hf := e.bijective)

/-- Two graded algebras receiving bijective graded presentations from one common source are
related by a bijective graded ring map: the composite of one presentation with the inverse of
the other.

This is how the conclusion of `bijective_of_gradedPresentation` is turned into the input of
`exists_iso_over_of_gradedRingEquiv`. -/
public theorem exists_gradedRingEquiv_of_bijective_presentations
    {X Y : ProjectiveGradedAlgebra.{u, v, w, m} Λ k} (hb : X.base = Y.base)
    {S : Type*} [CommRing S] [Module (↑X.base) S]
    (𝒮 : ℕ → Submodule (↑X.base) S) [DirectSum.Decomposition 𝒮]
    (φ : S →+* X.carrier) (ψ : S →+* Y.carrier)
    (hφsmul : ∀ (r : ↑X.base) (s : S), φ (r • s) = r • φ s)
    (hψsmul : ∀ (r : ↑X.base) (s : S), ψ (r • s) = (eqToHom hb).hom r • ψ s)
    (hφmem : ∀ (d : ℕ) (s : S), s ∈ 𝒮 d → φ s ∈ X.grading d)
    (hψmem : ∀ (d : ℕ) (s : S), s ∈ 𝒮 d → ψ s ∈ Y.grading d)
    (hφ : Function.Bijective φ) (hψ : Function.Bijective ψ) :
    ∃ e : X.carrier ≃+* Y.carrier,
      (∀ (r : ↑X.base) (x : X.carrier), e (r • x) = (eqToHom hb).hom r • e x) ∧
        (∀ (d : ℕ) (x : X.carrier), x ∈ X.grading d → e x ∈ Y.grading d) ∧
          ∀ s : S, e (φ s) = ψ s := by
  let eφ := RingEquiv.ofBijective φ hφ
  have hφe : ∀ s : S, eφ s = φ s := fun _ ↦ rfl
  have hinv : ∀ x : X.carrier, φ (eφ.symm x) = x := fun x ↦ by
    rw [← hφe, eφ.apply_symm_apply]
  have hinvsmul : ∀ (r : ↑X.base) (x : X.carrier), eφ.symm (r • x) = r • eφ.symm x := by
    intro r x
    apply eφ.injective
    rw [eφ.apply_symm_apply, hφe, hφsmul, hinv]
  refine ⟨eφ.symm.trans (RingEquiv.ofBijective ψ hψ), ?_, ?_, ?_⟩
  · intro r x
    show ψ (eφ.symm (r • x)) = (eqToHom hb).hom r • ψ (eφ.symm x)
    rw [hinvsmul, hψsmul]
  · intro d x hx
    exact hψmem d (eφ.symm x) (symm_mem_gradedPiece_of_addEquiv 𝒮 X.grading eφ.toAddEquiv hφmem hx)
  · intro s
    show ψ (eφ.symm (φ s)) = ψ s
    rw [← hφe, eφ.symm_apply_apply]

/-- Two graded algebras whose bases are identified by an equality and which are related by a
bijective graded ring map are isomorphic, by an isomorphism whose base morphism is that
identification and whose underlying map is the given one. -/
public theorem exists_iso_of_gradedRingEquiv
    {X Y : ProjectiveGradedAlgebra.{u, v, w, m} Λ k}
    (hb : X.base = Y.base) (e : X.carrier ≃+* Y.carrier)
    (hsmul : ∀ (r : ↑X.base) (x : X.carrier), e (r • x) = (eqToHom hb).hom r • e x)
    (hmem : ∀ (d : ℕ) (x : X.carrier), x ∈ X.grading d → e x ∈ Y.grading d) :
    ∃ i : X ≅ Y, i.hom.base = eqToHom hb ∧ i.inv.base = eqToHom hb.symm ∧
      (∀ x : X.carrier, i.hom.map x = e x) ∧ ∀ y : Y.carrier, i.inv.map y = e.symm y := by
  have hsmul' : ∀ (r : ↑Y.base) (y : Y.carrier),
      e.symm (r • y) = (eqToHom hb.symm).hom r • e.symm y := by
    intro r y
    apply e.injective
    rw [e.apply_symm_apply, hsmul, eqToHom_hom_eqToHom_symm_hom, e.apply_symm_apply]
  have hmem' : ∀ (d : ℕ) (y : Y.carrier), y ∈ Y.grading d → e.symm y ∈ X.grading d := by
    intro d y hy
    exact symm_mem_gradedPiece_of_addEquiv X.grading Y.grading e.toAddEquiv hmem hy
  refine ⟨{ hom := homOfGradedRingEquiv hb e hsmul hmem
            inv := homOfGradedRingEquiv hb.symm e.symm hsmul' hmem'
            hom_inv_id := ?_
            inv_hom_id := ?_ }, rfl, rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩
  · refine ProjectiveGradedAlgebra.Hom.ext ?_ ?_
    · show eqToHom hb ≫ eqToHom hb.symm = 𝟙 X.base
      rw [eqToHom_trans, eqToHom_refl]
    · refine RingHom.ext fun x ↦ ?_
      exact e.symm_apply_apply x
  · refine ProjectiveGradedAlgebra.Hom.ext ?_ ?_
    · show eqToHom hb.symm ≫ eqToHom hb = 𝟙 Y.base
      rw [eqToHom_trans, eqToHom_refl]
    · refine RingHom.ext fun y ↦ ?_
      exact e.apply_symm_apply y

variable {P : Type (max w m)} [CommRing P] [Algebra k P]
variable {grading : ℕ → Submodule k P} [GradedAlgebra grading]
variable [∀ d, Module.Finite k (grading d)]

/-- A morphism of graded algebras whose target is the special-fibre object of `P` has base
morphism the residue map of its source, because the identification of the residue field of the
special-fibre object with `k` is inverse to its residue map. -/
public theorem specialFiber_base_hom_eq_residue
    {X : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (H : X ⟶ specialFiber (Λ := Λ) P grading) (r : X.base) :
    H.base.hom r = X.base.residueEquiv (IsLocalRing.residue X.base r) :=
  (residueFieldBase_residueEquiv_residue Λ k (H.base.hom r)).symm.trans
    (H.base.residue_comm r)

/-- The base morphism of a morphism into the special-fibre object is surjective: it is the
residue map of its source followed by an isomorphism. -/
public theorem surjective_specialFiber_base_hom
    {X : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (H : X ⟶ specialFiber (Λ := Λ) P grading) :
    Function.Surjective H.base.hom := by
  intro a
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (X.base.residueEquiv.symm a)
  refine ⟨r, ?_⟩
  rw [specialFiber_base_hom_eq_residue H r, hr]
  exact X.base.residueEquiv.apply_symm_apply a

/-- The kernel of the base morphism of a morphism into the special-fibre object is the maximal
ideal: the residue map of an Artinian local algebra. -/
public theorem ker_specialFiber_base_hom
    {X : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (H : X ⟶ specialFiber (Λ := Λ) P grading) :
    RingHom.ker (H.base.hom.toRingHom) = IsLocalRing.maximalIdeal (↑X.base) := by
  ext r
  rw [RingHom.mem_ker,
    show H.base.hom.toRingHom r = X.base.residueEquiv (IsLocalRing.residue X.base r) from
      specialFiber_base_hom_eq_residue H r,
    ← IsLocalRing.residue_eq_zero_iff]
  refine ⟨fun h ↦ X.base.residueEquiv.injective ?_, fun h ↦ ?_⟩ <;> rw [h, map_zero] <;> rfl

/-- The comparison of the `d`-th graded piece of a deformation with that of the special fibre is
surjective with kernel the maximal ideal of the base times that piece: a base change along a
surjection. -/
private theorem surjective_and_ker_homPieceMap
    {X : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (H : X ⟶ specialFiber (Λ := Λ) P grading) (d : ℕ) :
    Function.Surjective (homPieceMap H d) ∧ LinearMap.ker (homPieceMap H d) =
      IsLocalRing.maximalIdeal (↑X.base) • (⊤ : Submodule (↑X.base) (X.grading d)) := by
  let Y := specialFiber (Λ := Λ) P grading
  let : CommRing (↑X.base) := X.base.commRing
  let : CommRing X.carrier := X.commRing
  let : Algebra (↑X.base) (↑Y.base) := H.base.hom.toAlgebra
  let : Algebra (↑X.base) Y.carrier :=
    ((algebraMap (↑Y.base) Y.carrier).comp H.base.hom.toRingHom).toAlgebra
  let : IsScalarTower (↑X.base) (↑Y.base) Y.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine ⟨(homPiece_isBaseChange H d).surjective_of_surjective_algebraMap
    (surjective_specialFiber_base_hom H), ?_⟩
  rw [(homPiece_isBaseChange H d).ker_eq_ker_algebraMap_smul_top
    (surjective_specialFiber_base_hom H)]
  congr 1
  exact ker_specialFiber_base_hom H

/-- The comparison of the `d`-th graded piece of a deformation with the `d`-th graded piece of
the special fibre is surjective: a base change along a surjection is surjective. -/
public theorem surjective_homPieceMap
    {X : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (H : X ⟶ specialFiber (Λ := Λ) P grading) (d : ℕ) :
    Function.Surjective (homPieceMap H d) :=
  (surjective_and_ker_homPieceMap H d).1

/-- The comparison of the `d`-th graded piece of a deformation with the `d`-th graded piece of
the special fibre has kernel the maximal ideal of the base times that piece: a module and its
reduction along a surjection differ exactly by the kernel ideal. -/
public theorem ker_homPieceMap
    {X : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (H : X ⟶ specialFiber (Λ := Λ) P grading) (d : ℕ) :
    LinearMap.ker (homPieceMap H d) =
      IsLocalRing.maximalIdeal (↑X.base) • (⊤ : Submodule (↑X.base) (X.grading d)) :=
  (surjective_and_ker_homPieceMap H d).2

/-- **Exactness of a lifted presentation.** Let `X` be a deformation of the graded algebra `P`
over an Artinian local base, with special-fibre comparison `H`, and let `φ : S → X` be a map of
graded modules over the base. If in each degree the composite `S_d → X_d → P_d` is surjective
and kills only elements of `𝔪 S_d`, then `φ` is bijective in each degree, and bijective.

This is Nakayama's lemma in both directions. Surjectivity of `φ_d` is Stacks 00DV (11) for the
nilpotent maximal ideal of the Artinian local base; injectivity is the vanishing of a kernel
contained in `𝔪 S_d`, which flatness of `X_d` — free from the projectivity of a deformation —
turns into `ker = 𝔪 · ker` and nilpotence then kills. No hypothesis beyond the two displayed
ones is needed: in particular `S` is not assumed flat, finite or projective. -/
@[sga "3 VIB 6.2.2" "special case"]
public theorem bijective_of_gradedPresentation
    {X : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (H : X ⟶ specialFiber (Λ := Λ) P grading)
    {S : Type*} [AddCommGroup S] [Module (↑X.base) S]
    (𝒮 : ℕ → Submodule (↑X.base) S) [DirectSum.Decomposition 𝒮]
    (φ : S →ₗ[↑X.base] X.carrier)
    (hmem : ∀ (d : ℕ) (s : S), s ∈ 𝒮 d → φ s ∈ X.grading d)
    (hsurj : ∀ (d : ℕ) (p : P), p ∈ grading d → ∃ s ∈ 𝒮 d, H.map (φ s) = p)
    (hker : ∀ (d : ℕ) (s : S), s ∈ 𝒮 d → H.map (φ s) = 0 →
      s ∈ IsLocalRing.maximalIdeal (↑X.base) • 𝒮 d) :
    (∀ d : ℕ, Function.Bijective fun s : 𝒮 d ↦ (⟨φ s, hmem d s.1 s.2⟩ : X.grading d)) ∧
      Function.Bijective φ := by
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal (↑X.base)) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal (↑X.base)).mp inferInstance
  have hpiece : ∀ d : ℕ,
      Function.Bijective fun s : 𝒮 d ↦ (⟨φ s, hmem d s.1 s.2⟩ : X.grading d) := by
    intro d
    let fd : (𝒮 d) →ₗ[↑X.base] (X.grading d) :=
      { toFun := fun s ↦ ⟨φ s, hmem d s.1 s.2⟩
        map_add' := fun a b ↦ Subtype.ext (map_add φ a.1 b.1)
        map_smul' := fun r a ↦ Subtype.ext (map_smul φ r a.1) }
    have hbij : Function.Bijective fd := by
      refine LinearMap.bijective_of_isNilpotent_of_comp_bijective hnil fd (homPieceMap H d)
        (ker_homPieceMap H d) ?_ ?_
      · intro y
        obtain ⟨s, hs, hsy⟩ := hsurj d y.1 y.2
        exact ⟨⟨s, hs⟩, Subtype.ext hsy⟩
      · intro x hx
        refine (Submodule.mem_smul_top_iff _ _ x).mpr (hker d x.1 x.2 ?_)
        exact congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    exact hbij
  exact ⟨hpiece, bijective_of_bijective_gradedPieces 𝒮 X.grading φ hmem hpiece⟩

/-- Two morphisms of base algebras into the base of the special-fibre object agree after
composition with a comparison of their sources: both are the residue map, and the comparison
respects residue fields. -/
public theorem eqToHom_comp_specialFiber_base
    {X Y : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (HX : X ⟶ specialFiber (Λ := Λ) P grading) (HY : Y ⟶ specialFiber (Λ := Λ) P grading)
    (hb : X.base = Y.base) : eqToHom hb ≫ HY.base = HX.base := by
  refine ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun r ↦ ?_)
  show HY.base.hom ((eqToHom hb).hom r) = HX.base.hom r
  rw [specialFiber_base_hom_eq_residue HY, specialFiber_base_hom_eq_residue HX]
  exact (eqToHom hb).residue_comm r

/-- Two deformations of `P` whose bases are identified by an equality and which are related by a
bijective graded ring map compatible with their identifications of the special fibre are
isomorphic in the deformation category, by an isomorphism whose projection to `𝒞_Λ` is that
identification of the bases.

This is the input `CategoryTheory.IsHomLift.of_fac'` needs in order to produce an isomorphism
in the fibre over the common base, which is what equality of isomorphism classes means. -/
public theorem exists_iso_over_of_gradedRingEquiv
    {X Y : deformationCategory (Λ := Λ) P grading}
    (hb : X.left.base = Y.left.base) (e : X.left.carrier ≃+* Y.left.carrier)
    (hsmul : ∀ (r : ↑X.left.base) (x : X.left.carrier), e (r • x) = (eqToHom hb).hom r • e x)
    (hmem : ∀ (d : ℕ) (x : X.left.carrier), x ∈ X.left.grading d → e x ∈ Y.left.grading d)
    (hcompat : ∀ x : X.left.carrier, Y.hom.map (e x) = X.hom.map x) :
    ∃ i : X ≅ Y,
      (objectsOverFunctor (projection.{u, w, w, max w m} (Λ := Λ) (k := k))
          (specialFiber (Λ := Λ) P grading)).map i.hom = eqToHom hb ∧
        (objectsOverFunctor (projection.{u, w, w, max w m} (Λ := Λ) (k := k))
          (specialFiber (Λ := Λ) P grading)).map i.inv = eqToHom hb.symm := by
  obtain ⟨i, hibase, hibase', himap, himap'⟩ := exists_iso_of_gradedRingEquiv hb e hsmul hmem
  have hcommF : i.hom ≫ Y.hom = X.hom := by
    refine ProjectiveGradedAlgebra.Hom.ext ?_ (RingHom.ext fun x ↦ ?_)
    · show i.hom.base ≫ Y.hom.base = X.hom.base
      rw [hibase]
      exact eqToHom_comp_specialFiber_base X.hom Y.hom hb
    · show Y.hom.map (i.hom.map x) = X.hom.map x
      rw [himap x]
      exact hcompat x
  have hcommG : i.inv ≫ X.hom = Y.hom := by
    refine ProjectiveGradedAlgebra.Hom.ext ?_ (RingHom.ext fun y ↦ ?_)
    · show i.inv.base ≫ X.hom.base = Y.hom.base
      rw [hibase']
      exact eqToHom_comp_specialFiber_base Y.hom X.hom hb.symm
    · show X.hom.map (i.inv.map y) = Y.hom.map y
      rw [himap' y]
      have h := hcompat (e.symm y)
      rw [e.apply_symm_apply] at h
      exact h.symm
  refine ⟨{ hom := Over.homMk i.hom hcommF
            inv := Over.homMk i.inv hcommG
            hom_inv_id := ?_
            inv_hom_id := ?_ }, hibase, hibase'⟩
  · ext
    exact i.hom_inv_id
  · ext
    exact i.inv_hom_id

/-- Two deformations of `P` in the fibre of the deformation category over a base `A`, related by
a bijective graded ring map compatible with their identifications of the special fibre, are
isomorphic in that fibre — hence have the same isomorphism class.

The equality of bases is a hypothesis rather than read off the two fibre memberships only
because it has to appear in the semilinearity hypothesis; proof irrelevance identifies it with
the comparison of those memberships, which is what the fibre isomorphism is built from. -/
public theorem nonempty_fiber_iso_of_gradedRingEquiv
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (X Y : (objectsOverFunctor (projection.{u, w, w, max w m} (Λ := Λ) (k := k))
      (specialFiber (Λ := Λ) P grading)).Fiber A)
    (hb : X.val.left.base = Y.val.left.base)
    (e : X.val.left.carrier ≃+* Y.val.left.carrier)
    (hsmul : ∀ (r : ↑X.val.left.base) (x : X.val.left.carrier),
      e (r • x) = (eqToHom hb).hom r • e x)
    (hmem : ∀ (d : ℕ) (x : X.val.left.carrier),
      x ∈ X.val.left.grading d → e x ∈ Y.val.left.grading d)
    (hcompat : ∀ x : X.val.left.carrier, Y.val.hom.map (e x) = X.val.hom.map x) :
    Nonempty (X ≅ Y) := by
  obtain ⟨i, hhom, hinv⟩ := exists_iso_over_of_gradedRingEquiv hb e hsmul hmem hcompat
  exact nonempty_fiber_iso_of_iso _ X Y i hhom hinv

/-- **Two deformations with a common lifted presentation are isomorphic.** Let `X` and `Y` be
deformations of `P` in the fibre of the deformation category over a base `A`, and let `S` be a
graded ring with bijective graded presentations `φ : S → X` and `ψ : S → Y` whose composites
with the two identifications of the special fibre agree. Then `X` and `Y` are isomorphic in that
fibre, so they have the same isomorphism class.

Bijectivity of `φ` and of `ψ` is what `bijective_of_gradedPresentation` supplies from the
degreewise behaviour modulo the maximal ideal; nothing else about `S` is used. -/
public theorem nonempty_fiber_iso_of_common_gradedPresentation
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (X Y : (objectsOverFunctor (projection.{u, w, w, max w m} (Λ := Λ) (k := k))
      (specialFiber (Λ := Λ) P grading)).Fiber A)
    (hb : X.val.left.base = Y.val.left.base)
    {S : Type*} [CommRing S] [Module (↑X.val.left.base) S]
    (𝒮 : ℕ → Submodule (↑X.val.left.base) S) [DirectSum.Decomposition 𝒮]
    (φ : S →+* X.val.left.carrier) (ψ : S →+* Y.val.left.carrier)
    (hφsmul : ∀ (r : ↑X.val.left.base) (s : S), φ (r • s) = r • φ s)
    (hψsmul : ∀ (r : ↑X.val.left.base) (s : S), ψ (r • s) = (eqToHom hb).hom r • ψ s)
    (hφmem : ∀ (d : ℕ) (s : S), s ∈ 𝒮 d → φ s ∈ X.val.left.grading d)
    (hψmem : ∀ (d : ℕ) (s : S), s ∈ 𝒮 d → ψ s ∈ Y.val.left.grading d)
    (hφ : Function.Bijective φ) (hψ : Function.Bijective ψ)
    (hcompat : ∀ s : S, Y.val.hom.map (ψ s) = X.val.hom.map (φ s)) :
    Nonempty (X ≅ Y) := by
  obtain ⟨e, hsmul, hmem, hφψ⟩ := exists_gradedRingEquiv_of_bijective_presentations hb 𝒮 φ ψ
    hφsmul hψsmul hφmem hψmem hφ hψ
  refine nonempty_fiber_iso_of_gradedRingEquiv X Y hb e hsmul hmem ?_
  intro x
  obtain ⟨s, rfl⟩ := hφ.surjective x
  rw [hφψ s]
  exact hcompat s

end ProjectiveGradedAlgebra

end Deformation.Examples

end
