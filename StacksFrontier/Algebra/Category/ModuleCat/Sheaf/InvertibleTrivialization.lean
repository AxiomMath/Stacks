module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Trivializing an invertible module along a nonvanishing section

Let `(X, O_X)` be a ringed space all of whose stalks `O_{X,x}` are local rings, let `L` be an
invertible sheaf of `O_X`-modules and let `s ∈ Γ(X, L)` be a global section. The nonvanishing
locus `X_s = {x | s_x ∉ 𝔪_x L_x}` is open by
`Stacks.SheafOfModules.isOpen_nonvanishingLocus`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FinitePresentationStalk.lean`). This file proves
the two remaining assertions of [Stacks, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY):

* the map `s : O_{X_s} → L|_{X_s}` is an isomorphism, and
* there is a section `s'` of the inverse of `L` over `X_s` with `⟨s, s'⟩ = 1`.

Both reduce to one piece of commutative algebra. If `Θ : M ⊗_R P ≃ R` is a pairing of
`R`-modules and `s ∈ M`, `n ∈ P` satisfy `Θ (s ⊗ n) = 1`, then `r ↦ r • s` is a bijection
`R → M` (`Stacks.SheafOfModules.bijective_toSpanSingleton`); no local-ring and no finiteness
hypothesis is needed, because `Θ.symm 1 = s ⊗ n` turns the automorphism
`Stacks.SheafOfModules.pairingAut Θ` of `M` into the map `m ↦ Θ (m ⊗ n) • s`. Specialized at a
stalk, where such an `n` exists exactly on `X_s`
(`Stacks.SheafOfModules.mem_nonvanishingLocus_iff`), this says that `s` generates `L_x` freely,
hence the stalk of `s : O_X → L` is bijective at every point of `X_s`.

## Main definitions

* `Stacks.SheafOfModules.globalGerm`: the germ at `x` of a global section of a sheaf of modules.

## Main results

* `Stacks.SheafOfModules.bijective_toSpanSingleton`: the algebraic core — a section pairing to
  `1` is a basis.
* `Stacks.SheafOfModules.tmul_left_injective`: consequently tensoring with such a section on the
  left is injective.
* `Stacks.SheafOfModules.bijective_stalkMapL_of_mem_nonvanishingLocus`: at a point of the
  nonvanishing locus the stalk of `s : O_X → L` is bijective.
* `Stacks.SheafOfModules.isIso_over_of_le_nonvanishingLocus`: `s : O_X → L` restricted to any
  open inside the nonvanishing locus is an isomorphism. The special case of the nonvanishing
  open itself — **Tag 01CY**, trivialization clause — is
  `Stacks.SheafOfModules.isIso_over_nonvanishingOpen`, in
  `StacksFrontier/AlgebraicGeometry/NonvanishingTrivialization/Basic.lean`.
* `Stacks.SheafOfModules.tensorPairing_left_injective`: over an open inside the nonvanishing
  locus a section pairing to the unit with `s` is unique; this is what makes the local inverse
  sections glue.
* `Stacks.SheafOfModules.exists_tensorPairing_eq_one`: **Tag 01CY**, inverse-section clause.

## Implementation notes

* **The inverse module is taken as data.** Stacks phrases the last clause as "there exists a
  section `s'` of `L^{⊗ -1}` over `X_s` such that `s' (s|_{X_s}) = 1`". The integer tensor
  powers of an invertible module are Tag 01CU, which is not formalized on this branch, so the
  statement here quantifies over *any* sheaf of modules `N` together with a trivialization
  `ψ : L ⊗_{O_X} N ≅ O_X` — which is exactly what invertibility supplies, by Tag 0B8K
  (`Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit`), and what Stacks' own proof
  uses `L^{⊗ -1}` for (via Tag 01CT). This is a generalization, not a weakening: once `L^{⊗ -1}`
  and the Tag 01CT isomorphism `L ⊗ L^{⊗ -1} ≅ O_X` are available, instantiating `N` at
  `L^{⊗ -1}` gives the literal Stacks statement.
* **Restriction to an open is the over-site pushforward.** `L|_{X_s}` is
  `SheafOfModules.over L X_s`, the restriction along `Over.forget X_s` of Mathlib's
  `SheafOfModules.overFunctor`; the morphism `s|_{X_s}` is `SheafOfModules.Hom.over`. On
  underlying presheaves of abelian groups this is literally reindexing, which is why
  `Stacks.SheafOfModules.over_app_eq` is `rfl` and the isomorphism statement reduces to
  bijectivity of `s` on every open contained in `X_s`.
* The reduction from stalks to sections is Mathlib's
  `TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective`, applied to the sheaf of abelian
  groups `SheafOfModules.toSheaf.obj L`; the gluing of the inverse sections is
  `TopCat.Sheaf.existsUnique_gluing'` and `TopCat.Sheaf.eq_of_locally_eq'` for the same sheaf.
  Nothing here needs the Nakayama argument of the Stacks proof, which would require `L_x` to be
  finitely generated (see the implementation notes of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleRankOne.lean`).
* Universes are those of the Stacks Tag 01CB formalization: everything is stated for
  `RingedSpace.{u, u}` and `SheafOfModules.{u}`, since the site `Opens X` forces the carrier,
  ring and module universes to agree. Nothing is specialized further.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open CategoryTheory TensorProduct Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

section LocalAlgebra

variable {R : Type u} [CommRing R] {M P : Type u}
  [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]

/-- If `s ⊗ n` pairs to `1` under `Θ`, then `Θ.symm 1 = s ⊗ n` and the automorphism
`pairingAut Θ` of `M` is the map `m ↦ Θ (m ⊗ n) • s`. -/
lemma pairingAut_apply_of_tmul_eq_one (Θ : M ⊗[R] P ≃ₗ[R] R) {s : M} {n : P}
    (h : Θ (s ⊗ₜ n) = 1) (m : M) :
    pairingAut Θ m = Θ (m ⊗ₜ n) • s := by
  have hsymm : Θ.symm 1 = s ⊗ₜ n := by rw [← h, Θ.symm_apply_apply]
  rw [pairingAut_apply, hsymm, tensorContract_apply]

/-- **The algebraic core of Tag 01CY.** If `Θ : M ⊗_R P ≃ R` and `Θ (s ⊗ n) = 1`, then `s` is a
basis of `M`: the map `r ↦ r • s` is bijective. Injectivity pairs with `n`; surjectivity is the
bijectivity of `pairingAut Θ`, which by `pairingAut_apply_of_tmul_eq_one` is `m ↦ Θ (m ⊗ n) • s`.
No local-ring or finiteness hypothesis is used. -/
theorem bijective_toSpanSingleton (Θ : M ⊗[R] P ≃ₗ[R] R) {s : M} {n : P}
    (h : Θ (s ⊗ₜ n) = 1) :
    Function.Bijective (LinearMap.toSpanSingleton R M s) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun r hr => ?_,
    fun m => ⟨Θ ((pairingAut Θ).symm m ⊗ₜ n), ?_⟩⟩
  · have key : Θ ((r • s) ⊗ₜ[R] n) = r := by
      rw [← TensorProduct.smul_tmul' r s n, map_smul, h, smul_eq_mul, mul_one]
    rw [LinearMap.toSpanSingleton_apply] at hr
    rw [← key, hr, TensorProduct.zero_tmul, map_zero]
  · rw [LinearMap.toSpanSingleton_apply, ← pairingAut_apply_of_tmul_eq_one Θ h,
      LinearEquiv.apply_symm_apply]

/-- A section pairing to `1` is a basis, so tensoring with it on the left is injective. -/
theorem tmul_left_injective (Θ : M ⊗[R] P ≃ₗ[R] R) {s : M} {n : P} (h : Θ (s ⊗ₜ n) = 1)
    (Q : Type u) [AddCommGroup Q] [Module R Q] :
    Function.Injective (fun b : Q => s ⊗ₜ[R] b) := by
  set e : R ≃ₗ[R] M := LinearEquiv.ofBijective _ (bijective_toSpanSingleton Θ h) with he
  have hes : e.symm s = 1 := by
    rw [LinearEquiv.symm_apply_eq, he]
    simp [LinearEquiv.ofBijective, LinearMap.toSpanSingleton_apply]
  have hθ : ∀ b : Q, (TensorProduct.lid R Q) (TensorProduct.map e.symm.toLinearMap
      (LinearMap.id (R := R) (M := Q)) (s ⊗ₜ[R] b)) = b := fun b => by
    simp [hes]
  intro b₁ b₂ (hb : s ⊗ₜ[R] b₁ = s ⊗ₜ[R] b₂)
  rw [← hθ b₁, ← hθ b₂, hb]

end LocalAlgebra

section Trivialization

open Stacks.SheafOfModules.TensorStalkRingedSpace

variable {X : RingedSpace.{u, u}}

/-- The germ at `x` of the global section `s`. -/
noncomputable def globalGerm (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    (s : L.sections) (x : X.carrier) : grpStalk X L.val x :=
  grpGerm X L.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤))

/-- The morphism `O_X → L` attached to a global section `s` sends the unit section to `s`.

The name says `unitSection` rather than `one` because `Stacks.SheafOfModules
.unitHomEquiv_symm_app_one` is already taken, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleLocalSummand`, by the *presheaf*-level
statement over a general site, which evaluates at `1 : O.obj W`. This one is sheaf-level over a
ringed space and evaluates at `unitSection X U`, so the two are not interchangeable and neither
subsumes the other. -/
lemma unitHomEquiv_symm_app_unitSection (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    (s : L.sections) (U : Opens X.carrier) :
    ((L.unitHomEquiv.symm s).val.app (op U)).hom (unitSection X U) = s.eval (op U) := by
  have := _root_.SheafOfModules.unitHomEquiv_apply_coe L (L.unitHomEquiv.symm s) (op U)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

/-- The stalk of the morphism `s : O_X → L` carries the germ of the unit section to the germ
of `s`. -/
lemma stalkMapL_unitGerm (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    (s : L.sections) (x : X.carrier) :
    stalkMapL X (_root_.SheafOfModules.unit (structureSheafRing X)).val L.val
        (L.unitHomEquiv.symm s).val x (unitGerm X x) = globalGerm L s x := by
  rw [globalGerm, unitGerm,
    stalkMapL_germ X (L.unitHomEquiv.symm s).val x ⊤ trivial (unitSection X ⊤),
    unitHomEquiv_symm_app_unitSection]

/-- `unitStalkLinearEquiv` is multiplication by the germ of the unit section. -/
lemma unitStalkLinearEquiv_apply (x : X.carrier) (r : ringStalk X x) :
    unitStalkLinearEquiv X x r = r • unitGerm X x := rfl

/-- Through the identification of `(O_X)_x` with the stalk of the structure sheaf viewed as a
module over itself, the stalk of `s : O_X → L` is `r ↦ r • s_x`. -/
lemma stalkMapL_unitStalkLinearEquiv
    (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    (s : L.sections) (x : X.carrier) (r : ringStalk X x) :
    stalkMapL X (_root_.SheafOfModules.unit (structureSheafRing X)).val L.val
        (L.unitHomEquiv.symm s).val x (unitStalkLinearEquiv X x r)
      = LinearMap.toSpanSingleton (ringStalk X x) (grpStalk X L.val x) (globalGerm L s x) r := by
  rw [unitStalkLinearEquiv_apply, map_smul, stalkMapL_unitGerm,
    LinearMap.toSpanSingleton_apply]

/-- The stalk map of a morphism of sheaves of modules, computed in sheaves of abelian groups,
is the `O_{X,x}`-linear stalk map of Tag 01CB. -/
lemma bijective_stalkFunctor_iff (F G : _root_.SheafOfModules.{u} (structureSheafRing X))
    (φ : F ⟶ G) (x : X.carrier) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).map φ).hom)
      ↔ Function.Bijective (stalkMapL X F.val G.val φ.val x) := Iff.rfl

/-- Restricting a morphism of sheaves of modules to an open is reindexing on the underlying
presheaves of abelian groups: its component at `U ⟶ W` is the component of the original
morphism at `U`. -/
lemma over_app_eq {F G : _root_.SheafOfModules.{u} (structureSheafRing X)} (φ : F ⟶ G)
    (W : Opens X.carrier) (U : (Over W)ᵒᵖ) :
    ((PresheafOfModules.toPresheaf ((structureSheafRing X).over W).obj).map
        ((_root_.SheafOfModules.forget ((structureSheafRing X).over W)).map
          (_root_.SheafOfModules.Hom.over φ W))).app U
      = ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).map φ).hom.app
          (op U.unop.left) := rfl

variable {L N : _root_.SheafOfModules.{u} (structureSheafRing X)}
  (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (L)).obj
      (N)) ≅ _root_.SheafOfModules.unit (structureSheafRing X))

/-- A local section pairing to the unit section with `s` pairs to `1` with the germ of `s`. -/
lemma stalkPairing_globalGerm (s : L.sections) (x : X.carrier) (W : Opens X.carrier)
    (hxW : x ∈ W) (b : N.val.obj (op W))
    (hb : tensorPairing ψ W (s.eval (op W)) b = unitSection X W) :
    stalkPairing ψ x (globalGerm L s x ⊗ₜ[ringStalk X x] grpGerm X N.val x W hxW b) = 1 := by
  rw [globalGerm, ← grpGerm_eval s x W hxW, stalkPairing_germ, hb]
  exact map_one (ringGerm X x W hxW)

/-- Restricting a section that pairs to the unit with `s` again pairs to the unit. -/
lemma tensorPairing_res_eq_one (s : L.sections) {V W : Opens X.carrier} (i : V ⟶ W)
    (b : N.val.obj (op W)) (hb : tensorPairing ψ W (s.eval (op W)) b = unitSection X W) :
    tensorPairing ψ V (s.eval (op V)) (N.val.map i.op b) = unitSection X V := by
  have e1 : L.val.map i.op (s.eval (op W)) = s.eval (op V) :=
    PresheafOfModules.sections_property s i.op
  rw [← e1, ← tensorPairing_res, hb]
  exact map_one ((structureSheafRing X).obj.map i.op).hom

variable [∀ x : X.carrier, IsLocalRing (ringStalk X x)]

include ψ in
/-- At a point of the nonvanishing locus, the stalk of the map `s : O_X → L` is bijective. -/
theorem bijective_stalkMapL_of_mem_nonvanishingLocus (s : L.sections) (x : X.carrier)
    (hx : x ∈ nonvanishingLocus L s) :
    Function.Bijective (stalkMapL X (_root_.SheafOfModules.unit (structureSheafRing X)).val L.val
      (L.unitHomEquiv.symm s).val x) := by
  obtain ⟨W, hxW, b, hb⟩ := (mem_nonvanishingLocus_iff ψ s x).mp hx
  have hcomp : (stalkMapL X (_root_.SheafOfModules.unit (structureSheafRing X)).val L.val
        (L.unitHomEquiv.symm s).val x) ∘ (unitStalkLinearEquiv X x)
      = LinearMap.toSpanSingleton (ringStalk X x) (grpStalk X L.val x) (globalGerm L s x) :=
    funext (stalkMapL_unitStalkLinearEquiv L s x)
  refine (Function.Bijective.of_comp_iff _ (unitStalkLinearEquiv X x).bijective).mp ?_
  rw [hcomp]
  exact bijective_toSpanSingleton (stalkPairing ψ x) (stalkPairing_globalGerm ψ s x W hxW b hb)

include ψ in
/-- On any open contained in the nonvanishing locus, the map `s : O_X → L` is an isomorphism. -/
theorem isIso_over_of_le_nonvanishingLocus (s : L.sections) (W : Opens X.carrier)
    (hW : ∀ x ∈ W, x ∈ nonvanishingLocus L s) :
    IsIso (_root_.SheafOfModules.Hom.over (L.unitHomEquiv.symm s) W) := by
  have key : ∀ U : (Over W)ᵒᵖ, IsIso
      (((PresheafOfModules.toPresheaf ((structureSheafRing X).over W).obj).map
        ((_root_.SheafOfModules.forget ((structureSheafRing X).over W)).map
          (_root_.SheafOfModules.Hom.over (L.unitHomEquiv.symm s) W))).app U) := by
    intro U
    rw [over_app_eq]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      (TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective
        ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).map (L.unitHomEquiv.symm s))
        U.unop.left fun x hxU => (bijective_stalkFunctor_iff _ _ _ x).mpr
          (bijective_stalkMapL_of_mem_nonvanishingLocus ψ s x (hW x (leOfHom U.unop.hom hxU))))
  have h1 : IsIso ((PresheafOfModules.toPresheaf ((structureSheafRing X).over W).obj).map
      ((_root_.SheafOfModules.forget ((structureSheafRing X).over W)).map
        (_root_.SheafOfModules.Hom.over (L.unitHomEquiv.symm s) W))) :=
    NatIso.isIso_of_isIso_app _
  have h2 : IsIso ((_root_.SheafOfModules.forget ((structureSheafRing X).over W)).map
      (_root_.SheafOfModules.Hom.over (L.unitHomEquiv.symm s) W)) :=
    isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf ((structureSheafRing X).over W).obj)
  exact isIso_of_reflects_iso _ (_root_.SheafOfModules.forget ((structureSheafRing X).over W))

include ψ in
/-- Over an open inside the nonvanishing locus, a section pairing to the unit with `s` is
unique. -/
theorem tensorPairing_left_injective (s : L.sections) (V : Opens X.carrier)
    (hV : ∀ x ∈ V, x ∈ nonvanishingLocus L s) {b₁ b₂ : N.val.obj (op V)}
    (hb : tensorPairing ψ V (s.eval (op V)) b₁ = tensorPairing ψ V (s.eval (op V)) b₂) :
    b₁ = b₂ := by
  refine TopCat.Presheaf.section_ext
    ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj N) V b₁ b₂ fun x hxV => ?_
  obtain ⟨W, hxW, n, hn⟩ := (mem_nonvanishingLocus_iff ψ s x).mp (hV x hxV)
  have hg : globalGerm L s x ⊗ₜ[ringStalk X x] grpGerm X N.val x V hxV b₁
      = globalGerm L s x ⊗ₜ[ringStalk X x] grpGerm X N.val x V hxV b₂ := by
    refine (stalkPairing ψ x).injective ?_
    rw [globalGerm, ← grpGerm_eval s x V hxV, stalkPairing_germ, stalkPairing_germ, hb]
  exact tmul_left_injective (stalkPairing ψ x) (stalkPairing_globalGerm ψ s x W hxW n hn)
    (grpStalk X N.val x) hg

include ψ in
/-- **Stacks Project, Tag 01CY** (inverse section). Let `L` be an invertible sheaf of modules on a
ringed space with local stalks, let `N` be a sheaf of modules with a trivialization
`ψ : L ⊗ N ≅ O_X`, and let `s` be a global section of `L`. Then over the nonvanishing open `X_s`
there is a section `b` of `N` with `ψ (s ⊗ b) = 1`.

Stacks states this for `N = L^{⊗ -1}`; see the implementation notes. -/
@[stacks 01CY "inverse section"]
theorem exists_tensorPairing_eq_one
    [IsInvertible X.presheaf (structureSheafRing X).property L] (s : L.sections) :
    ∃ b : N.val.obj (op (nonvanishingOpen L s)),
      tensorPairing ψ (nonvanishingOpen L s) (s.eval (op (nonvanishingOpen L s))) b
        = unitSection X (nonvanishingOpen L s) := by
  choose W hxW b hb using fun x : {y : X.carrier // y ∈ nonvanishingLocus L s} =>
    (mem_nonvanishingLocus_iff ψ s x.1).mp x.2
  have hWle : ∀ i, W i ≤ nonvanishingOpen L s := fun i y hy =>
    (mem_nonvanishingLocus_iff ψ s y).mpr ⟨W i, hy, b i, hb i⟩
  have hcover : nonvanishingOpen L s ≤ iSup W := fun y hy =>
    Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxW ⟨y, hy⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible
      ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj N).1 W b := by
    intro i j
    show N.val.map (Opens.infLELeft (W i) (W j)).op (b i)
      = N.val.map (Opens.infLERight (W i) (W j)).op (b j)
    refine tensorPairing_left_injective ψ s (W i ⊓ W j) (fun y hy => hWle i hy.1) ?_
    rw [tensorPairing_res_eq_one ψ s (Opens.infLELeft (W i) (W j)) (b i) (hb i),
      tensorPairing_res_eq_one ψ s (Opens.infLERight (W i) (W j)) (b j) (hb j)]
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj N) W
    (nonvanishingOpen L s) (fun i => homOfLE (hWle i)) hcover b hcompat
  refine ⟨g, TopCat.Sheaf.eq_of_locally_eq'
    ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj
      (_root_.SheafOfModules.unit (structureSheafRing X))) W
    (nonvanishingOpen L s) (fun i => homOfLE (hWle i)) hcover _ _ fun i => ?_⟩
  have hgi : N.val.map (homOfLE (hWle i)).op g = b i := hg i
  have e1 : L.val.map (homOfLE (hWle i)).op (s.eval (op (nonvanishingOpen L s)))
      = s.eval (op (W i)) := PresheafOfModules.sections_property s _
  have h1 : (_root_.SheafOfModules.unit (structureSheafRing X)).val.map
        (homOfLE (hWle i)).op
        (tensorPairing ψ (nonvanishingOpen L s) (s.eval (op (nonvanishingOpen L s))) g)
      = unitSection X (W i) :=
    (tensorPairing_res ψ (homOfLE (hWle i)) (s.eval (op (nonvanishingOpen L s))) g).trans
      (by rw [e1, hgi, hb i])
  exact h1.trans (map_one ((structureSheafRing X).obj.map (homOfLE (hWle i)).op).hom).symm

end Trivialization

end Stacks.SheafOfModules
