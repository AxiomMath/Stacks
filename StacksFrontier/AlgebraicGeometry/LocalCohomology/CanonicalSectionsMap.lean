module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact

/-!
# The canonical map from ideal-power duals to sections on an open complement

Let `X` be a scheme, let `I` be a quasi-coherent sheaf of ideals on `X` given by its
affine-local ideal data, and let `F` be an `𝒪_X`-module. Writing `U` for the open complement
of the support of `I`, a morphism `φ : I ^ n • 𝒪_X ⟶ F` has a canonical value in `Γ(F, U)`:
over `U` the subsheaf `I ^ n • 𝒪_X` contains the unit section, and one evaluates `φ` on it.
These values are compatible with the inclusions `I ^ (n + 1) • 𝒪_X ⊆ I ^ n • 𝒪_X`, so they
assemble into a map
`colim_n Hom(I ^ n • 𝒪_X, F) ⟶ Γ(F, U)`.

This file constructs that map and pins it down by its local evaluation property. It is the
map whose injectivity and surjectivity are the content of Stacks tags 01PQ and 01YB; neither
is proved here.

## Main definitions

* `Stacks.LocalCohomology.idealComplement`: the open complement `X \ V(I)` of the support of
  an ideal sheaf.
* `Stacks.LocalCohomology.idealPowerSystem`: the inverse system `n ↦ I ^ n • M` of the
  ideal-power subsheaves, with the inclusions as transition maps.
* `Stacks.LocalCohomology.idealPowerHom`: the direct system `n ↦ Hom(I ^ n • G, F)`, with
  transition maps given by precomposition with those inclusions.
* `Stacks.LocalCohomology.complementUnitLift`: the unit section of `𝒪_X` over an open disjoint
  from `V(I)`, viewed as a section of `I ^ n • 𝒪_X`.
* `Stacks.LocalCohomology.canonicalMapToSections`: the canonical map
  `colim_n Hom(I ^ n • 𝒪_X, F) → Γ(F, X \ V(I))`, bundled with the local evaluation property
  that characterises it.

## Main results

* `Stacks.LocalCohomology.idealPowerMultiple_obj_affine`: on an affine open `U` the sections of
  `I ^ n • 𝒪_X` are exactly `I(U) ^ n`.
* `Stacks.LocalCohomology.one_mem_idealPowerMultiple_of_le_complement`: away from `V(I)` the
  subsheaf `I ^ n • 𝒪_X` contains the unit section.
* `Stacks.LocalCohomology.idealPowerSystem_map_comp_ι`: the transition maps of the ideal-power
  system are compatible with the inclusions into the ambient module.
* `Stacks.LocalCohomology.exists_pow_le_annihilator_of_fg`: for a finitely generated ideal and a
  finitely generated source, pointwise power torsion of the image of a linear map is annihilation
  by a single power of the ideal. This is the algebraic engine of the injectivity argument.
* `Stacks.LocalCohomology.exists_fin_affineOpen_cover`,
  `Stacks.LocalCohomology.preservesFiniteLimits_restrictFunctor` and
  the reduction-to-a-cover ingredients the same argument needs (quasi-coherence of a pullback
  along an open immersion is
  `Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion`,
  StacksFrontier/AlgebraicGeometry/AffineBaseChange/Basic.lean:131, the one declaration of it in
  this tree).

## Implementation notes

The ideal powers are the sheaf-of-modules subobjects
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple`, and the transition maps of
`idealPowerSystem` are its inclusions
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultipleMap`. The target of the canonical map is
the module of sections over the complement of the support of Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData`.

`canonicalMapToSections` is bundled as a subtype: the map together with the statement that on
any open `V` disjoint from `V(I)` and any section `s` of `I ^ n • 𝒪_X` over `V` whose image in
`𝒪_X` is `1`, the restriction of the value to `V` is `φ(s)`. That property pins the map down
independently of the construction, so consumers should use only the property.

`AlgebraicGeometry.Scheme.Modules` is a `def` whose `Hom`, `Category`, `Abelian` and `HasLimits`
instances are separate declarations, and `AlgebraicGeometry.Scheme.ringCatSheaf` has type
`TopCat.Sheaf RingCat ↑X.toPresheafedSpace`, which is only definitionally — not reducibly —
`Sheaf (Opens.grothendieckTopology ↥X) RingCat`. Terms mixing `X.Modules` with the generic
`SheafOfModules X.ringCatSheaf` therefore fail to elaborate at the transparency instance search
and `rw` use. `AlgebraicGeometry.SheafOfModules.Submodule.toModules` and `unitModule` below are
the two transports that keep every statement in this file on one side of that wall; a
construction stated across it, such as the identification of the embedded kernel of a morphism
with its categorical kernel, does not elaborate without relaxing transparency and so is not
given here.

## References

* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace AlgebraicGeometry.SheafOfModules.Submodule

/-- A submodule of a sheaf of modules on a scheme, spelled at `X.Modules`.

`AlgebraicGeometry.Scheme.Modules` is a `def`, and its `Category`, `Abelian` and `HasLimits`
instances are re-exports stated for it, so instance search does not see through the `def` to the
generic `SheafOfModules` ones. `SheafOfModules.Submodule.toSheafOfModules` lands at the generic
spelling, so none of those instances apply to it; being an `abbrev` at `X.Modules`, this does
not have that defect. -/
public noncomputable abbrev toModules {X : Scheme.{u}} {M : X.Modules}
    (N : SheafOfModules.Submodule M) : X.Modules :=
  N.toSheafOfModules

end AlgebraicGeometry.SheafOfModules.Submodule

namespace Stacks.LocalCohomology

open Stacks.Ample (unitModule)

noncomputable section

/-! ### Algebraic preliminaries -/

/-- A finitely generated module on which every element is killed by some power of a fixed
scalar is killed by one common power of that scalar. -/
public lemma exists_pow_smul_eq_zero_of_fg_torsion
    {A P : Type*} [CommRing A] [AddCommGroup P] [Module A P]
    (N : Submodule A P) (hN : N.FG) (a : A)
    (ht : ∀ x ∈ N, ∃ n : ℕ, a ^ n • x = 0) :
    ∃ n : ℕ, ∀ x ∈ N, a ^ n • x = 0 := by
  classical
  obtain ⟨s, hs⟩ := hN
  choose k hk using fun x : s => ht x (hs ▸ Submodule.subset_span x.property)
  let q : ℕ := s.attach.sup k
  refine ⟨q, fun x hx => ?_⟩
  rw [← hs] at hx
  refine Submodule.span_induction (s := (↑s : Set P))
    (p := fun y _ => a ^ q • y = 0) ?_ ?_ ?_ ?_ hx
  · intro y hy
    let z : s := ⟨y, hy⟩
    have hle : k z ≤ q := Finset.le_sup (Finset.mem_attach _ _)
    calc
      a ^ q • y = a ^ (q - k z + k z) • y := by rw [Nat.sub_add_cancel hle]
      _ = a ^ (q - k z) • (a ^ k z • y) := by rw [pow_add, mul_smul]
      _ = 0 := by rw [hk z, smul_zero]
  · simp
  · intro x y hx hy ihx ihy
    rw [smul_add, ihx, ihy, zero_add]
  · intro c x hx ih
    rw [smul_comm, ih, smul_zero]

/-- Finite generation turns pointwise power torsion on the image of a linear map into
annihilation by a single power of the ideal. -/
public lemma exists_pow_le_annihilator_of_fg
    {A P M : Type*} [CommRing A] [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M]
    (I : Ideal A) (hI : I.FG) (N : Submodule A P) (hN : N.FG)
    (φ : P →ₗ[A] M)
    (hlocal : ∀ a ∈ I, ∀ x ∈ N, ∃ n : ℕ, a ^ n • φ x = 0) :
    ∃ k : ℕ, ∀ a ∈ I ^ k, ∀ x ∈ N, a • φ x = 0 := by
  let S : Submodule A M := N.map φ
  have hIrad : I ≤ S.annihilator.radical := by
    intro a ha
    rw [Ideal.mem_radical_iff]
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_fg_torsion S (hN.map φ) a (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
      exact hlocal a ha x hx)
    exact ⟨n, Submodule.mem_annihilator.mpr hn⟩
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIrad hI
  exact ⟨k, fun a ha x hx =>
    Submodule.mem_annihilator.mp (hk ha) _ (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)⟩

/-- If a linear map becomes zero after localization away from `a`, then every value of the
map is annihilated by some power of `a`. -/
public lemma exists_pow_smul_eq_zero_of_localized_zero
    {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (a : A) (f : M →ₗ[A] N)
    [IsLocalizedModule (Submonoid.powers a) f] (x : M) (hx : f x = 0) :
    ∃ n : ℕ, a ^ n • x = 0 := by
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers a) (f := f)).mp hx
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff s.1 a).mp s.2
  exact ⟨n, hn ▸ hs⟩

/-- A linear map out of `I ^ n` whose values are all annihilated by `I ^ k` vanishes on
`I ^ (n + k)`. -/
public lemma linearMap_comp_inclusion_pow_eq_zero
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (n k : ℕ) (f : (I ^ n : Ideal A) →ₗ[A] M)
    (hkill : ∀ a ∈ I ^ k, ∀ x, a • f x = 0) :
    f.comp (Submodule.inclusion
      (show (I ^ (n + k) : Ideal A) ≤ I ^ n from
        Ideal.pow_le_pow_right (by omega))) = 0 := by
  let N : Submodule A A := I ^ n
  let J : Submodule A A := I ^ k
  have hle : (I ^ (n + k) : Ideal A) ≤ I ^ n := Ideal.pow_le_pow_right (by omega)
  have hpow : (I ^ (n + k) : Ideal A) = J • N := by
    rw [pow_add, mul_comm, Ideal.smul_eq_mul]
  have hmap : Submodule.map N.subtype (J • (⊤ : Submodule A ↥N)) = J • N :=
    le_antisymm
      (Submodule.map_le_iff_le_comap.mpr <| Submodule.smul_le.2 fun a ha x _ =>
        Submodule.smul_mem_smul ha x.property)
      (Submodule.smul_le.2 fun a ha x hx => Submodule.mem_map.mpr
        ⟨a • (⟨x, hx⟩ : N), Submodule.smul_mem_smul ha Submodule.mem_top, rfl⟩)
  have hker : J • (⊤ : Submodule A ↥N) ≤ f.ker :=
    Submodule.smul_le.2 fun a ha x _ => by rw [LinearMap.mem_ker, map_smul, hkill a ha x]
  apply LinearMap.ext
  intro z
  apply LinearMap.mem_ker.mpr
  have hz : z.val ∈ J • N := by
    rw [← hpow]
    exact z.property
  rw [← hmap] at hz
  obtain ⟨y, hy, hzy⟩ := Submodule.mem_map.mp hz
  have heq : Submodule.inclusion hle z = y := Subtype.ext hzy.symm
  change f (Submodule.inclusion hle z) = 0
  rw [heq]
  exact hker hy

/-- The form of `linearMap_comp_inclusion_pow_eq_zero` applicable to submodules merely known to
be equal to the relevant ideal powers, which is how they arise as sections of the ideal-power
subsheaves. -/
public lemma linearMap_comp_inclusion_eq_zero_of_eq
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (n k : ℕ) (P Q : Submodule A A)
    (hP : P = I ^ n) (hQ : Q = I ^ (n + k)) (hQP : Q ≤ P)
    (f : P →ₗ[A] M)
    (hkill : ∀ a ∈ I ^ k, ∀ x : P, a • f x = 0) :
    LinearMap.comp f (Submodule.inclusion hQP) = 0 := by
  subst hP hQ
  exact linearMap_comp_inclusion_pow_eq_zero I n k f hkill

/-- An element of an ideal multiplies the whole ring into that ideal, stated for the scalar
action of the ring on itself. -/
public lemma smul_mem_of_mem_ideal {A : Type*} [CommRing A] (J : Ideal A) {a : A} (ha : a ∈ J)
    (x : A) : a • x ∈ J := by
  simpa [smul_eq_mul] using J.mul_mem_right x ha

/-- An ideal multiple of the whole module lands in any submodule absorbing the ideal. -/
public lemma smul_top_le_of_smul_mem {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (J : Ideal A) (N : Submodule A M) (h : ∀ a ∈ J, ∀ x : M, a • x ∈ N) :
    J • (⊤ : Submodule A M) ≤ N :=
  Submodule.smul_le.2 fun a ha x _ => h a ha x

/-- An ideal is contained in its own multiple of the ring, because the ring has a unit. -/
public lemma ideal_le_smul_top_self {A : Type*} [CommRing A] (J : Ideal A) :
    (J : Submodule A A) ≤ J • (⊤ : Submodule A A) := by
  intro x hx
  simpa using Submodule.smul_mem_smul (M := A) hx
    (show (1 : A) ∈ (⊤ : Submodule A A) from Submodule.mem_top)

/-! ### Generalities on sheaves of modules on a scheme -/

/-- Two submodules of a sheaf of modules on a scheme agree as soon as they agree on every
affine open, since the affine opens form a basis. -/
public alias submodule_eq_of_affine_obj_eq :=
  AlgebraicGeometry.Scheme.Modules.submodule_eq_of_obj_affineOpens_eq

/-- Alias of `Stacks.AffineTilde.preservesFiniteLimits_restrictFunctor`. -/
public alias preservesFiniteLimits_restrictFunctor :=
    Stacks.AffineTilde.preservesFiniteLimits_restrictFunctor

/-- A quasi-compact scheme has a finite cover by affine opens, indexed by a `Fin`. -/
public lemma exists_fin_affineOpen_cover {X : Scheme.{u}} [CompactSpace X] :
    ∃ t : ℕ, ∃ U : Fin t → X.Opens,
      (∀ i, IsAffineOpen (U i)) ∧ iSup U = ⊤ := by
  classical
  have htopcompact : IsCompact ((⊤ : X.Opens) : Set X) := by
    simpa using (isCompact_univ : IsCompact (Set.univ : Set X))
  obtain ⟨Us, hUs, hUsFinite, hUsSup⟩ :=
    X.isBasis_affineOpens.exists_finite_of_isCompact htopcompact
  let Us' := insert (⊥ : X.Opens) Us
  have hUs' : ∀ V ∈ Us', IsAffineOpen V := by
    rintro V (rfl | hV)
    exacts [isAffineOpen_bot X, hUs hV]
  have hsup : sSup Us' = ⊤ := by
    rw [eq_top_iff, hUsSup]
    exact sSup_le_sSup (Set.subset_insert _ _)
  let _ : Fintype Us' := (hUsFinite.insert _).fintype
  let e := Fintype.equivFin Us'
  refine ⟨Fintype.card Us', fun i => (e.symm i).val, fun i => hUs' _ (e.symm i).property,
    eq_top_iff.2 ?_⟩
  rw [← hsup, sSup_eq_iSup]
  exact iSup_le fun V => iSup_le fun hV => le_iSup_of_le (e ⟨V, hV⟩) (by simp)

/-- The transition maps of an inverse system built from a sequence of morphisms compose to the
given compatible maps into a fixed object. -/
public lemma ofOpSequence_map_comp
    {C : Type*} [Category C] (T : ℕ → C)
    (f : ∀ n, T (n + 1) ⟶ T n) (Y : C)
    (ι : ∀ n, T n ⟶ Y)
    (hι : ∀ n, f n ≫ ι n = ι (n + 1))
    (n m : ℕ) (h : n ≤ m) :
    (Functor.ofOpSequence f).map (homOfLE h).op ≫ ι n = ι m := by
  let η : Functor.ofOpSequence f ⟶ (Functor.const ℕᵒᵖ).obj Y :=
    NatTrans.ofOpSequence (fun r => ι r) (by
      intro r
      change (Functor.ofOpSequence f).map (homOfLE (Nat.le_add_right r 1)).op ≫
        ι r = ι (r + 1) ≫ 𝟙 Y
      rw [Functor.ofOpSequence_map_homOfLE_succ, Category.comp_id]
      exact hι r)
  have hn := η.naturality (homOfLE h).op
  change (Functor.ofOpSequence f).map (homOfLE h).op ≫ ι n = ι m ≫ 𝟙 Y at hn
  exact hn.trans (Category.comp_id _)

/-! ### The ideal-power systems and the open complement -/

/-- The inverse system `n ↦ I ^ n • M` of ideal-power subsheaves of `M`, with the inclusions as
transition maps. -/
public def idealPowerSystem {X : Scheme.{u}} (I : X.IdealSheafData) (M : X.Modules) :
    ℕᵒᵖ ⥤ X.Modules :=
  Functor.ofOpSequence (X := fun n => (idealPowerMultiple I n M).toModules)
    (fun n => idealPowerMultipleMap I M (Nat.le_succ n))

/-- The direct system `n ↦ Hom(I ^ n • G, F)` of homomorphisms out of the ideal-power subsheaves
of `G`, with transition maps given by precomposition with the inclusions. -/
public def idealPowerHom {X : Scheme.{u}} (I : X.IdealSheafData)
    (G F : X.Modules) : ℕ ⥤ Type u :=
  Functor.ofSequence (X := fun n => (idealPowerSystem I G).obj (op n) ⟶ F)
    (fun n => TypeCat.ofHom (fun φ : (idealPowerSystem I G).obj (op n) ⟶ F =>
      (idealPowerSystem I G).map (homOfLE (Nat.le_succ n)).op ≫ φ))

/-- The open complement `X \ V(I)` of the support of an ideal sheaf. -/
public def idealComplement {X : Scheme.{u}} (I : X.IdealSheafData) : X.Opens :=
  ⟨(I.support : Set X)ᶜ, I.support.2.isOpen_compl⟩

/-- The transition maps of `idealPowerSystem`, composed with the inclusion into `M`, give the
inclusion of the higher power into `M`. -/
public lemma idealPowerSystem_map_comp_ι {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules) (n m : ℕ) (h : n ≤ m) :
    (idealPowerSystem I M).map (homOfLE h).op ≫ (idealPowerMultiple I n M).ι =
      (idealPowerMultiple I m M).ι :=
  ofOpSequence_map_comp (fun r => (idealPowerMultiple I r M).toModules)
    (fun r => idealPowerMultipleMap I M (Nat.le_succ r)) M
    (fun r => (idealPowerMultiple I r M).ι)
    (fun r => idealPowerMultipleMap_comp_ι I M (Nat.le_succ r)) n m h

/-- A section of the structure sheaf over an affine open is killed by the map to the structure
sheaf of the closed subscheme cut out by an ideal sheaf exactly when it lies in the ideal. -/
public lemma ker_subschemeι_app_iff {X : Scheme.{u}} (J : X.IdealSheafData)
    (V : X.affineOpens) (x : Γ(X, V)) :
    (J.subschemeι.app V).hom x = 0 ↔ x ∈ J.ideal V := by
  rw [← RingHom.mem_ker, J.ker_subschemeι_app]

/-- On an affine open `U` the sections of `I ^ n • 𝒪_X` are exactly `I(U) ^ n`.

One inclusion is the universal property of `idealPowerMultiple` applied to the kernel of
`𝒪_X ⟶ (I ^ n).subschemeι_* 𝒪`, whose sections over an affine open are `I(U) ^ n` by
`ker_subschemeι_app_iff`; the other is the defining affine-local lower bound together with the
fact that the structure sheaf has a unit section. -/
public lemma idealPowerMultiple_obj_affine {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (U : X.affineOpens) :
    (idealPowerMultiple I n (unitModule X)).toSubmodule.obj (op U) = I.ideal U ^ n := by
  let Iₙ := I ^ n
  let K := Stacks.AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule
    (SheafOfModules.unitToPushforwardObjUnit Iₙ.subschemeι.toRingCatSheafHom)
  have hKobj : ∀ V : X.affineOpens, K.toSubmodule.obj (op V) = I.ideal V ^ n :=
    fun V => Submodule.ext (ker_subschemeι_app_iff Iₙ V)
  have hPK : idealPowerMultiple I n (unitModule X) ≤ K :=
    (idealPowerMultiple_le_iff I n (unitModule X) K).2 fun V => by
      rw [hKobj V]
      exact smul_top_le_of_smul_mem (I.ideal V ^ n) _
        (fun a ha x => smul_mem_of_mem_ideal (I.ideal V ^ n) ha x)
  exact le_antisymm ((hPK (op U)).trans (hKobj U).le)
    ((ideal_le_smul_top_self _).trans (le_idealPowerMultiple_obj I n (unitModule X) U))

/-- On an open disjoint from the support of `I`, the subsheaf `I ^ n • 𝒪_X` contains the unit
section. The affine opens contained in the given open cover it, on each of them `I` is the unit
ideal because its vanishing locus there is empty, and the subsheaf axiom glues. -/
public lemma one_mem_idealPowerMultiple_of_le_complement
    {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) (V : X.Opens)
    (hV : V ≤ idealComplement I) :
    (show Γ(unitModule X, V) from (1 : Γ(X, V))) ∈
      (idealPowerMultiple I n (unitModule X)).toSubmodule.obj (op V) := by
  let P := idealPowerMultiple I n (unitModule X)
  let one : Γ(unitModule X, V) := (1 : Γ(X, V))
  let R : Presieve V := fun W _ =>
    ∃ A : X.affineOpens, W = (A : X.Opens) ∧ (A : X.Opens) ≤ V
  have hcov : Sieve.generate R ∈ Opens.grothendieckTopology X V := by
    intro x hx
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
    exact ⟨A, homOfLE hAV, ⟨A, 𝟙 _, homOfLE hAV, ⟨⟨A, hA⟩, rfl, hAV⟩, by simp⟩, hxA⟩
  have hR : R ≤ P.toSubmodule.toSubfunctor.sieveOfSection one := by
    rintro W f ⟨A, rfl, hAV⟩
    have hdisj : X.zeroLocus (U := (A : X.Opens)) (I.ideal A) ∩ (A : X.Opens) = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hxZ, hxA⟩
      have hnot : x ∉ I.support := by simpa [idealComplement] using hV (hAV hxA)
      exact hnot ((I.mem_support_iff_of_mem hxA).2 hxZ)
    have himage : A.2.fromSpec '' PrimeSpectrum.zeroLocus (I.ideal A : Set Γ(X, A)) = ∅ := by
      rw [A.2.fromSpec_image_zeroLocus]
      exact hdisj
    have hIA : I.ideal A = ⊤ := by
      simpa only [SetLike.coe_sort_coe] using
        PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp (Set.image_eq_empty.mp himage)
    have h1 : (show Γ(unitModule X, A) from (1 : Γ(X, A))) ∈
        I.ideal A ^ n • (⊤ : Submodule Γ(X, A) Γ(unitModule X, A)) :=
      ideal_le_smul_top_self (I.ideal A ^ n)
        (by rw [hIA, Ideal.top_pow]; exact Submodule.mem_top)
    have hone : ((unitModule X).val.presheaf.map f.op).hom one =
        (show Γ(unitModule X, A) from (1 : Γ(X, A))) := map_one (X.presheaf.map f.op).hom
    have hmem : ((unitModule X).val.presheaf.map f.op).hom one ∈
        P.toSubmodule.obj (op (A : X.Opens)) := by
      rw [hone]
      exact le_idealPowerMultiple_obj I n (unitModule X) A h1
    exact hmem
  exact P.isSheaf one ((Opens.grothendieckTopology X).superset_covering
    ((Sieve.generate_le_iff R _).2 hR) hcov)

/-! ### The canonical map to sections on the open complement -/

/-- The unit section of `𝒪_X` over an open disjoint from `V(I)`, viewed as a section of
`I ^ n • 𝒪_X`. -/
public def complementUnitLift {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) (V : X.Opens)
    (hV : V ≤ idealComplement I) :
    ((idealPowerMultiple I n (unitModule X)).toModules).val.obj (op V) :=
  ⟨(show Γ(unitModule X, V) from (1 : Γ(X, V))),
    one_mem_idealPowerMultiple_of_le_complement I n V hV⟩

/-- The image of `complementUnitLift` in `𝒪_X` is the unit section. -/
public lemma complementUnitLift_spec {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (V : X.Opens) (hV : V ≤ idealComplement I) :
    (((idealPowerMultiple I n (unitModule X)).ι.val.app (op V)).hom
      (complementUnitLift I n V hV)) = (1 : Γ(X, V)) := by
  rfl

/-- The sections `complementUnitLift` are compatible with restriction. -/
public lemma complementUnitLift_restrict {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (V W : X.Opens)
    (hV : V ≤ idealComplement I) (hW : W ≤ idealComplement I) (hWV : W ≤ V) :
    ((((idealPowerMultiple I n (unitModule X)).toModules).val.presheaf.map
      (homOfLE hWV).op).hom (complementUnitLift I n V hV)) = complementUnitLift I n W hW :=
  Subtype.ext (map_one (X.presheaf.map (homOfLE hWV).op).hom)

/-- The canonical map `colim_n Hom(I ^ n • 𝒪_X, F) → Γ(F, X \ V(I))`, bundled with the property
that characterises it: whenever `s` is a section of `I ^ n • 𝒪_X` over an open `V` disjoint from
`V(I)` whose image in `𝒪_X` is `1`, the value of the map on the class of `φ` restricts on `V` to
`φ(s)`.

The map itself is the colimit descent of the cocone whose component at `n` evaluates a morphism
on `complementUnitLift`; the characterising property is then naturality of `φ`. Nothing
downstream should use the construction, only the property. -/
public def canonicalMapToSections {X : Scheme.{u}} (I : X.IdealSheafData) (F : X.Modules) :
    { f : colimit (idealPowerHom I (unitModule X) F) → Γ(F, idealComplement I) //
      ∀ (n : ℕ) (φ : (idealPowerSystem I (unitModule X)).obj (op n) ⟶ F)
        (V : X.Opens) (hV : V ≤ idealComplement I)
        (s : ((idealPowerSystem I (unitModule X)).obj (op n)).val.obj (op V)),
        (((idealPowerMultiple I n (unitModule X)).ι.val.app (op V)).hom s =
          (show _ from (1 : Γ(X, V)))) →
        ((F.presheaf.map (homOfLE hV).op).hom
          (f ((colimit.ι (idealPowerHom I (unitModule X) F) n) φ)) =
              (φ.val.app (op V)).hom s) } := by
  classical
  let D := idealPowerHom I (unitModule X) F
  let eval (n : ℕ) (φ : D.obj n) : Γ(F, idealComplement I) :=
    (φ.val.app (op (idealComplement I))).hom
      (complementUnitLift I n (idealComplement I) le_rfl)
  have heval (n : ℕ) (φ : D.obj n) :
      eval (n + 1) ((D.map (homOfLE (Nat.le_succ n))).hom φ) = eval n φ := by
    dsimp only [D, idealPowerHom]
    simp only [CategoryTheory.Functor.ofSequence_map_homOfLE_succ]
    dsimp [eval]
    have hLift :
        ((((idealPowerSystem I (unitModule X)).map (homOfLE (Nat.le_succ n)).op).val.app
          (op (idealComplement I))).hom
            (complementUnitLift I (n + 1) (idealComplement I) le_rfl)) =
          complementUnitLift I n (idealComplement I) le_rfl :=
      Subtype.ext <| congrArg
        (fun t : (idealPowerMultiple I (n + 1) (unitModule X)).toModules ⟶ unitModule X =>
          (t.val.app (op (idealComplement I))).hom
            (complementUnitLift I (n + 1) (idealComplement I) le_rfl))
        (idealPowerSystem_map_comp_ι I (unitModule X) n (n + 1) (Nat.le_succ n))
    change (φ.val.app (op (idealComplement I))).hom
        ((((idealPowerSystem I (unitModule X)).map
          (homOfLE (Nat.le_succ n)).op).val.app (op (idealComplement I))).hom
            (complementUnitLift I (n + 1) (idealComplement I) le_rfl)) = _
    rw [hLift]
  let c : Cocone D :=
    { pt := Γ(F, idealComplement I)
      ι := NatTrans.ofSequence (fun n => TypeCat.ofHom (eval n))
        (fun n => by ext φ; exact heval n φ) }
  refine ⟨(colimit.desc D c).hom.toFun, ?_⟩
  intro n φ V hV s hs
  change ((F.presheaf.map (homOfLE hV).op).hom
    ((colimit.ι D n ≫ colimit.desc D c).hom φ) = _)
  rw [colimit.ι_desc]
  dsimp [c, eval, D, idealPowerHom]
  let g : op (idealComplement I) ⟶ op V := (homOfLE hV).op
  have hs' :
      ((((idealPowerMultiple I n (unitModule X)).toModules).val.presheaf.map g).hom
        (complementUnitLift I n (idealComplement I) le_rfl)) = s :=
    Subtype.ext ((map_one (X.presheaf.map g).hom).trans hs.symm)
  change (F.presheaf.map g).hom ((φ.val.app (op (idealComplement I))).hom
      (complementUnitLift I n (idealComplement I) le_rfl)) = (φ.val.app (op V)).hom s
  rw [← hs']
  exact (PresheafOfModules.naturality_apply φ.val g _).symm

end

end Stacks.LocalCohomology

end
