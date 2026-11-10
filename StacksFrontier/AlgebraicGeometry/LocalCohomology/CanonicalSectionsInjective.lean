module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingLocal
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CanonicalSectionsMap
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleKernel
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent

/-!
# Injectivity of the canonical map to sections on an open complement

Let `X` be a quasi-compact scheme, let `I` be a quasi-coherent sheaf of ideals on `X` whose
first power `I • 𝒪_X` is of finite type, and let `F` be a quasi-coherent `𝒪_X`-module. The
canonical map
`colim_n Hom(I ^ n • 𝒪_X, F) ⟶ Γ(F, X \ V(I))`
of `Stacks.LocalCohomology.canonicalMapToSections` is then injective. This is the injectivity
half of Stacks tag 01PQ.

## Main results

* `Stacks.LocalCohomology.canonicalMapToSections_injective`: the canonical map is injective.
* `Stacks.LocalCohomology.exists_eventual_eq_of_canonicalMapToSections_eq`: two representatives
  with the same image already agree after a finite transition in the direct system, which is
  injectivity restated at the level of representatives.
* `Stacks.LocalCohomology.idealPowerMultiple_isQuasicoherent`: the ideal-power subsheaves of the
  structure sheaf are quasi-coherent.
* `Stacks.LocalCohomology.affineIdeal_fg`: a finite-type ideal sheaf has finitely generated
  sections on every affine chart.
* `Stacks.LocalCohomology.exists_pow_ideal_annihilates_app_on_affine`: on an affine chart a
  single power of the ideal annihilates every value of a representative that evaluates to zero
  away from the support.
* `Stacks.LocalCohomology.hom_eq_zero_of_restrict_cover`: a morphism which vanishes on each
  member of an open cover vanishes.

## Implementation notes

The argument is the one of the Stacks Project. Given two representatives with the same image,
pass to a common stage and form their difference `δ`. Its value on the unit lift over any open
disjoint from `V(I)` vanishes, so for each element `a` of the ideal on an affine chart, `δ`
becomes zero after restricting to the basic open of `a`; as that restriction is a localization
at the powers of `a`, some power of `a` annihilates each value of `δ`. Finite generation of the
ideal on the chart upgrades this to a single power `I ^ k` annihilating all values, and over an
affine chart the sections of the ideal powers are the ideal powers themselves, so composing `δ`
with the transition map `I ^ (q + k) • 𝒪_X ⟶ I ^ q • 𝒪_X` kills it on that chart. A finite
affine cover then gives vanishing globally.

Two spellings of the sections of an `𝒪_X`-module occur. `Γ(M, U)` carries the
`Γ(X, U)`-module structure that Mathlib registers, while `M.val.obj (op U)` carries the one over
the ring sheaf; the two are definitionally but not reducibly the same, so statements here use the
`Γ(M, U)` spelling and `AlgebraicGeometry.Scheme.Modules.Hom.app`, and proofs move to the
`LinearMap` spelling by positional application, where the defeq check runs at default
transparency. `Stacks.AlgebraicGeometry.QcohLimits.appₗ` packages the sections of a morphism as a
`Γ(X, U)`-linear map, which is what the algebraic input lemmas consume.

The identification of the embedded kernel of a morphism with its categorical kernel, which the
quasi-coherence of the ideal powers needs, is
`Stacks.AlgebraicGeometry.kernelSubmoduleIso`.

## References

* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.LocalCohomology

open Stacks.Ample (unitModule)

noncomputable section

/-- A zero colimit section forces every evaluation of its representative on the complement to
vanish. -/
public lemma canonicalMapToSections_zero_eval {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : X.Modules) (n : ℕ)
    (φ : (idealPowerSystem I (unitModule X)).obj (op n) ⟶ F)
    (hzero : (canonicalMapToSections I F).1
      (colimit.ι (idealPowerHom I (unitModule X) F) n φ) = 0)
    (V : X.Opens) (hV : V ≤ idealComplement I) :
    (φ.val.app (op V)).hom (complementUnitLift I n V hV) = 0 := by
  have h := (canonicalMapToSections I F).property n φ V hV
    (complementUnitLift I n V hV) (complementUnitLift_spec I n V hV)
  rw [hzero, map_zero] at h
  exact h.symm

/-- The inclusion of a smaller submodule sheaf factors the inclusion of a larger one. -/
public lemma sheafSubmodule_homOfLE_comp_ι {X : Scheme.{u}} {M : X.Modules}
    {N P : M.Submodule} (h : N ≤ P) :
    (⟨PresheafOfModules.Submodule.homOfLE h⟩ : N.toModules ⟶ P.toModules) ≫ P.ι = N.ι :=
  SheafOfModules.Hom.ext (PresheafOfModules.Submodule.homOfLE_ι h)

/-- A morphism of a functor built from a sequence by precomposition acts by precomposition with
the transition map of the underlying inverse system. -/
public lemma ofSequence_precomp_map_apply
    {C : Type*} [Category C] (S : ℕᵒᵖ ⥤ C) (Y : C)
    {n m : ℕ} (h : n ≤ m) (φ : S.obj (op n) ⟶ Y) :
    (Functor.ofSequence (X := fun r => S.obj (op r) ⟶ Y)
      (fun r => TypeCat.ofHom (fun ψ =>
        S.map (homOfLE (Nat.le_succ r)).op ≫ ψ))).map (homOfLE h) φ =
      S.map (homOfLE h).op ≫ φ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k generalizing n φ with
  | zero =>
      rw [Subsingleton.elim (homOfLE h) (𝟙 n)]
      simp only [Nat.add_zero, homOfLE_leOfHom, CategoryTheory.Functor.map_id, op_id,
        Category.id_comp]
      rfl
  | succ k ih =>
      let D := Functor.ofSequence (X := fun r => S.obj (op r) ⟶ Y)
        (fun r => TypeCat.ofHom (fun ψ => S.map (homOfLE (Nat.le_succ r)).op ≫ ψ))
      let f : n ⟶ n + k := homOfLE (by omega)
      let g : n + k ⟶ n + k + 1 := homOfLE (Nat.le_succ (n + k))
      have htotal : (homOfLE h : n ⟶ n + (k + 1)) = f ≫ g := Subsingleton.elim _ _
      have hprev := ih (n := n) (φ := φ) (by omega)
      have hstep (ψ : S.obj (op (n + k)) ⟶ Y) : D.map g ψ = S.map g.op ≫ ψ := by
        simp only [D, g, Functor.ofSequence_map_homOfLE_succ]
        rfl
      have hsplit : D.map (homOfLE h) φ = D.map g (D.map f φ) := by
        rw [htotal, Functor.map_comp]
        rfl
      rw [hsplit, hstep (D.map f φ), hprev, htotal, op_comp, Functor.map_comp,
        Category.assoc]

/-- The transition maps of the direct system of ideal-power homomorphisms act by precomposition
with the inclusions of the ideal powers. -/
public lemma idealPowerHom_map_apply {X : Scheme.{u}} (I : X.IdealSheafData)
    (G F : X.Modules) {n m : ℕ} (h : n ≤ m)
    (φ : (idealPowerSystem I G).obj (op n) ⟶ F) :
    (idealPowerHom I G F).map (homOfLE h) φ =
      (idealPowerSystem I G).map (homOfLE h).op ≫ φ :=
  ofSequence_precomp_map_apply (idealPowerSystem I G) F h φ

/-- A morphism of modules on a scheme whose restriction to each member of an open cover is zero
is zero.

The image of the morphism restricts to the image of each restriction, which is zero, so the
image is zero by `isZero_of_isZero_restrict_cover`. -/
public lemma hom_eq_zero_of_restrict_cover {X : Scheme.{u}} {M N : X.Modules}
    (g : M ⟶ N) {t : ℕ} (U : Fin t → X.Opens) (hU : iSup U = ⊤)
    (hrest : ∀ i, ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι (U i))).map g) = 0) :
    g = 0 := by
  let F := Abelian.image g
  have hrestF (i) : IsZero ((Scheme.Modules.restrictFunctor
      (Scheme.Opens.ι (U i))).obj F) := by
    let R := Scheme.Modules.restrictFunctor (Scheme.Opens.ι (U i))
    let _ : PreservesFiniteLimits R := preservesFiniteLimits_restrictFunctor _
    let _ : PreservesColimitsOfSize.{u, u} R := preservesColimitsOfSize_shrink.{u, u, u, u} R
    have hzero : IsZero (Abelian.image (R.map g)) :=
      IsZero.of_iso (isZero_zero _)
        (Abelian.imageIsoImage (R.map g) ≪≫ CategoryTheory.Limits.imageZero' (hrest i))
    exact IsZero.of_iso hzero (Abelian.PreservesImage.iso R g)
  have hι : Abelian.image.ι g = 0 :=
    (TopDegreeBaseChange.isZero_of_isZero_restrict_cover U hU F hrestF).eq_of_src _ _
  rw [← Abelian.image.fac g, hι, comp_zero]

/-- On an affine open, a representative whose values are annihilated by a power of the ideal
becomes zero after composing with the transition map into that power further along.

Over an affine open the sections of the ideal powers are the ideal powers themselves and the
transition map is the inclusion, so this is
`Stacks.LocalCohomology.linearMap_comp_inclusion_eq_zero_of_eq`. -/
public lemma transition_comp_app_eq_zero_of_annihilated {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : X.Modules) (n k : ℕ)
    (φ : (idealPowerSystem I (unitModule X)).obj (op n) ⟶ F)
    (U : X.affineOpens)
    (hkill : ∀ a ∈ I.ideal U ^ k,
      ∀ x : Γ((idealPowerSystem I (unitModule X)).obj (op n), (U : X.Opens)),
        a • (φ.app (U : X.Opens)) x = 0)
    (x : Γ((idealPowerSystem I (unitModule X)).obj (op (n + k)), (U : X.Opens))) :
    (φ.app (U : X.Opens))
      (((idealPowerSystem I (unitModule X)).map
        (homOfLE (show n ≤ n + k by omega)).op).app (U : X.Opens) x) = 0 := by
  let instF : Module Γ(X, (U : X.Opens)) ↑(F.val.obj (op (U : X.Opens))) :=
    inferInstanceAs (Module Γ(X, (U : X.Opens)) Γ(F, (U : X.Opens)))
  have hmono := Stacks.AlgebraicGeometry.mono_ι (idealPowerMultiple I n (unitModule X))
  set Pn : Submodule Γ(X, (U : X.Opens)) Γ(unitModule X, (U : X.Opens)) :=
    (idealPowerMultiple I n (unitModule X)).toSubmodule.obj (op U)
  set Pm : Submodule Γ(X, (U : X.Opens)) Γ(unitModule X, (U : X.Opens)) :=
    (idealPowerMultiple I (n + k) (unitModule X)).toSubmodule.obj (op U)
  have hn : Pn = I.ideal U ^ n := idealPowerMultiple_obj_affine I n U
  have hm : Pm = I.ideal U ^ (n + k) := idealPowerMultiple_obj_affine I (n + k) U
  have hle : Pm ≤ Pn := by
    rw [hm, hn]
    exact Ideal.pow_le_pow_right (by omega)
  have hsub : idealPowerMultiple I (n + k) (unitModule X) ≤
      idealPowerMultiple I n (unitModule X) :=
    (idealPowerMultiple_le_iff I (n + k) (unitModule X)
        (idealPowerMultiple I n (unitModule X))).2 fun V =>
      le_trans (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)))
        ((idealPowerMultiple_le_iff I n (unitModule X)
          (idealPowerMultiple I n (unitModule X))).mp le_rfl V)
  have hmor : (idealPowerSystem I (unitModule X)).map
        (homOfLE (show n ≤ n + k by omega)).op =
      (⟨PresheafOfModules.Submodule.homOfLE hsub⟩ :
        (idealPowerMultiple I (n + k) (unitModule X)).toModules ⟶
          (idealPowerMultiple I n (unitModule X)).toModules) :=
    (@cancel_mono _ _ _ _ _ _ hmono).mp
      ((idealPowerSystem_map_comp_ι I (unitModule X) n (n + k) (by omega)).trans
        (sheafSubmodule_homOfLE_comp_ι hsub).symm)
  have htrans :
      (((idealPowerSystem I (unitModule X)).map
        (homOfLE (show n ≤ n + k by omega)).op).val.app (op (U : X.Opens))).hom =
          Submodule.inclusion hle :=
    congrArg (fun t : (idealPowerMultiple I (n + k) (unitModule X)).toModules ⟶
      (idealPowerMultiple I n (unitModule X)).toModules =>
        (t.val.app (op (U : X.Opens))).hom) hmor
  have hkill' : ∀ a ∈ I.ideal U ^ k, ∀ y : Pn,
      a • (φ.val.app (op (U : X.Opens))).hom y = 0 := hkill
  have hzero := linearMap_comp_inclusion_eq_zero_of_eq
    (I.ideal U) n k Pn Pm hn hm hle (φ.val.app (op (U : X.Opens))).hom hkill'
  have happ := congrArg (fun f : Pm →ₗ[Γ(X, (U : X.Opens))] _ => f x) hzero
  have hx := congrArg (fun f : Pm →ₗ[Γ(X, (U : X.Opens))] Pn => f x) htrans
  have happ' : (φ.val.app (op (U : X.Opens))).hom (Submodule.inclusion hle x) = 0 := happ
  exact (congrArg (fun z => (φ.val.app (op (U : X.Opens))).hom z) hx).trans happ'

/-- A morphism killed by a functor isomorphic to the identity is zero. -/
public lemma functor_map_zero_of_iso_id {C : Type*} [Category C] [HasZeroMorphisms C]
    (F : C ⥤ C) (e : F ≅ 𝟭 C) {M N : C} (f : M ⟶ N) (h : F.map f = 0) : f = 0 := by
  rw [← cancel_epi (e.hom.app M), comp_zero]
  simpa [h] using (e.hom.naturality f).symm

/-- The ideal-power subsheaves of the structure sheaf are quasi-coherent.

On affine opens the sections of `I ^ n • 𝒪_X` are `I(U) ^ n`, which is also what the sections of
the kernel of `𝒪_X ⟶ (I ^ n).subschemeι_* 𝒪` are, so the two submodule sheaves agree; that
kernel is quasi-coherent because the ideal sheaf cutting out a scheme-theoretic image is. -/
public lemma idealPowerMultiple_isQuasicoherent {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) :
    ((idealPowerMultiple I n (unitModule X)).toModules).IsQuasicoherent := by
  let Iₙ := I ^ n
  let g := SheafOfModules.unitToPushforwardObjUnit Iₙ.subschemeι.toRingCatSheafHom
  have hK : (RegularIdealSheaf.kernelSubmodule g).toSheafOfModules.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (kernelSubmoduleIso g).symm inferInstance
  have hEq : idealPowerMultiple I n (unitModule X) = RegularIdealSheaf.kernelSubmodule g := by
    apply submodule_eq_of_affine_obj_eq
    intro V
    rw [idealPowerMultiple_obj_affine]
    ext x
    exact (ker_subschemeι_app_iff Iₙ V x).symm
  change ((idealPowerMultiple I n (unitModule X)).toSheafOfModules).IsQuasicoherent
  rwa [hEq]

/-- A morphism of quasi-coherent modules on an affine scheme which vanishes on global sections
is zero, because the equivalence with modules over the global sections is faithful. -/
public lemma hom_eq_zero_of_app_top {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) (h : f.val.app (op ⊤) = 0) : f = 0 := by
  let E := AlgebraicGeometry.tildeEquiv (R := R)
  let Q := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let qM : Q.FullSubcategory := ⟨M, inferInstance⟩
  let qN : Q.FullSubcategory := ⟨N, inferInstance⟩
  let qf : qM ⟶ qN := ⟨f⟩
  have hqf : E.inverse.map qf = 0 := by
    ext x
    change (f.val.app (op ⊤)).hom x = 0
    exact congrArg (fun q => q.hom x) h
  have hqf0 : qf = 0 := E.inverse.map_injective (by simpa using hqf)
  exact congrArg (fun z : qM ⟶ qN => z.hom) hqf0

/-- Sections over equal opens: a morphism vanishing on one vanishes on the other. -/
public lemma app_eq_zero_of_opens_eq {X : Scheme.{u}} {M N : X.Modules} (g : M ⟶ N)
    {V W : X.Opens} (hVW : V = W) (h : g.val.app (op V) = 0) : g.val.app (op W) = 0 :=
  hVW ▸ h

/-- An affine open is the image of the whole spectrum of its sections under `fromSpec`. -/
private theorem eq_fromSpec_image_top {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    U = hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) := by
  rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]

/-- A morphism of quasi-coherent modules whose sections over an affine open vanish restricts to
zero along the canonical morphism from the spectrum of the sections over that open.

The restriction is a morphism of quasi-coherent modules on an affine scheme whose global
sections are the sections over the given open, so `hom_eq_zero_of_app_top` applies. -/
public lemma restrict_map_eq_zero_fromSpec {X : Scheme.{u}}
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (g : M ⟶ N) {U : X.Opens} (hU : IsAffineOpen U) (h : g.val.app (op U) = 0) :
    ((Scheme.Modules.restrictFunctor hU.fromSpec).map g) = 0 := by
  have hqc (P : X.Modules) [P.IsQuasicoherent] : (P.restrict hU.fromSpec).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app P).symm
      (AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion hU.fromSpec P)
  have := hqc M
  have := hqc N
  have hImage := eq_fromSpec_image_top hU
  have htop : ((Scheme.Modules.restrictFunctor hU.fromSpec).map g).val.app (op ⊤) = 0 := by
    ext x
    change (g.val.app (op (hU.fromSpec ''ᵁ ⊤))).hom x = 0
    exact congrArg (fun q => q.hom x) (app_eq_zero_of_opens_eq g hImage h)
  exact hom_eq_zero_of_app_top ((Scheme.Modules.restrictFunctor hU.fromSpec).map g) htop

/-- A morphism of modules whose restriction along the canonical morphism from the spectrum of the
sections over an affine open vanishes already restricts to zero on that open subscheme.

Restriction along that morphism factors as restriction to the open followed by restriction along
the isomorphism of the open with the spectrum, and the latter is invertible. -/
public lemma restrict_map_eq_zero_of_affineOpen {X : Scheme.{u}}
    {M N : X.Modules} (g : M ⟶ N) {U : X.Opens} (hU : IsAffineOpen U)
    (h : ((Scheme.Modules.restrictFunctor hU.fromSpec).map g) = 0) :
    ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι U)).map g) = 0 := by
  have : IsAffine U := hU
  let e := hU.isoSpec
  let Rf := Scheme.Modules.restrictFunctor (Scheme.Opens.ι U)
  let S := Scheme.Modules.restrictFunctor e.inv
  have heq : e.inv ≫ Scheme.Opens.ι U = hU.fromSpec := rfl
  have hfrom : (Scheme.Modules.restrictFunctor (e.inv ≫ Scheme.Opens.ι U)).map g = 0 := by
    let η := Scheme.Modules.restrictFunctorCongr heq
    apply (cancel_mono (η.hom.app N)).1
    simp [η, h]
  let η := Scheme.Modules.restrictFunctorComp e.inv (Scheme.Opens.ι U)
  have hcomp : (Rf ⋙ S).map g = 0 := by
    rw [← cancel_epi (η.hom.app M), ← η.hom.naturality g, hfrom]
    simp
  let ρ := Scheme.Modules.restrictFunctor e.hom
  let ηid : (S ⋙ ρ) ≅ 𝟭 _ :=
    (Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫ Scheme.Modules.restrictFunctorId
  have hback : (S ⋙ ρ).map (Rf.map g) = 0 := by simpa using congrArg ρ.map hcomp
  exact functor_map_zero_of_iso_id (S ⋙ ρ) ηid (Rf.map g) hback

/-- If a representative evaluates to zero on every open away from the support of the ideal, then
on an affine chart every element of the ideal has a power annihilating each of its values.

The basic open of such an element is disjoint from the support, so on it the section becomes a
multiple of the unit lift and the representative kills it; quasi-coherence identifies the
sections there with a localization, so the value is annihilated by a power. -/
public lemma exists_pow_smul_eq_zero_of_canonicalMapToSections_zero {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent] (n : ℕ)
    (φ : (idealPowerSystem I (unitModule X)).obj (op n) ⟶ F)
    (heval : ∀ (V : X.Opens) (hV : V ≤ idealComplement I),
      (φ.val.app (op V)).hom (complementUnitLift I n V hV) = 0)
    (U : X.affineOpens)
    (x : Γ((idealPowerSystem I (unitModule X)).obj (op n), (U : X.Opens)))
    (a : Γ(X, (U : X.Opens))) (ha : a ∈ I.ideal U) :
    ∃ m : ℕ, a ^ m • (φ.app (U : X.Opens)) x = 0 := by
  let V : X.Opens := X.basicOpen a
  have hVU : V ≤ (U : X.Opens) := X.basicOpen_le a
  have hV : V ≤ idealComplement I := by
    intro y hy
    have hyU : y ∈ (U : X.Opens) := X.basicOpen_le a hy
    have hyS : y ∉ I.support := by
      intro hyS
      have hyZ : y ∈ X.zeroLocus (U := (U : X.Opens)) (I.ideal U) :=
        (I.mem_support_iff_of_mem hyU).mp hyS
      exact (Scheme.mem_zeroLocus_iff X (I.ideal U : Set Γ(X, (U : X.Opens))) y).mp hyZ a ha hy
    simpa [idealComplement] using hyS
  have heval' : ∀ (W : X.Opens) (hW : W ≤ idealComplement I),
      (φ.app W) (complementUnitLift I n W hW) = 0 := heval
  let g : op (U : X.Opens) ⟶ op V := (homOfLE hVU).op
  let xV : Γ((idealPowerSystem I (unitModule X)).obj (op n), V) :=
    ((idealPowerSystem I (unitModule X)).obj (op n)).presheaf.map g x
  let u : Γ((idealPowerSystem I (unitModule X)).obj (op n), V) :=
    complementUnitLift I n V hV
  let c : ↑Γ(X, V) := xV.1
  have hxV : xV = c • u := Subtype.ext (mul_one c).symm
  have hphiV : (φ.app V) xV = 0 := by
    rw [hxV, Scheme.Modules.Hom.app_smul]
    change c • (φ.app V) (complementUnitLift I n V hV) = 0
    rw [heval' V hV, smul_zero]
  let _ := moduleOfLE F hVU
  let ρ := restrictₗ F hVU
  have hρ : ρ ((φ.app (U : X.Opens)) x) = 0 := by
    change (F.presheaf.map g) ((φ.app (U : X.Opens)) x) = 0
    rwa [← QcohLimits.app_naturality φ hVU x]
  have : IsLocalizedModule.Away a ρ := isLocalizedModule_restrictₗ F U.2 a rfl hVU
  exact exists_pow_smul_eq_zero_of_localized_zero a ρ ((φ.app (U : X.Opens)) x) hρ

/-- Transporting a section over an affine open to the global sections of the spectrum of the
sections over that open and back recovers the original section. -/
public lemma presheaf_map_appIso_inv_ΓSpecIso_inv {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (hImage : U = hU.fromSpec ''ᵁ ⊤) (b : Γ(X, U)) :
    (X.presheaf.mapIso (eqToIso hImage).op).hom
      ((hU.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv b)) = b := by
  let f := hU.fromSpec
  let A := Γ(X, U)
  let eRing : Γ(X, f ''ᵁ ⊤) ≅ A := X.presheaf.mapIso (eqToIso hImage).op
  change eRing.hom ((f.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv b)) = b
  have hAEq : eRing.hom ≫ (Scheme.ΓSpecIso A).inv = (f.appIso ⊤).hom := by
    simp only [eRing, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appIso_hom']
    have hpreU : (⊤ : (Spec A).Opens) ≤ f ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
    have hAppLE : f.appLE U ⊤ hpreU = (Scheme.ΓSpecIso A).inv := by
      change f.app U ≫ (Spec A).presheaf.map (homOfLE hpreU).op = _
      rw [hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      have hmaps : (eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE hpreU).op = 𝟙 _ :=
        Subsingleton.elim _ _
      rw [hmaps]
      change (Scheme.ΓSpecIso Γ(X, U)).inv = (Scheme.ΓSpecIso A).inv
      rfl
    rw [← hAppLE]
    have hpre : (⊤ : (Spec A).Opens) ≤ f ⁻¹ᵁ (f ''ᵁ ⊤) := fun y hy => ⟨y, Opens.mem_top y, rfl⟩
    simpa only [eqToIso.hom] using
      (f.map_appLE' (U := f ''ᵁ ⊤) (U' := U) (V := (⊤ : (Spec A).Opens)) hpre hImage)
  have hAEq' : eRing.hom = (f.appIso ⊤).hom ≫ (Scheme.ΓSpecIso A).hom := by
    rw [← hAEq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hAEq']
  change (Scheme.ΓSpecIso A).hom
    ((f.appIso ⊤).hom ((f.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv b))) = b
  rw [(f.appIso ⊤).inv_hom_id_apply]
  exact (Scheme.ΓSpecIso A).inv_hom_id_apply b

/-- The global sections of the restriction of a quasi-coherent module of finite type to the
spectrum of the sections over an affine open form a finite module over those sections. -/
public lemma module_finite_restrict_fromSpec_top {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) Γ(M.restrict hU.fromSpec, ⊤) := by
  let f := hU.fromSpec
  have : ((Scheme.Modules.pullback f).obj M).IsFiniteType :=
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType f.toLRSHom.toShHom M
  have hRestr : (M.restrict f).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm
  let A := Γ(X, U)
  let P := SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf
  let qM : P.FullSubcategory := ⟨M.restrict f, by infer_instance⟩
  let E := AlgebraicGeometry.tildeEquiv (R := CommRingCat.of A)
  let m := E.inverse.obj qM
  have eCounit : (AlgebraicGeometry.tilde m) ≅ qM.obj :=
    { hom := (E.counitIso.app qM).hom.hom
      inv := (E.counitIso.app qM).inv.hom
      hom_inv_id := congrArg (fun g => g.hom) (E.counitIso.app qM).hom_inv_id
      inv_hom_id := congrArg (fun g => g.hom) (E.counitIso.app qM).inv_hom_id }
  let _ : qM.obj.IsFiniteType := hRestr
  have htilde : (AlgebraicGeometry.tilde m).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} eCounit.symm
  exact (tilde_isFiniteType_iff m).mp htilde

/-- A finite-type ideal sheaf has finitely generated sections on every affine chart.

Restricting the ideal subsheaf to the spectrum of the sections over the chart gives a
quasi-coherent module of finite type there; the equivalence with modules over that ring turns
finite type into module finiteness, and the sections over the chart are isomorphic as a module to
the global sections of the restriction. -/
public lemma affineIdeal_fg {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
    [((idealPowerMultiple I 1 (unitModule X)).toModules).IsFiniteType] :
    (I.ideal U).FG := by
  let M : X.Modules := (idealPowerMultiple I 1 (unitModule X)).toModules
  let Uo : X.Opens := U
  let hU : IsAffineOpen Uo := U.2
  let f := hU.fromSpec
  have : M.IsQuasicoherent := idealPowerMultiple_isQuasicoherent I 1
  have : Module.Finite Γ(X, Uo) Γ(M.restrict f, ⊤) := module_finite_restrict_fromSpec_top M hU
  let A := Γ(X, Uo)
  have hImage : Uo = f ''ᵁ ⊤ := eq_fromSpec_image_top hU
  let eTopAb : Γ(M.restrict f, ⊤) ≅ Γ(M, Uo) :=
    M.restrictAppIso f ⊤ ≪≫ M.presheaf.mapIso (eqToIso hImage).op
  let eTop0 : Γ(M.restrict f, ⊤) ≃+ Γ(M, Uo) := eTopAb.addCommGroupIsoToAddEquiv
  let eRing : Γ(X, f ''ᵁ ⊤) ≅ A := X.presheaf.mapIso (eqToIso hImage).op
  have hR (b : A) : eRing.hom ((f.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv b)) = b :=
    presheaf_map_appIso_inv_ΓSpecIso_inv hU hImage b
  have htop (b : A) (m' : Γ(M.restrict f, ⊤)) : eTop0 (b • m') = b • eTop0 m' := by
    change eTopAb.hom (b • m') = b • eTopAb.hom m'
    rw [Scheme.Modules.smul_Spec_def]
    have hres : (Spec A).presheaf.map (⊤ : (Spec A).Opens).leTop.op = 𝟙 _ := rfl
    rw [hres]
    simp only [CategoryTheory.id_apply]
    simp only [eTopAb, Iso.trans_hom, ConcreteCategory.comp_apply]
    rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
    simp only [Functor.mapIso_hom, Iso.op_hom] at *
    rw [M.map_smul]
    congr 1
    exact hR b
  let eTop : Γ(M.restrict f, ⊤) ≃ₗ[A] Γ(M, Uo) := { eTop0 with map_smul' := htop }
  have hsections : Module.Finite A Γ(M, Uo) :=
    Module.Finite.of_surjective eTop.toLinearMap eTop.surjective
  have hsub : ((idealPowerMultiple I 1 (unitModule X)).toSubmodule.obj (op Uo)).FG :=
    Module.Finite.iff_fg.mp hsections
  rwa [idealPowerMultiple_obj_affine I 1 U, pow_one] at hsub

/-- On an affine chart, finite generation upgrades the pointwise power torsion of a
representative to a single power of the ideal annihilating all of its values. -/
public lemma exists_pow_ideal_annihilates_app_on_affine {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    [((idealPowerMultiple I 1 (unitModule X)).toModules).IsFiniteType]
    (n : ℕ) (φ : (idealPowerSystem I (unitModule X)).obj (op n) ⟶ F)
    (heval : ∀ (V : X.Opens) (hV : V ≤ idealComplement I),
      (φ.val.app (op V)).hom (complementUnitLift I n V hV) = 0)
    (U : X.affineOpens) :
    ∃ k : ℕ, ∀ a ∈ I.ideal U ^ k,
      ∀ x : Γ((idealPowerSystem I (unitModule X)).obj (op n), (U : X.Opens)),
        a • (φ.app (U : X.Opens)) x = 0 := by
  have hI : (I.ideal U).FG := affineIdeal_fg I U
  have hN : ((idealPowerMultiple I n (unitModule X)).toSubmodule.obj (op U)).FG := by
    rw [idealPowerMultiple_obj_affine I n U]
    exact hI.pow (n := n)
  have : Module.Finite Γ(X, (U : X.Opens))
      Γ((idealPowerSystem I (unitModule X)).obj (op n), (U : X.Opens)) :=
    @Module.Finite.of_fg Γ(X, (U : X.Opens)) Γ(unitModule X, (U : X.Opens)) _ _ _ _ hN
  have hpoint : ∀ a ∈ I.ideal U,
      ∀ x : Γ((idealPowerSystem I (unitModule X)).obj (op n), (U : X.Opens)),
        ∃ m : ℕ, a ^ m • QcohLimits.appₗ φ (U : X.Opens) x = 0 := fun a ha x =>
    exists_pow_smul_eq_zero_of_canonicalMapToSections_zero I F n φ heval U x a ha
  obtain ⟨k, hk⟩ := exists_pow_le_annihilator_of_fg (I.ideal U) hI
    (⊤ : Submodule Γ(X, (U : X.Opens))
      Γ((idealPowerSystem I (unitModule X)).obj (op n), (U : X.Opens)))
    Module.Finite.fg_top (QcohLimits.appₗ φ (U : X.Opens)) (fun a ha x _ => hpoint a ha x)
  exact ⟨k, fun a ha x => hk a ha x Submodule.mem_top⟩

/-- Two stage-`q` representatives with the same image under the canonical map have a difference
that evaluates to zero on the unit lift over every open away from the support. -/
public lemma canonicalMapToSections_sub_eval {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : X.Modules) (q : ℕ)
    (φ ψ : (idealPowerSystem I (unitModule X)).obj (op q) ⟶ F)
    (hsec : (canonicalMapToSections I F).1
        (colimit.ι (idealPowerHom I (unitModule X) F) q φ) =
      (canonicalMapToSections I F).1
        (colimit.ι (idealPowerHom I (unitModule X) F) q ψ))
    (V : X.Opens) (hV : V ≤ idealComplement I) :
    ((φ - ψ).val.app (op V)).hom (complementUnitLift I q V hV) = 0 := by
  let s := complementUnitLift I q V hV
  have hφ := (canonicalMapToSections I F).property q φ V hV s
    (complementUnitLift_spec I q V hV)
  have hψ := (canonicalMapToSections I F).property q ψ V hV s
    (complementUnitLift_spec I q V hV)
  have hres := congrArg ((F.presheaf.map (homOfLE hV).op).hom) hsec
  rw [hφ, hψ] at hres
  change ((φ.val.app (op V)).hom - (ψ.val.app (op V)).hom) s = 0
  exact sub_eq_zero.mpr hres

/-- A representative evaluating to zero on the unit lift over every open away from the support
becomes zero after composing with a transition map of the direct system.

On each member of a finite affine cover a single power of the ideal annihilates its values, so
composing with the transition map past the largest of these powers kills it on each member of the
cover, hence everywhere. -/
public lemma exists_transition_comp_eq_zero_of_eval {X : Scheme.{u}}
    [CompactSpace X] (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    [((idealPowerMultiple I 1 (unitModule X)).toModules).IsFiniteType] (q : ℕ)
    (δ : (idealPowerSystem I (unitModule X)).obj (op q) ⟶ F)
    (heval : ∀ (V : X.Opens) (hV : V ≤ idealComplement I),
      (δ.val.app (op V)).hom (complementUnitLift I q V hV) = 0) :
    ∃ K : ℕ, (idealPowerSystem I (unitModule X)).map
      (homOfLE (Nat.le_add_right q K)).op ≫ δ = 0 := by
  classical
  let S := idealPowerSystem I (unitModule X)
  obtain ⟨t, Uc, hAffine, hcover⟩ := exists_fin_affineOpen_cover (X := X)
  let Ua (i : Fin t) : X.affineOpens := ⟨Uc i, hAffine i⟩
  choose ki hki using fun i : Fin t =>
    exists_pow_ideal_annihilates_app_on_affine I F q δ heval (Ua i)
  let K : ℕ := Finset.univ.sup ki
  have hkill (i : Fin t) (a : Γ(X, ((Ua i : X.affineOpens) : X.Opens)))
      (ha : a ∈ I.ideal (Ua i) ^ K) (x : Γ(S.obj (op q), ((Ua i : X.affineOpens) : X.Opens))) :
      a • (δ.app ((Ua i : X.affineOpens) : X.Opens)) x = 0 :=
    hki i a (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i)) ha) x
  let r := q + K
  let γ : q ⟶ r := homOfLE (Nat.le_add_right q K)
  let τ : S.obj (op r) ⟶ F := S.map γ.op ≫ δ
  have : (S.obj (op r)).IsQuasicoherent := idealPowerMultiple_isQuasicoherent I r
  have hτapp (i : Fin t) : τ.val.app (op (Uc i)) = 0 := by
    ext x
    exact transition_comp_app_eq_zero_of_annihilated I F q K δ (Ua i) (hkill i) x
  exact ⟨K, hom_eq_zero_of_restrict_cover τ Uc hcover fun i =>
    restrict_map_eq_zero_of_affineOpen τ (hAffine i)
      (restrict_map_eq_zero_fromSpec τ (hAffine i) (hτapp i))⟩

/-- Two representatives with the same image under the canonical map agree after a finite
transition.

Their difference evaluates to zero on every open away from the support, so by
`exists_transition_comp_eq_zero_of_eval` it vanishes after a finite transition. -/
public lemma exists_eventual_eq_of_canonicalMapToSections_eq {X : Scheme.{u}}
    [CompactSpace X] (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    [((idealPowerMultiple I 1 (unitModule X)).toModules).IsFiniteType] (n m : ℕ)
    (φ : (idealPowerSystem I (unitModule X)).obj (op n) ⟶ F)
    (ψ : (idealPowerSystem I (unitModule X)).obj (op m) ⟶ F)
    (hsec : (canonicalMapToSections I F).1
        (colimit.ι (idealPowerHom I (unitModule X) F) n φ) =
      (canonicalMapToSections I F).1
        (colimit.ι (idealPowerHom I (unitModule X) F) m ψ)) :
    ∃ r : ℕ, ∃ f : n ⟶ r, ∃ g : m ⟶ r,
      (idealPowerHom I (unitModule X) F).map f φ =
        (idealPowerHom I (unitModule X) F).map g ψ := by
  let D := idealPowerHom I (unitModule X) F
  let S := idealPowerSystem I (unitModule X)
  let q := max n m
  let α : n ⟶ q := homOfLE (Nat.le_max_left n m)
  let β : m ⟶ q := homOfLE (Nat.le_max_right n m)
  let φq : S.obj (op q) ⟶ F := D.map α φ
  let ψq : S.obj (op q) ⟶ F := D.map β ψ
  have hι {k : ℕ} (p : k ⟶ q) (χ : S.obj (op k) ⟶ F) :
      colimit.ι D q (D.map p χ) = colimit.ι D k χ := colimit.w_apply D p χ
  obtain ⟨K, hτ⟩ := exists_transition_comp_eq_zero_of_eval I F q (φq - ψq)
    (canonicalMapToSections_sub_eval I F q _ _ (by rwa [hι, hι]))
  have hγ := idealPowerHom_map_apply I (unitModule X) F (Nat.le_add_right q K)
  refine ⟨q + K, α ≫ homOfLE (Nat.le_add_right q K), β ≫ homOfLE (Nat.le_add_right q K), ?_⟩
  rw [Functor.map_comp, Functor.map_comp]
  change D.map _ φq = D.map _ ψq
  rw [hγ, hγ]
  change _ ≫ φq = _ ≫ ψq
  rw [← sub_eq_zero, ← Preadditive.comp_sub]
  exact hτ

/-- **Stacks Project, Tag 01PQ (injectivity).** The canonical map from the colimit of
homomorphisms out of the powers of a finite-type ideal sheaf on a quasi-compact scheme to the
sections of a quasi-coherent module on the complement of the support is injective. -/
@[stacks 01PQ "injectivity"]
public theorem canonicalMapToSections_injective {X : Scheme.{u}} [CompactSpace X]
    (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    [((idealPowerMultiple I 1 (unitModule X)).toModules).IsFiniteType] :
    Function.Injective (canonicalMapToSections I F).1 := by
  intro x y hxy
  let D := idealPowerHom I (unitModule X) F
  obtain ⟨n, φ, rfl⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit D) x
  obtain ⟨m, ψ, rfl⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit D) y
  exact (colimit_eq_iff (F := D)).2
    (exists_eventual_eq_of_canonicalMapToSections_eq I F n m φ ψ hxy)

end

end Stacks.LocalCohomology

end
