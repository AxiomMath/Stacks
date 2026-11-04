module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalSituation
public import StacksFrontier.Deformation.Artin.DeformationObjectExt
public import StacksFrontier.Deformation.Artin.FormalObject
public import StacksFrontier.Deformation.Artin.FormalObject.Versal
public import StacksFrontier.Deformation.Artin.FormalObject.OfPredeformation
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.FormalObject.VersalLifting
public import StacksFrontier.Deformation.Groupoid.BaseCategory
public import StacksFrontier.Deformation.Smooth.Versal
public import StacksFrontier.Deformation.Formal.VersalObject.MinimalPowerSeries
public import StacksFrontier.Deformation.Formal.VersalObject.MinimalUniqueness
public import StacksFrontier.RingTheory.Jacobson.Nullstellensatz
public import StacksFrontier.Deformation.Schlessinger.VersalExistence
public import StacksFrontier.Deformation.RimSchlessinger.Basic

/-!
# Versal rings at a point of an algebraic stack (Stacks 0DQV)

In the versal situation of **Stacks 0DQU** — an algebraic stack `𝒳` locally of finite type over a
locally Noetherian scheme `S` — let `x₀ : Spec k ⟶ 𝒳` be a field-valued point whose structure
morphism to `S` is of finite type. A *versal ring* to `𝒳` at `x₀` is a Noetherian complete local
`S`-algebra `A` with residue field `k` which is the base of a versal formal object of the
predeformation category of `x₀` (Artin's Axioms, **Stacks 07T4** and **Stacks 0CXJ**).

The predeformation category is built from a chosen affine open `Spec Λ ⊆ S` through which
`Spec k ⟶ S` factors. This file contains the definition and the rebasing of Artinian local
algebras along the open lift of `Spec k ⟶ S` to a second affine chart; the proof that the
notion does not depend on the chart continues in `VersalRing.RebaseDeformation`,
`VersalRing.ChartChange` and `VersalRing.ChartIndependence`.

## Main definitions

* `AlgebraicGeometry.Stack.IsVersalRingAt`: `A` is a versal ring to `𝒳` at `x₀`, presented over
  an affine open `Spec Λ ⊆ S`.

## Implementation notes

Three groups of declaration-local `attribute [local implicit_reducible]` lines replace two
file-scope transparency options: the rebasing constructions are plain `def`s producing structures
whose carrier is the carrier of the input, so a goal mentioning both spellings is not type-correct
at the `implicit` transparency level and `rw`/`simp` then fail silently. Making exactly the
constructions named in the `Application type mismatch` messages reducible, together with the
abstract lemma `eqToHom_squeeze`, removes the need for any elaboration-option override.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Stack

universe u v w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

/-- A complete Noetherian local algebra is a versal ring at a field-valued
point if it is the base of a versal formal object in the point's
predeformation category. -/
@[stacks 0DQV]
public abbrev IsVersalRingAt
    (D : AlgebraicGeometry.Stack.VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S)
    (_hiΛ : IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (_hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k) : Prop :=
  let C := Deformation.Artin.predeformationCategory iΛ
    (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀
  letI : Category C.carrier := C.category
  ∃ ξ : Deformation.FormalObject C.projection,
    ξ.base = A ∧
      Deformation.IsVersal
        (Deformation.Artin.predeformationCategory_isPredeformationCategory
          D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ

/-- The ring isomorphism induced on `(n+1)`-st adic truncations by a ring isomorphism of complete
local algebras. -/
private noncomputable def truncationRingEquiv
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (A' : Deformation.CompleteLocalAlgCat.{u, u, u} Λ' k)
    (e : A ≃+* A') (n : ℕ) :
    (A ⧸ maximalIdeal A ^ (n + 1)) ≃+*
      (A' ⧸ maximalIdeal A' ^ (n + 1)) := by
  apply Ideal.quotientEquiv (maximalIdeal A ^ (n + 1))
    (maximalIdeal A' ^ (n + 1)) e
  have he : (maximalIdeal A).map (e : A →+* A') = maximalIdeal A' :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  rw [Ideal.map_pow, he]

/-- `truncationRingEquiv` is computed on a residue class by applying the given isomorphism to a
representative. -/
private theorem truncationRingEquiv_mk
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (A' : Deformation.CompleteLocalAlgCat.{u, u, u} Λ' k)
    (e : A ≃+* A') (n : ℕ) (x : A) :
    truncationRingEquiv A A' e n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (e x) :=
  Ideal.quotientEquiv_mk _ _ _ _ _

/-- An Artinian local ring has a unique prime ideal, so its spectrum has at most one point. -/
theorem artinianPrimeSpectrum_subsingleton
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Subsingleton (PrimeSpectrum B) := by
  have hdim : Ring.KrullDimLE 0 B :=
    (isArtinianRing_iff_krullDimLE_zero (R := B)).mp inferInstance
  exact @Ring.KrullDimLE.subsingleton_primeSpectrum B _ hdim inferInstance

/-- A morphism from the spectrum of an Artinian local algebra into `T` whose unique point lands in
the range of an open immersion `i : U ⟶ T` factors through `U`. -/
noncomputable def artinianSpecLift
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    {T U : Scheme.{u}} (f : Spec (.of B) ⟶ T) (i : U ⟶ T)
    [IsOpenImmersion i] (x : PrimeSpectrum B)
    (hx : f x ∈ Set.range i) : Spec (.of B) ⟶ U :=
  IsOpenImmersion.lift i f (by
    rintro y ⟨z, rfl⟩
    have hz : z = x :=
      @Subsingleton.elim (Spec (.of B)) (artinianPrimeSpectrum_subsingleton B) z x
    rwa [hz])

/-- `artinianSpecLift` is a factorization: composing it with the open immersion recovers the
original morphism. -/
theorem artinianSpecLift_fac
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    {T U : Scheme.{u}} (f : Spec (.of B) ⟶ T) (i : U ⟶ T)
    [IsOpenImmersion i] (x : PrimeSpectrum B)
    (hx : f x ∈ Set.range i) : artinianSpecLift B f i x hx ≫ i = f :=
  IsOpenImmersion.lift_fac i f (by
    rintro y ⟨z, rfl⟩
    have hz : z = x :=
      @Subsingleton.elim (Spec (.of B)) (artinianPrimeSpectrum_subsingleton B) z x
    rwa [hz])

/-- The ring map `Λ' → B` extracted from a morphism `Spec B ⟶ S` whose image lies in the affine
open `Spec Λ' ⊆ S`. -/
noncomputable def artinianAlgebraMapOfOpenLift
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    {S : Scheme.{u}} (iΛ' : Spec (.of Λ') ⟶ S) [IsOpenImmersion iΛ']
    (f : Spec (.of B) ⟶ S) (x : PrimeSpectrum B)
    (hx : f x ∈ Set.range iΛ') : Λ' →+* B :=
  (Spec.homEquiv (artinianSpecLift B f iΛ' x hx)).hom

/-- `artinianAlgebraMapOfOpenLift` induces `artinianSpecLift` on spectra. -/
theorem specMap_artinianAlgebraMapOfOpenLift
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    {S : Scheme.{u}} (iΛ' : Spec (.of Λ') ⟶ S) [IsOpenImmersion iΛ']
    (f : Spec (.of B) ⟶ S) (x : PrimeSpectrum B)
    (hx : f x ∈ Set.range iΛ') :
    Spec.map (CommRingCat.ofHom (artinianAlgebraMapOfOpenLift B iΛ' f x hx)) =
      artinianSpecLift B f iΛ' x hx :=
  Spec.homEquiv.symm_apply_apply (artinianSpecLift B f iΛ' x hx)

/-- An Artinian local `Λ`-algebra with residue field `k`, read as an Artinian local `Λ'`-algebra
along a ring map `Λ' → B` compatible with the residue-field identification. -/
noncomputable def rebaseArtinianAlgebra
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (g : Λ' →+* B)
    (hg : ∀ a : Λ', B.residueEquiv (residue B (g a)) = algebraMap Λ' k a) :
    Deformation.ArtinianLocalAlgCat.{u, u, u} Λ' k := by
  letI : Algebra Λ' B := g.toAlgebra
  exact
    { carrier := B
      commRing := B.commRing
      algebra := inferInstance
      isArtinianRing := B.isArtinianRing
      isLocalRing := B.isLocalRing
      residueEquiv := AlgEquiv.ofRingEquiv (f := B.residueEquiv.toRingEquiv) (fun a => by
        change B.residueEquiv (residue B (g a)) = algebraMap Λ' k a
        exact hg a) }

/-- `rebaseArtinianAlgebra` depends only on the ring map, not on the chosen compatibility proof. -/
theorem rebaseArtinianAlgebra_congr
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (g h : Λ' →+* B)
    (hg : ∀ a : Λ', B.residueEquiv (residue B (g a)) = algebraMap Λ' k a)
    (hh : ∀ a : Λ', B.residueEquiv (residue B (h a)) = algebraMap Λ' k a)
    (e : g = h) : rebaseArtinianAlgebra B g hg = rebaseArtinianAlgebra B h hh := by
  cases e
  have hp : hg = hh := Subsingleton.elim _ _
  cases hp
  rfl

/-- A complete local `Λ`-algebra with residue field `k`, read as a complete local `Λ'`-algebra
along a ring map `Λ' → A` compatible with the residue-field identification. -/
noncomputable def rebaseCompleteLocalAlgebra
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (g : Λ' →+* A)
    (hg : ∀ a : Λ', A.residueEquiv (residue A (g a)) = algebraMap Λ' k a) :
    Deformation.CompleteLocalAlgCat.{u, u, u} Λ' k := by
  letI : Algebra Λ' A := g.toAlgebra
  exact
    { carrier := A
      commRing := A.commRing
      algebra := inferInstance
      completeLocal := A.completeLocal
      residueEquiv := AlgEquiv.ofRingEquiv (f := A.residueEquiv.toRingEquiv) (fun a => by
        change A.residueEquiv (residue A (g a)) = algebraMap Λ' k a
        exact hg a) }

/-- Rebasing commutes with adic truncation: the `n`-th truncation of a rebased complete local
algebra is the rebase of its `n`-th truncation. -/
theorem rebaseArtinianAlgebra_truncation
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (g : Λ' →+* A)
    (hg : ∀ a : Λ', A.residueEquiv (residue A (g a)) = algebraMap Λ' k a)
    (n : ℕ) :
    rebaseArtinianAlgebra (Deformation.AdicTruncation.obj A n)
        (show Λ' →+* Deformation.AdicTruncation.obj A n from
          (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal A n)).comp g) (by
          intro a
          let I := Deformation.AdicTruncation.ideal A n
          let : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
            ((Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt
              (maximalIdeal.isMaximal A).lt_top).ne
          let : IsLocalRing (A ⧸ I) :=
            IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
          change Deformation.AdicTruncation.residueEquiv A n
            (residue (A ⧸ I) (Ideal.Quotient.mk I (g a))) = _
          exact (Deformation.AdicTruncation.residueEquiv_residue_mk A n (g a)).trans
            (hg a)) =
      Deformation.AdicTruncation.obj (rebaseCompleteLocalAlgebra A g hg) n := by
  unfold rebaseArtinianAlgebra rebaseCompleteLocalAlgebra
  rfl

/-- Ring maps with equal maps on spectra are equal. -/
private theorem ringHom_eq_of_specMap_eq {R T : Type u} [CommRing R] [CommRing T]
    {f g : R →+* T} (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) :
    f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/-- The inverse of a ring isomorphism over `S` is again over `S`. -/
private theorem specMap_symm_comp_eq
    {Λ Λ' A A' : Type u} [CommRing Λ] [CommRing Λ'] [CommRing A] [CommRing A'] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S) [Algebra Λ A] [Algebra Λ' A']
    (e : A ≃+* A')
    (heS : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' A')) ≫ iΛ') :
    Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ' A')) ≫ iΛ' =
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ := by
  rw [← heS, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  simp

/-- From a ring isomorphism `A ≃+* A'` over `S` compatible with the residue fields, a ring map
`Λ' → A` exhibiting `A` as a `Λ'`-algebra over `S`. -/
private theorem completeLocalRebaseData
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (A' : Deformation.CompleteLocalAlgCat.{u, u, u} Λ' k)
    (e : A ≃+* A')
    (heS : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' A')) ≫ iΛ')
    (hek : ∀ a : A,
      A'.residueEquiv (residue A' (e a)) = A.residueEquiv (residue A a)) :
    ∃ (g : Λ' →+* A),
      (∀ a, A.residueEquiv (residue A (g a)) = algebraMap Λ' k a) ∧
      Spec.map (CommRingCat.ofHom g) ≫ iΛ' =
        Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ := by
  let g : Λ' →+* A := e.symm.toRingHom.comp (algebraMap Λ' A')
  refine ⟨g, ?_, ?_⟩
  · intro a
    rw [← hek (g a)]
    have hega : e (g a) = algebraMap Λ' A' a := by
      dsimp [g]
      exact e.apply_symm_apply _
    rw [hega]
    rw [← ResidueField.algebraMap_eq]
    exact A'.residueEquiv.commutes a
  · have heS' := specMap_symm_comp_eq iΛ iΛ' e heS
    change Spec.map (CommRingCat.ofHom
      (e.symm.toRingHom.comp (algebraMap Λ' A'))) ≫ iΛ' = _
    rwa [CommRingCat.ofHom_comp, Spec.map_comp]

/-- A ring isomorphism of complete local algebras respecting the structure maps and the
residue-field identifications is an isomorphism in `CompleteLocalAlgCat`. -/
noncomputable def completeLocalAlgIsoOfRingEquiv
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A B : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (e : A ≃+* B)
    (halg : ∀ a : Λ, e (algebraMap Λ A a) = algebraMap Λ B a)
    (hres : ∀ a : A,
      B.residueEquiv (residue B (e a)) = A.residueEquiv (residue A a)) : A ≅ B := by
  let forward : A ⟶ B := {
    hom := AlgHom.mk e.toRingHom halg
    isLocal := ⟨fun a ha => (MulEquiv.isUnit_map e).mp ha⟩
    residue_comm := hres }
  let backward : B ⟶ A := {
    hom := AlgHom.mk e.symm.toRingHom (fun a => by
      change e.symm (algebraMap Λ B a) = algebraMap Λ A a
      rw [← halg a]
      exact e.symm_apply_apply _)
    isLocal := ⟨fun a ha => (MulEquiv.isUnit_map e.symm).mp ha⟩
    residue_comm := by
      intro b
      calc
        _ = B.residueEquiv (residue B (e (e.symm b))) := (hres (e.symm b)).symm
        _ = _ := by rw [e.apply_symm_apply] }
  exact {
    hom := forward
    inv := backward
    hom_inv_id := by
      apply Deformation.CompleteLocalAlgCat.Hom.ext
      apply AlgHom.ext
      intro a
      simp [forward, backward]
    inv_hom_id := by
      apply Deformation.CompleteLocalAlgCat.Hom.ext
      apply AlgHom.ext
      intro a
      simp [forward, backward] }

/-- The rebase of `A` along the map produced by `completeLocalRebaseData` is isomorphic to `A'`. -/
private noncomputable def completeLocalRebaseIso
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (A' : Deformation.CompleteLocalAlgCat.{u, u, u} Λ' k)
    (e : A ≃+* A')
    (heS : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' A')) ≫ iΛ')
    (hek : ∀ a : A,
      A'.residueEquiv (residue A' (e a)) = A.residueEquiv (residue A a)) :
    rebaseCompleteLocalAlgebra A
        (Classical.choose (completeLocalRebaseData iΛ iΛ' A A' e heS hek))
        (Classical.choose_spec (completeLocalRebaseData iΛ iΛ' A A' e heS hek)).1 ≅ A' := by
  let hdata := completeLocalRebaseData iΛ iΛ' A A' e heS hek
  let g := Classical.choose hdata
  let hg := (Classical.choose_spec hdata).1
  let g₀ : Λ' →+* A := e.symm.toRingHom.comp (algebraMap Λ' A')
  change rebaseCompleteLocalAlgebra A g hg ≅ A'
  have heS₀ := specMap_symm_comp_eq iΛ iΛ' e heS
  have hg₀ : Spec.map (CommRingCat.ofHom g₀) =
      Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ' A')) := by
    rw [CommRingCat.ofHom_comp, ← Spec.map_comp]
  have hspec : Spec.map (CommRingCat.ofHom g) = Spec.map (CommRingCat.ofHom g₀) := by
    apply (cancel_mono iΛ').1
    calc
      Spec.map (CommRingCat.ofHom g) ≫ iΛ' =
          Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ :=
        (Classical.choose_spec hdata).2
      _ = (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ' A'))) ≫ iΛ' :=
        heS₀.symm
      _ = Spec.map (CommRingCat.ofHom g₀) ≫ iΛ' := by rw [← hg₀]
  have hring : g = g₀ := ringHom_eq_of_specMap_eq hspec
  apply completeLocalAlgIsoOfRingEquiv
  · intro a
    change e (g a) = algebraMap Λ' A' a
    rw [hring]
    exact e.apply_symm_apply _
  · exact hek

/-- The ring map produced by `artinianAlgebraMapOfOpenLift` is compatible with the residue-field
identification. -/
theorem artinianAlgebraMapOfOpenLift_residue
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    {S : Scheme.{u}} (iΛ' : Spec (.of Λ') ⟶ S) [IsOpenImmersion iΛ']
    (f : Spec (.of B) ⟶ S) (x : PrimeSpectrum B)
    (hx : f x ∈ Set.range iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap B)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') :
    ∀ a : Λ', B.residueEquiv
      (residue B (artinianAlgebraMapOfOpenLift B iΛ' f x hx a)) = algebraMap Λ' k a := by
  let lift := artinianSpecLift B f iΛ' x hx
  have hclosed' : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap B)) ≫ lift =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) := by
    apply (cancel_mono iΛ').1
    rwa [Category.assoc, artinianSpecLift_fac]
  have hring : (Deformation.Artin.residueMap B).comp
      (artinianAlgebraMapOfOpenLift B iΛ' f x hx) = algebraMap Λ' k :=
    ringHom_eq_of_specMap_eq (by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, specMap_artinianAlgebraMapOfOpenLift]
      exact hclosed')
  intro a
  have hpoint := congrArg (fun g : Λ' →+* k => g a) hring
  simpa [Deformation.Artin.residueMap] using hpoint

/-- `artinianAlgebraMapOfOpenLift` is natural in the Artinian local algebra. -/
theorem artinianAlgebraMapOfOpenLift_natural
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    {B C : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    {S : Scheme.{u}} (iΛ' : Spec (.of Λ') ⟶ S) [IsOpenImmersion iΛ']
    (fB : Spec (.of B) ⟶ S) (xB : PrimeSpectrum B)
    (hxB : fB xB ∈ Set.range iΛ')
    (fC : Spec (.of C) ⟶ S) (xC : PrimeSpectrum C)
    (hxC : fC xC ∈ Set.range iΛ') (g : B ⟶ C)
    (hbase : Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫ fB = fC) :
    CommRingCat.ofHom
        ((g.hom.toRingHom).comp (artinianAlgebraMapOfOpenLift B iΛ' fB xB hxB)) =
      CommRingCat.ofHom (artinianAlgebraMapOfOpenLift C iΛ' fC xC hxC) := by
  have hlift : Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫
      artinianSpecLift B fB iΛ' xB hxB = artinianSpecLift C fC iΛ' xC hxC := by
    apply (cancel_mono iΛ').1
    rw [Category.assoc, artinianSpecLift_fac, hbase, artinianSpecLift_fac]
  congr 1
  exact ringHom_eq_of_specMap_eq (by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, specMap_artinianAlgebraMapOfOpenLift,
      specMap_artinianAlgebraMapOfOpenLift]
    exact hlift)

/-- The residue map of an Artinian local `Λ`-algebra composed with its structure map is the
structure morphism of `k`. -/
theorem specMap_residueMap_comp_base
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap B)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ B)) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  change B.residueEquiv (residue B (algebraMap Λ B a)) = algebraMap Λ k a
  rw [← ResidueField.algebraMap_eq]
  exact B.residueEquiv.commutes a

/-- An arrow `g` of `X` between objects lying over `f` and `f'` induces a morphism over `S`. -/
private theorem eqToHom_comp_map_left_comp_eq
    {X : Type w} [Category X] {S : Scheme.{u}} (q : X ⥤ Over S) {p p' : X} (g : p ⟶ p')
    {Y Y' : Scheme.{u}} {f : Y ⟶ S} {f' : Y' ⟶ S} (h : q.obj p = Over.mk f)
    (h' : q.obj p' = Over.mk f') :
    (eqToHom (congrArg Over.left h).symm ≫ (q.map g).left ≫ eqToHom (congrArg Over.left h')) ≫
      f' = f := by
  have hu : eqToHom (congrArg Over.left h).symm ≫ (q.obj p).hom = f := by
    simpa [Over.eqToHom_left] using Over.w (eqToHom h.symm)
  have hv : eqToHom (congrArg Over.left h') ≫ f' = (q.obj p').hom := by
    simpa [Over.eqToHom_left] using Over.w (eqToHom h')
  rw [Category.assoc, Category.assoc, hv, Over.w, hu]

/-- The closed point of a deformation object maps to the chosen field-valued point of `S`. -/
theorem deformationObject_closedMap
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type w} [Category X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (O : Deformation.Artin.DeformationObject iΛ q x₀ hx₀) :
    Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap O.algebra)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ O.algebra)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ := by
  rw [← O.arrow_base]
  exact eqToHom_comp_map_left_comp_eq q O.arrow hx₀ O.base

/-- A morphism of deformation objects commutes with the structure maps to `S`. -/
theorem deformationMorphism_baseMap
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type w} [Category X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    {a b : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (m : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b) :
    Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ a.algebra)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ b.algebra)) ≫ iΛ := by
  rw [← m.arrow_base]
  exact eqToHom_comp_map_left_comp_eq q m.arrow b.base a.base

/-- Two affine-open presentations of the same field-valued point of `S` induce the same morphism
`Spec k ⟶ S`. -/
theorem closedPointCharts_eq
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    {X : Type w} [Category X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')) :
    Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ' := by
  have h := hx₀.symm.trans hx₀'
  have hw := Over.w (eqToHom h)
  have hl : (eqToHom h).left = 𝟙 (Spec (.of k)) := by
    simp [Over.eqToHom_left]
  change (eqToHom h).left ≫
    (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') =
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ at hw
  rw [hl] at hw
  calc
    _ = 𝟙 (Spec (.of k)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') := hw.symm
    _ = _ := by simp

/-- The canonical ring map `Λ' → B` attached to an Artinian local `Λ`-algebra `B` whose structure
morphism to `S` factors through the affine open `Spec Λ'`. -/
noncomputable def canonicalArtinianOpenLift
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) : Λ' →+* B := by
  letI : IsOpenImmersion iΛ' := hiΛ'
  let f : Spec (.of B) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ
  let xk : PrimeSpectrum k := ⟨⊥, inferInstance⟩
  let x : PrimeSpectrum B :=
    (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap B))).base xk
  have hfactor : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap B)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ' := by
    calc
      _ = (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap B)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ B))) ≫ iΛ := by
        simp [f, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ := by
        rw [specMap_residueMap_comp_base B]
      _ = _ := hclosed
  have hx : f x ∈ Set.range iΛ' := by
    refine ⟨(Spec.map (CommRingCat.ofHom (algebraMap Λ' k))).base xk, ?_⟩
    have hp := congrArg (fun g : Spec (.of k) ⟶ S => g.base xk) hfactor
    change iΛ'.base ((Spec.map (CommRingCat.ofHom (algebraMap Λ' k))).base xk) =
      iΛ.base ((Spec.map (CommRingCat.ofHom (algebraMap Λ B))).base
        ((Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap B))).base xk))
    exact hp.symm
  exact artinianAlgebraMapOfOpenLift B iΛ' f x hx

/-- The closed point of `Spec B` maps into `Spec Λ'` compatibly with the chosen field point. -/
private theorem residueMap_comp_eq_of_closedCharts
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap B)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ' := by
  rw [← Category.assoc, specMap_residueMap_comp_base B, hclosed]

/-- The image of the closed point of `Spec B` lies in the affine open `Spec Λ'`. -/
private theorem closedPoint_mem_range
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    (Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ)
      ((Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap B))).base
        ⟨⊥, inferInstance⟩) ∈ Set.range iΛ' := by
  refine ⟨(Spec.map (CommRingCat.ofHom (algebraMap Λ' k))).base ⟨⊥, inferInstance⟩, ?_⟩
  exact (congrArg (fun g : Spec (.of k) ⟶ S => g.base ⟨⊥, inferInstance⟩)
    (residueMap_comp_eq_of_closedCharts iΛ iΛ' hclosed B)).symm

/-- `canonicalArtinianOpenLift` factors the structure morphism of `B` through `Spec Λ' ⟶ S`. -/
theorem canonicalArtinianOpenLift_fac
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Spec.map (CommRingCat.ofHom
      (canonicalArtinianOpenLift iΛ iΛ' hiΛ' hclosed B)) ≫ iΛ' =
      Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ := by
  let : IsOpenImmersion iΛ' := hiΛ'
  exact (congrArg (· ≫ iΛ') (specMap_artinianAlgebraMapOfOpenLift B iΛ' _ _
    (closedPoint_mem_range iΛ iΛ' hclosed B))).trans (artinianSpecLift_fac B _ iΛ' _ _)

/-- The unique point of `Spec B` maps into the affine open `Spec Λ'`. -/
theorem canonicalArtinianOpenLift_point
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    ∃ x : PrimeSpectrum B,
      (Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ) x ∈ Set.range iΛ' :=
  ⟨_, closedPoint_mem_range iΛ iΛ' hclosed B⟩

/-- At the structure morphism of `B`, `artinianAlgebraMapOfOpenLift` agrees with
`canonicalArtinianOpenLift`. -/
theorem artinianAlgebraMapOfOpenLift_eq_canonical
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')
    (x : PrimeSpectrum B)
    (hx : (Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ) x ∈ Set.range iΛ') :
    artinianAlgebraMapOfOpenLift B iΛ'
        (Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ) x hx =
      canonicalArtinianOpenLift iΛ iΛ' hiΛ' hclosed B := by
  let f : Spec (.of B) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ
  have hspec : Spec.map (CommRingCat.ofHom
      (artinianAlgebraMapOfOpenLift B iΛ' f x hx)) =
      Spec.map (CommRingCat.ofHom
        (canonicalArtinianOpenLift iΛ iΛ' hiΛ' hclosed B)) := by
    apply (cancel_mono iΛ').1
    rw [specMap_artinianAlgebraMapOfOpenLift, canonicalArtinianOpenLift_fac]
    exact artinianSpecLift_fac B f iΛ' x hx
  exact ringHom_eq_of_specMap_eq hspec

/-- Any ring map `Λ' → B` factoring the structure morphism through `Spec Λ'` equals
`canonicalArtinianOpenLift`. -/
theorem algebraMap_eq_canonicalArtinianOpenLift
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')
    (g : Λ' →+* B)
    (hgS : Spec.map (CommRingCat.ofHom g) ≫ iΛ' =
      Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ) :
    g = canonicalArtinianOpenLift iΛ iΛ' hiΛ' hclosed B := by
  have hx := canonicalArtinianOpenLift_point iΛ iΛ' hclosed B
  let x := Classical.choose hx
  have hxr := Classical.choose_spec hx
  let f : Spec (.of B) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ
  let lift := artinianAlgebraMapOfOpenLift B iΛ' f x hxr
  have hspec : Spec.map (CommRingCat.ofHom g) = Spec.map (CommRingCat.ofHom lift) := by
    apply (cancel_mono iΛ').1
    rw [hgS, specMap_artinianAlgebraMapOfOpenLift]
    exact (artinianSpecLift_fac B f iΛ' x hxr).symm
  rw [ringHom_eq_of_specMap_eq hspec]
  exact artinianAlgebraMapOfOpenLift_eq_canonical B iΛ iΛ' hiΛ' hclosed x hxr

/-- `canonicalArtinianOpenLift` is compatible with the residue-field identification. -/
theorem canonicalArtinianOpenLift_residue
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) (a : Λ') :
    B.residueEquiv (residue B
      (canonicalArtinianOpenLift iΛ iΛ' hiΛ' hclosed B a)) = algebraMap Λ' k a := by
  let : IsOpenImmersion iΛ' := hiΛ'
  exact artinianAlgebraMapOfOpenLift_residue B iΛ' _ _ (closedPoint_mem_range iΛ iΛ' hclosed B)
    (residueMap_comp_eq_of_closedCharts iΛ iΛ' hclosed B) a

end AlgebraicGeometry.Stack

end
