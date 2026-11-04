module

public import StacksFrontier.Deformation.Artin.Versality.OpennessCounterexampleAxioms
public import StacksFrontier.Deformation.Artin.FormalObject.ApproximationRepresentable
public import StacksFrontier.Deformation.Artin.FormalObject.EffectiveOfBase
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# Axiom [4] for the openness-of-versality example

Tag 07XR asserts that the category `𝒳` of the example satisfies axiom [4] of Artin's axioms:
the functor of Stacks 07X6, from objects of `𝒳` over the spectra of Noetherian complete local
rings to formal objects of `𝒳`, is an equivalence. This file proves it.

## Main results

* `Deformation.Artin.full_of_isApproximationFunctor_of_full` — the functor of Stacks 07X6 is
  full when the structure functor is fully faithful.
* `Deformation.Artin.contains_spec_of_contains_truncation` — the spectrum of a complete local
  base lies in the big fppf site when its infinitesimal thickenings do.
* `Deformation.Artin.isArtinAxiomsObject_baseOver` — the spectrum of the base of a formal
  object of `𝒳` lies in `𝒳`.
* `Deformation.Artin.isEquivalence_approximationFunctor_artinAxiomsCategory` — axiom [4] for
  the category of Tag 07XR.

## References

* [Stacks Project, Tag 07XR](https://stacks.math.columbia.edu/tag/07XR)
* [Stacks Project, Tag 07X6](https://stacks.math.columbia.edu/tag/07X6)
-/

@[expose] public section

namespace Deformation.Artin

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u v w

/-! ### Fullness for a fully faithful structure functor -/

section Full

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS)

/-- Two morphisms of formal objects agree as soon as the first is compatible, on every
infinitesimal thickening, with the base map of the second. -/
private theorem FormalObject.Hom.ext_of_baseMap [p.Faithful] {X Y : FormalObject B S hS p}
    {Ψ Φ : X ⟶ Y}
    (h : ∀ n, (BigFppfOver.toScheme B S hS).map
        (eqToHom (X.level_eq n).symm ≫ p.map (Ψ.app n) ≫ eqToHom (Y.level_eq n)) ≫
        adicThickeningι Y.base.R (maximalIdeal Y.base.R) n =
      adicThickeningι X.base.R (maximalIdeal X.base.R) n ≫ Φ.baseMap) : Ψ = Φ := by
  refine FormalObject.Hom.ext fun n => p.map_injective ?_
  have hlevel : eqToHom (X.level_eq n).symm ≫ p.map (Ψ.app n) ≫ eqToHom (Y.level_eq n) =
      eqToHom (X.level_eq n).symm ≫ p.map (Φ.app n) ≫ eqToHom (Y.level_eq n) :=
    (BigFppfOver.toScheme B S hS).map_injective <|
      (cancel_mono (adicThickeningι Y.base.R (maximalIdeal Y.base.R) n)).mp
        ((h n).trans (Φ.baseMap_spec.2 n).symm)
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id] using
    congrArg (fun z => eqToHom (X.level_eq n) ≫ z ≫ eqToHom (Y.level_eq n).symm) hlevel

/-- The base map of a morphism of formal objects, transported to chosen complete local bases, is
the image of a morphism of the big fppf site over `S`. -/
private theorem exists_baseOver_hom_toScheme_map_eq_baseMap {X Y : FormalObject B S hS p}
    (Φ : X ⟶ Y) {x y : CompleteLocalObjectsFull B S hS p} (hx : X.base = chosenBase B S hS p x)
    (hy : Y.base = chosenBase B S hS p y) :
    ∃ ab : baseOver B S hS (chosenBase B S hS p x) (chosenContains B S hS p x) ⟶
      baseOver B S hS (chosenBase B S hS p y) (chosenContains B S hS p y),
      (BigFppfOver.toScheme B S hS).map ab =
        eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) hx).symm ≫ Φ.baseMap ≫
          eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) hy) := by
  have hαS :
      (eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) hx).symm ≫ Φ.baseMap ≫
          eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) hy)) ≫
        (chosenBase B S hS p y).toS = (chosenBase B S hS p x).toS := by
    rw [Category.assoc, Category.assoc, eqToHom_formalBase_toS hy,
      Φ.baseMap_spec.1, ← eqToHom_formalBase_toS hx, ← Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.id_comp]
  exact ⟨Over.homMk (ObjectProperty.homMk
      (X := B.obj (chosenContains B S hS p x))
      (Y := B.obj (chosenContains B S hS p y)) _)
    (by apply ObjectProperty.hom_ext; exact hαS), rfl⟩

/-- A morphism `f` of complete local objects lying over the transported base map of a morphism
`Φ` of formal objects is, through an approximation functor, compatible with that base map. -/
private theorem toScheme_map_app_comp_adicThickeningι
    {G : CompleteLocalObjects B S hS p ⥤ FormalObject B S hS p}
    (r : ∀ (x : CompleteLocalObjects B S hS p) (n : ℕ), (G.obj x).level n ⟶ x.obj.1)
    (hb : ∀ x, (G.obj x).base = chosenBase B S hS p x.obj)
    (hι : ∀ x n,
      (BigFppfOver.toScheme B S hS).map
          (eqToHom ((G.obj x).level_eq n).symm ≫ p.map (r x n) ≫
            eqToHom (chosenBase_eq B S hS p x.obj)) =
        adicThickeningι (G.obj x).base.R
          (maximalIdeal (G.obj x).base.R) n ≫
          eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb x)))
    {x y : CompleteLocalObjects B S hS p} (Φ : G.obj x ⟶ G.obj y) (f : x ⟶ y)
    (ab : baseOver B S hS (chosenBase B S hS p x.obj) (chosenContains B S hS p x.obj) ⟶
      baseOver B S hS (chosenBase B S hS p y.obj) (chosenContains B S hS p y.obj))
    (hab : (BigFppfOver.toScheme B S hS).map ab =
      eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb x)).symm ≫ Φ.baseMap ≫
        eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb y)))
    (hf : p.map f.1.1 = eqToHom (chosenBase_eq B S hS p x.obj) ≫ ab ≫
      eqToHom (chosenBase_eq B S hS p y.obj).symm)
    (n : ℕ) (hnat : (G.map f).app n ≫ r y n = r x n ≫ f.1.1) :
    (BigFppfOver.toScheme B S hS).map
        (eqToHom ((G.obj x).level_eq n).symm ≫ p.map ((G.map f).app n) ≫
          eqToHom ((G.obj y).level_eq n)) ≫
        adicThickeningι (G.obj y).base.R (maximalIdeal (G.obj y).base.R) n =
      adicThickeningι (G.obj x).base.R (maximalIdeal (G.obj x).base.R) n ≫ Φ.baseMap := by
  have h := congrArg p.map hnat
  rw [Functor.map_comp, Functor.map_comp, hf] at h
  have hstep :
      (eqToHom ((G.obj x).level_eq n).symm ≫ p.map ((G.map f).app n) ≫
          eqToHom ((G.obj y).level_eq n)) ≫
        (eqToHom ((G.obj y).level_eq n).symm ≫ p.map (r y n) ≫
          eqToHom (chosenBase_eq B S hS p y.obj)) =
      (eqToHom ((G.obj x).level_eq n).symm ≫ p.map (r x n) ≫
        eqToHom (chosenBase_eq B S hS p x.obj)) ≫ ab := by
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [reassoc_of% h]
    simp only [eqToHom_trans, eqToHom_refl, Category.comp_id]
  refine (cancel_mono (eqToHom
    (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb y)))).mp ?_
  have h' : (BigFppfOver.toScheme B S hS).map
        (eqToHom ((G.obj x).level_eq n).symm ≫ p.map ((G.map f).app n) ≫
          eqToHom ((G.obj y).level_eq n)) ≫
        (BigFppfOver.toScheme B S hS).map
          (eqToHom ((G.obj y).level_eq n).symm ≫ p.map (r y n) ≫
            eqToHom (chosenBase_eq B S hS p y.obj)) =
      (BigFppfOver.toScheme B S hS).map
          (eqToHom ((G.obj x).level_eq n).symm ≫ p.map (r x n) ≫
            eqToHom (chosenBase_eq B S hS p x.obj)) ≫
        (BigFppfOver.toScheme B S hS).map ab := by
    rw [← Functor.map_comp, ← Functor.map_comp, hstep]
  rw [hι x n, hι y n, hab] at h'
  refine (Category.assoc _ _ _).trans (h'.trans ?_)
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => adicThickeningι (G.obj x).base.R
    (maximalIdeal (G.obj x).base.R) n ≫ z)
    ((eqToIso (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb x))).hom_inv_id_assoc _)) ?_
  exact (Category.assoc _ _ _).symm

/-- **Fullness of the functor (Stacks 07X6)** for a category over the big fppf site whose
structure functor is fully faithful. -/
public theorem full_of_isApproximationFunctor_of_full [p.Full] [p.Faithful]
    {G : CompleteLocalObjects B S hS p ⥤ FormalObject B S hS p}
    (hG : IsApproximationFunctor B S hS p G) : G.Full := by
  obtain ⟨r, hb, -, -, hnat, hι⟩ := hG
  constructor
  intro x y Φ
  obtain ⟨ab, hab⟩ := exists_baseOver_hom_toScheme_map_eq_baseMap p Φ (hb x) (hb y)
  have hΦcp : Φ.baseMap (closedPoint (G.obj x).base.R) =
      closedPoint (G.obj y).base.R := by
    have hpt : adicThickeningι (G.obj y).base.R (maximalIdeal (G.obj y).base.R) 0
          ((BigFppfOver.toScheme B S hS).map (eqToHom ((G.obj x).level_eq 0).symm ≫
            p.map (Φ.app 0) ≫ eqToHom ((G.obj y).level_eq 0))
            (closedPoint ((G.obj x).base.R ⧸ maximalIdeal (G.obj x).base.R ^ (0 + 1)))) =
        Φ.baseMap (adicThickeningι (G.obj x).base.R (maximalIdeal (G.obj x).base.R) 0
          (closedPoint ((G.obj x).base.R ⧸ maximalIdeal (G.obj x).base.R ^ (0 + 1)))) :=
      congrArg (fun e : adicThickening (G.obj x).base.R
          (maximalIdeal (G.obj x).base.R) 0 ⟶ Spec (.of (G.obj y).base.R) =>
        e (closedPoint ((G.obj x).base.R ⧸ maximalIdeal (G.obj x).base.R ^ (0 + 1))))
        (Φ.baseMap_spec.2 0)
    have hz : (BigFppfOver.toScheme B S hS).map
        (eqToHom ((G.obj x).level_eq 0).symm ≫ p.map (Φ.app 0) ≫
          eqToHom ((G.obj y).level_eq 0))
        (closedPoint ((G.obj x).base.R ⧸ maximalIdeal (G.obj x).base.R ^ (0 + 1))) =
        closedPoint ((G.obj y).base.R ⧸ maximalIdeal (G.obj y).base.R ^ (0 + 1)) :=
      eq_closedPoint_of_adicThickening 0 _
    rw [hz, adicThickeningι_closedPoint, adicThickeningι_closedPoint] at hpt
    exact hpt.symm
  obtain ⟨fm, hfm⟩ : ∃ fm : x.obj ⟶ y.obj, p.map fm.1 =
      eqToHom (chosenBase_eq B S hS p x.obj) ≫ ab ≫
        eqToHom (chosenBase_eq B S hS p y.obj).symm :=
    ⟨ObjectProperty.homMk (p.preimage _), p.map_preimage _⟩
  have hbm : baseMap B S hS p fm = (BigFppfOver.toScheme B S hS).map ab := by
    change (BigFppfOver.toScheme B S hS).map
      (eqToHom (chosenBase_eq B S hS p x.obj).symm ≫ p.map fm.1 ≫
        eqToHom (chosenBase_eq B S hS p y.obj)) = _
    rw [hfm]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp, Category.comp_id]
  have hloc : localBaseMaps B S hS p fm := by
    change baseMap B S hS p fm
        (closedPoint (chosenBase B S hS p x.obj).R) =
      closedPoint (chosenBase B S hS p y.obj).R
    rw [hbm, hab]
    change eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb y))
        (Φ.baseMap (eqToHom
          (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb x)).symm
          (closedPoint (chosenBase B S hS p x.obj).R))) =
      closedPoint (chosenBase B S hS p y.obj).R
    rw [eqToHom_symm_formalBase_closedPoint (hb x), hΦcp,
      eqToHom_formalBase_closedPoint (hb y)]
  exact ⟨⟨fm, hloc⟩, FormalObject.Hom.ext_of_baseMap p fun n =>
    toScheme_map_app_comp_adicThickeningι p r hb hι Φ ⟨fm, hloc⟩ ab hab hfm n
      (hnat x y ⟨fm, hloc⟩ n)⟩

end Full

/-! ### The spectrum of a complete local base lies in the site -/

/-- An element of a complete local ring lying in every power of the maximal ideal is zero. -/
private theorem eq_zero_of_forall_mem_pow {S : Scheme.{u}} (A : FormalBase S) {a : A.R}
    (h : ∀ n, a ∈ maximalIdeal A.R ^ (n + 1)) : a = 0 := by
  have := A.complete
  refine IsHausdorff.haus' (I := maximalIdeal A.R) a fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  cases n with
  | zero => simp
  | succ n => exact h n

/-- **The spectrum of a complete local base lies in the big fppf site as soon as all of its
infinitesimal thickenings do.** -/
public theorem contains_spec_of_contains_truncation (B : BigFppfSite.{u}) {S : Scheme.{u}}
    (A : FormalBase S) (h : ∀ n, B.Contains (A.truncation n)) :
    B.Contains (Spec (.of A.R)) := by
  let F : ULift.{u} ℕ → Scheme.{u} := fun i => A.truncation i.down
  let c := ⨆ i, (F i).size
  have hc : ∀ i, (F i).size ≤ c := fun i => le_ciSup (Cardinal.bddAbove_of_small) i
  refine Scheme.size_lt_of_le_stacksBound_iSup B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    B.aleph0_lt_cutoff_cof (by simp) F (fun i => h i.down) ?_
  have hinj : Function.Injective
      (fun a : A.R => fun i : ULift.{u} ℕ =>
        Ideal.Quotient.mk (maximalIdeal A.R ^ (i.down + 1)) a) := by
    intro a b hab
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_mem_pow A fun n => ?_
    rw [← Ideal.Quotient.eq]
    exact congrFun hab ⟨n⟩
  have hR : Cardinal.mk A.R ≤ c ^ Cardinal.aleph0 := by
    refine (Cardinal.mk_le_of_injective hinj).trans ?_
    rw [Cardinal.mk_pi]
    have hω : Cardinal.mk (ULift.{u} ℕ) = Cardinal.aleph0 := by simp
    rw [← hω, ← Cardinal.prod_const']
    refine Cardinal.prod_le_prod _ _ fun i => ?_
    refine le_trans ?_ (hc i)
    change Cardinal.mk (A.R ⧸ maximalIdeal A.R ^ (i.down + 1)) ≤
      (Spec (.of (A.R ⧸ maximalIdeal A.R ^ (i.down + 1)))).size
    rw [Scheme.size_Spec]
    exact le_max_right _ _
  have hc0 : Cardinal.aleph0 ≤ c := (Scheme.aleph0_le_size (F ⟨0⟩)).trans (hc ⟨0⟩)
  rw [Scheme.size_Spec]
  refine le_trans ?_ (le_max_left _ _)
  exact max_le (hc0.trans (Cardinal.self_le_power _ Cardinal.one_le_aleph0)) hR

/-! ### Axiom [4] -/

section Axiom4

variable {k : Type u} [Field k] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k))))

/-- The `k[s,t]`-algebra structure read off a composite with the spectrum of a ring map is
the given one followed by that ring map. -/
private theorem algebraMap_specAlgebra_specMap_comp {A A' : Type u} [CommRing A]
    [CommRing A'] (f : A →+* A') (τ : Spec (.of A) ⟶ Spec (.of (MvPolynomial (Fin 2) k)))
    (r : MvPolynomial (Fin 2) k) :
    @algebraMap _ _ _ _ (specAlgebra (Spec.map (CommRingCat.ofHom f) ≫ τ)) r =
      f (@algebraMap _ _ _ _ (specAlgebra τ) r) := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
  have e : (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv ≫
      (Spec.map (CommRingCat.ofHom f) ≫ τ).appTop ≫ (Scheme.ΓSpecIso (.of A')).hom =
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv ≫ τ.appTop ≫
        (Scheme.ΓSpecIso (.of A)).hom) ≫ CommRingCat.ofHom f := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, Category.assoc, h, Category.assoc]
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom e) r

/-- **The spectrum of a complete local base of a formal object of the category of Tag 07XR lies
in the category.** -/
public theorem isArtinAxiomsObject_baseOver
    (ξ : FormalObject B _ hS (ObjectProperty.ι (IsArtinAxiomsObject k B hS)))
    (hA : B.Contains (Spec (.of ξ.base.R))) :
    IsArtinAxiomsObject k B hS (baseOver B _ hS ξ.base hA) := by
  let A := ξ.base
  let τ := A.toS
  refine isArtinAxiomsObject_siteObject B hS hA τ ?_
  rw [@isAdmissible_iff_of_isLocalRing k _ _ _ _ (specAlgebra τ)]
  intro hs ht
  refine eq_zero_of_forall_mem_pow A fun n => ?_
  let mk := Ideal.Quotient.mk (maximalIdeal A.R ^ (n + 1))
  have : IsLocalHom mk := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let T := truncationOver B _ hS A ξ.contains n
  have hT : IsArtinAxiomsObject k B hS T := by
    have h : (ξ.level n).obj = T := ξ.level_eq n
    exact h ▸ (ξ.level n).property
  have : IsAffine ((BigFppfOver.toScheme B _ hS).obj T) :=
    inferInstanceAs (IsAffine (Spec (.of (A.R ⧸ maximalIdeal A.R ^ (n + 1)))))
  have hΓ := isAdmissible_sections_of_isArtinAxiomsObject B hS T hT
  have hn : @IsAdmissible k _ (A.R ⧸ maximalIdeal A.R ^ (n + 1)) _
      (specAlgebra (Spec.map (CommRingCat.ofHom mk) ≫ τ)) := by
    refine isAdmissible_of_ringHom _ _
      (Scheme.ΓSpecIso (.of (A.R ⧸ maximalIdeal A.R ^ (n + 1)))).hom.hom (fun r => ?_) hΓ
    change (Scheme.ΓSpecIso _).hom ((AlgebraicGeometry.toSpecΓ _ ≫
      (Spec.map (CommRingCat.ofHom mk) ≫ τ).appTop) r) = _
    rw [toSpecΓ_eq_ΓSpecIso_inv]
    rfl
  have h0 := @eq_zero_of_isAdmissible k _ _ _ _
    (specAlgebra (Spec.map (CommRingCat.ofHom mk) ≫ τ))
    (by rw [algebraMap_specAlgebra_specMap_comp]; exact map_nonunit mk _ hs)
    (by rw [algebraMap_specAlgebra_specMap_comp]; exact map_nonunit mk _ ht) hn
  rw [algebraMap_specAlgebra_specMap_comp] at h0
  exact Ideal.Quotient.eq_zero_iff_mem.mp h0

/-- **The category of the openness-of-versality example satisfies axiom [4]**: the functor of
Stacks 07X6, from objects over the spectra of Noetherian complete local rings to formal objects,
is an equivalence. -/
@[stacks 07XR "axiom [4]: the functor of Stacks 07X6 from objects over Noetherian complete \
  local rings to formal objects is an equivalence"]
public theorem isEquivalence_approximationFunctor_artinAxiomsCategory :
    (approximationFunctor B _ hS (ObjectProperty.ι (IsArtinAxiomsObject k B hS))
      (isFiberedInGroupoids_artinAxiomsCategory B hS)).IsEquivalence := by
  let p := ObjectProperty.ι (IsArtinAxiomsObject k B hS)
  have hp := isFiberedInGroupoids_artinAxiomsCategory B hS
  have hess : (approximationFunctor B _ hS p hp).EssSurj := ⟨fun ξ => by
    have hA := contains_spec_of_contains_truncation B ξ.base ξ.contains
    let x : CompleteLocalObjects B _ hS p :=
      ⟨⟨⟨baseOver B _ hS ξ.base hA, isArtinAxiomsObject_baseOver B hS ξ hA⟩,
        ξ.base, hA, rfl⟩⟩
    exact isEffective_of_object_over_base B _ hS p hp
      (fun t => ⟨ObjectProperty.homMk t, rfl⟩) (fun s t h => p.map_injective h) ξ hA x rfl⟩
  exact { faithful := faithful_approximationFunctor B _ hS p hp
          full := full_of_isApproximationFunctor_of_full p
            (approximationFunctorData B _ hS p hp).2
          essSurj := hess }

end Axiom4

end Deformation.Artin
