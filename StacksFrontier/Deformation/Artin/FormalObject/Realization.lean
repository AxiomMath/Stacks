module

public import StacksFrontier.Deformation.Artin.FormalObject.EffectiveOfBase
public import StacksFrontier.Deformation.Artin.FormalObject.ApproximationRepresentable

/-!
# Objects over a complete local base realizing a formal object

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids over the big fppf site of a scheme
`S` and let `ξ = (R, ξ_n, f_n)` be a formal object of `p` (**Stacks 07X4**) whose complete local
base `Spec R` belongs to the site. An object `x` of `𝒳` over `Spec R` *realizes* `ξ` when it
comes with arrows `ξ_n ⟶ x` over the inclusions `Spec(R / 𝔪^{n+1}) ⟶ Spec R` of the infinitesimal
thickenings, compatible with the transitions of `ξ`; in a category fibred in groupoids these
arrows are cartesian, so `ξ` is the system of restrictions of `x`. This is the sense in which the
source says that a formal object "comes from a morphism `Spec R ⟶ 𝒳`" (Stacks 0DR1), with the
morphism `Spec R ⟶ 𝒳` being the 1-morphism named by `x`.

Realization is stated with no reference to the *chosen* complete local base
`Deformation.Artin.chosenBase` that the approximation functor of **Stacks 07X6** works with, and it
is the form in which the statements of Stacks 07X8 are used downstream. This file proves the two
comparisons between them:

* an effective formal object (**Stacks 07X7**) is realized by an object lying over its own base,
  and a realized formal object is the image under the approximation functor of the realizing
  object, up to isomorphism;
* if the approximation functor is full, a morphism of formal objects between two realized formal
  objects comes from a morphism of the realizing objects, compatibly with the realizations, and
  that morphism lies over the map of complete local bases induced by the morphism of formal
  objects.

## Main definitions

* `Deformation.Artin.FormalObject.Realization`: a realization of a formal object by an object over
  its complete local base.

## Main results

* `Deformation.Artin.FormalObject.isoOfCompatibleMaps`: two formal objects with compatible arrows
  to the same object, over compatible isomorphisms of their levels, are isomorphic.
* `Deformation.Artin.FormalObject.Realization.approximationIso`: the approximation of a realizing
  object is isomorphic to the realized formal object.
* `Deformation.Artin.FormalObject.isEffective_of_realization` and
  `Deformation.Artin.FormalObject.exists_realization_of_isEffective`: realized formal objects are
  exactly the effective ones whose base belongs to the site.
* `Deformation.Artin.FormalObject.Realization.exists_hom`: under fullness of the approximation
  functor, morphisms of realized formal objects come from morphisms of the realizing objects.

## References

* [Stacks Project, Tag 07X4](https://stacks.math.columbia.edu/tag/07X4)
* [Stacks Project, Tag 07X6](https://stacks.math.columbia.edu/tag/07X6)
* [Stacks Project, Tag 07X7](https://stacks.math.columbia.edu/tag/07X7)
* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
-/

@[expose] public noncomputable section

namespace Deformation.Artin

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u v w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : Type v} [Category.{w} F] {p : F ⥤ BigFppfOver B S hS}

namespace FormalObject

/-! ### Formal objects with compatible arrows to one object -/

/-- **Two formal objects with compatible arrows to one object are isomorphic.** In a category
fibred in groupoids, let `ξ` and `η` be formal objects with arrows `r_n : ξ_n ⟶ x` and
`r'_n : η_n ⟶ x` compatible with the transitions, and let `θ_n` be isomorphisms of the objects of
the site under the levels, compatible with the transitions, with `θ_n ≫ p(r_n) = p(r'_n)`. Then
the unique lifts of the `θ_n` through the `r_n` form an isomorphism `η ≅ ξ`. -/
def isoOfCompatibleMaps (hp : p.IsFiberedInGroupoids) {ξ η : FormalObject B S hS p} {x : F}
    (r : ∀ n, ξ.level n ⟶ x) (r' : ∀ n, η.level n ⟶ x)
    (hr : ∀ n, ξ.transition n ≫ r (n + 1) = r n)
    (hr' : ∀ n, η.transition n ≫ r' (n + 1) = r' n)
    (θ : ∀ n, p.obj (η.level n) ≅ p.obj (ξ.level n))
    (hθ : ∀ n, (θ n).hom ≫ p.map (r n) = p.map (r' n))
    (hθt : ∀ n, p.map (η.transition n) ≫ (θ (n + 1)).hom = (θ n).hom ≫ p.map (ξ.transition n)) :
    η ≅ ξ := by
  have hθ' : ∀ n, (θ n).inv ≫ p.map (r' n) = p.map (r n) := fun n => by
    rw [← hθ n, Iso.inv_hom_id_assoc]
  have hθt' : ∀ n, p.map (ξ.transition n) ≫ (θ (n + 1)).inv =
      (θ n).inv ≫ p.map (η.transition n) := fun n => by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hθt n, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  choose s hs using fun n => (hp.unique_lift (r n) (r' n) (θ n).hom (hθ n)).exists
  choose t ht using fun n => (hp.unique_lift (r' n) (r n) (θ n).inv (hθ' n)).exists
  have uniq : ∀ {a b : F} (φ : b ⟶ x) (ψ : a ⟶ x) (c₁ c₂ : a ⟶ b),
      p.map c₁ = p.map c₂ → c₁ ≫ φ = ψ → c₂ ≫ φ = ψ → c₁ = c₂ := by
    intro a b φ ψ c₁ c₂ hpc h₁ h₂
    obtain ⟨χ, -, hχ⟩ := hp.unique_lift φ ψ (p.map c₁) (by rw [← Functor.map_comp, h₁])
    exact (hχ c₁ ⟨rfl, h₁⟩).trans (hχ c₂ ⟨hpc.symm, h₂⟩).symm
  have hsnat : ∀ n, η.transition n ≫ s (n + 1) = s n ≫ ξ.transition n := fun n =>
    uniq (r (n + 1)) (r' n) _ _
      (by rw [Functor.map_comp, Functor.map_comp, (hs (n + 1)).1, (hs n).1, hθt n])
      (by rw [Category.assoc, (hs (n + 1)).2, hr' n])
      (by rw [Category.assoc, hr n, (hs n).2])
  have htnat : ∀ n, ξ.transition n ≫ t (n + 1) = t n ≫ η.transition n := fun n =>
    uniq (r' (n + 1)) (r n) _ _
      (by rw [Functor.map_comp, Functor.map_comp, (ht (n + 1)).1, (ht n).1, hθt' n])
      (by rw [Category.assoc, (ht (n + 1)).2, hr n])
      (by rw [Category.assoc, hr' n, (ht n).2])
  exact
  { hom := ⟨s, hsnat⟩
    inv := ⟨t, htnat⟩
    hom_inv_id := Hom.ext fun n => uniq (r' n) (r' n) _ _
      (by
        change p.map (s n ≫ t n) = p.map (𝟙 _)
        rw [Functor.map_comp, (hs n).1, (ht n).1, Iso.hom_inv_id, CategoryTheory.Functor.map_id])
      (by
        change (s n ≫ t n) ≫ r' n = r' n
        rw [Category.assoc, (ht n).2, (hs n).2])
      (Category.id_comp _)
    inv_hom_id := Hom.ext fun n => uniq (r n) (r n) _ _
      (by
        change p.map (t n ≫ s n) = p.map (𝟙 _)
        rw [Functor.map_comp, (ht n).1, (hs n).1, Iso.inv_hom_id, CategoryTheory.Functor.map_id])
      (by
        change (t n ≫ s n) ≫ r n = r n
        rw [Category.assoc, (hs n).2, (ht n).2])
      (Category.id_comp _) }

/-- The components of `Deformation.Artin.FormalObject.isoOfCompatibleMaps` are compatible with
the given arrows to `x`. -/
theorem isoOfCompatibleMaps_hom_app_comp (hp : p.IsFiberedInGroupoids)
    {ξ η : FormalObject B S hS p} {x : F}
    (r : ∀ n, ξ.level n ⟶ x) (r' : ∀ n, η.level n ⟶ x)
    (hr : ∀ n, ξ.transition n ≫ r (n + 1) = r n)
    (hr' : ∀ n, η.transition n ≫ r' (n + 1) = r' n)
    (θ : ∀ n, p.obj (η.level n) ≅ p.obj (ξ.level n))
    (hθ : ∀ n, (θ n).hom ≫ p.map (r n) = p.map (r' n))
    (hθt : ∀ n, p.map (η.transition n) ≫ (θ (n + 1)).hom = (θ n).hom ≫ p.map (ξ.transition n))
    (n : ℕ) :
    (isoOfCompatibleMaps hp r r' hr hr' θ hθ hθt).hom.app n ≫ r n = r' n := by
  unfold isoOfCompatibleMaps
  exact (Classical.choose_spec
    (hp.unique_lift (r n) (r' n) (θ n).hom (hθ n)).exists).2

/-! ### Realizations -/

variable (ξ : FormalObject B S hS p) (hA : B.Contains (Spec (.of ξ.base.R)))

/-- **A realization of a formal object `ξ` by an object `x` over its complete local base.** The
arrows `ξ_n ⟶ x` lie over the inclusions of the infinitesimal thickenings of the closed point of
`Spec R` and are compatible with the transitions of `ξ`. -/
structure Realization (x : F) (hx : p.obj x = baseOver B S hS ξ.base hA) where
  /-- The arrow from the `n`-th level to the realizing object. -/
  r : ∀ n, ξ.level n ⟶ x
  /-- The arrows are compatible with the transitions. -/
  comp_transition : ∀ n, ξ.transition n ≫ r (n + 1) = r n
  /-- The arrows lie over the inclusions of the infinitesimal thickenings. -/
  map_eq : ∀ n, p.map (r n) =
    eqToHom (ξ.level_eq n) ≫ restrictionToBase B S hS ξ.base hA ξ.contains n ≫ eqToHom hx.symm

variable {ξ hA}

/-- The realizing object, as a complete local object. -/
def Realization.completeLocalObject {x : F} {hx : p.obj x = baseOver B S hS ξ.base hA}
    (_ : Realization ξ hA x hx) : CompleteLocalObjects B S hS p :=
  ⟨⟨x, ⟨ξ.base, hA, hx⟩⟩⟩

/-- The inclusion of a thickening of a complete local base into it is a monomorphism of the site,
being a closed immersion. -/
instance mono_restrictionToBase (A : FormalBase S) (hA : B.Contains (Spec (.of A.R)))
    (c : ∀ n, B.Contains (A.truncation n)) (n : ℕ) :
    Mono (restrictionToBase B S hS A hA c n) := by
  have : Mono (adicThickeningι A.R (maximalIdeal A.R) n) := by
    have : IsClosedImmersion (adicThickeningι A.R (maximalIdeal A.R) n) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  refine ⟨fun {Z} g h hgh => ?_⟩
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  have := congrArg (fun m => B.inclusion.map m.left) hgh
  simp only [Over.comp_left, Functor.map_comp] at this
  exact (cancel_mono (adicThickeningι A.R (maximalIdeal A.R) n)).mp this

/-- **The isomorphisms of thickenings of two complete local bases with the same object of the
site commute with the inclusions of the thickenings.** -/
theorem truncationOverIso_hom_restrictionToBase {A A' : FormalBase S}
    {hA : B.Contains (Spec (.of A.R))} {hA' : B.Contains (Spec (.of A'.R))}
    (h : baseOver B S hS A hA = baseOver B S hS A' hA')
    (cA : ∀ n, B.Contains (A.truncation n)) (cA' : ∀ n, B.Contains (A'.truncation n)) (n : ℕ) :
    (truncationOverIso B S hS h cA cA' n).hom ≫ restrictionToBase B S hS A' hA' cA' n =
      restrictionToBase B S hS A hA cA n ≫ eqToHom h := by
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  rw [Over.comp_left, Over.comp_left, Functor.map_comp, Functor.map_comp, Over.eqToHom_left,
    eqToHom_map]
  show Spec.map (CommRingCat.ofHom (adicTruncationEquiv (baseRingEquiv B S hS h) n).toRingHom) ≫
      adicThickeningι A'.R (maximalIdeal A'.R) n =
    adicThickeningι A.R (maximalIdeal A.R) n ≫ _
  rw [specMap_adicTruncationEquiv_comp_ι, specMap_baseRingEquiv]
  rfl

/-- The transition of a formal object lies over the inclusion of one thickening in the next. -/
theorem map_transition (ζ : FormalObject B S hS p) (n : ℕ) :
    p.map (ζ.transition n) =
      eqToHom (ζ.level_eq n) ≫ truncationOverSucc B S hS ζ.base ζ.contains n ≫
        eqToHom (ζ.level_eq (n + 1)).symm := by
  let := ζ.transition_lift n
  exact IsHomLift.fac' p _ (ζ.transition n)

/-- An arrow from a level of a formal object to an object over the complete local base lies over
the inclusion of the thickening as soon as its image in the schemes is that inclusion. -/
private theorem map_eq_of_toScheme_map_eq (η : FormalObject B S hS p)
    (hA : B.Contains (Spec (.of η.base.R))) {z : F} (hz : p.obj z = baseOver B S hS η.base hA)
    {n : ℕ} (r : η.level n ⟶ z)
    (h : (BigFppfOver.toScheme B S hS).map (eqToHom (η.level_eq n).symm ≫ p.map r ≫ eqToHom hz) =
      adicThickeningι η.base.R (maximalIdeal η.base.R) n ≫
        eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (rfl : η.base = η.base))) :
    p.map r = eqToHom (η.level_eq n) ≫
      restrictionToBase B S hS η.base hA η.contains n ≫ eqToHom hz.symm := by
  have hfaith : eqToHom (η.level_eq n).symm ≫ p.map r ≫ eqToHom hz =
      restrictionToBase B S hS η.base hA η.contains n := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [h, restrictionToBase_toScheme]
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  rw [← hfaith]
  simp

/-- The core of `Deformation.Artin.FormalObject.Realization.approximationIso`, with the chosen
complete local base of the realizing object replaced by an arbitrary one, so that the equation
identifying it with the base of the approximation can be substituted. -/
private theorem nonempty_iso_of_realization_aux (hp : p.IsFiberedInGroupoids)
    {ξ : FormalObject B S hS p} {hA : B.Contains (Spec (.of ξ.base.R))}
    {x : F} {hx : p.obj x = baseOver B S hS ξ.base hA} (R : Realization ξ hA x hx)
    (η : FormalObject B S hS p) (A' : FormalBase S) (hA' : B.Contains (Spec (.of A'.R)))
    (hxA' : p.obj x = baseOver B S hS A' hA') (hbase : η.base = A')
    (r' : ∀ n, η.level n ⟶ x) (hr' : ∀ n, η.transition n ≫ r' (n + 1) = r' n)
    (hsch : ∀ n, (BigFppfOver.toScheme B S hS).map
        (eqToHom (η.level_eq n).symm ≫ p.map (r' n) ≫ eqToHom hxA') =
      adicThickeningι η.base.R (maximalIdeal η.base.R) n ≫
        eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) hbase)) :
    ∃ I : η ≅ ξ, ∀ n, I.hom.app n ≫ R.r n = r' n := by
  subst hbase
  have h : baseOver B S hS η.base hA' = baseOver B S hS ξ.base hA := hxA'.symm.trans hx
  let θ : ∀ n, p.obj (η.level n) ≅ p.obj (ξ.level n) := fun n =>
    eqToIso (η.level_eq n) ≪≫ truncationOverIso B S hS h η.contains ξ.contains n ≪≫
      eqToIso (ξ.level_eq n).symm
  have hr'map := fun n => map_eq_of_toScheme_map_eq η hA' hxA' (r' n) (hsch n)
  have hθ : ∀ n, (θ n).hom ≫ p.map (R.r n) = p.map (r' n) := by
    intro n
    simp only [θ, Iso.trans_hom, eqToIso.hom, Category.assoc, R.map_eq, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    rw [reassoc_of% (truncationOverIso_hom_restrictionToBase h η.contains ξ.contains n),
      hr'map n]
    simp
  have hθt : ∀ n, p.map (η.transition n) ≫ (θ (n + 1)).hom =
      (θ n).hom ≫ p.map (ξ.transition n) := by
    intro n
    simp only [θ, Iso.trans_hom, eqToIso.hom, Category.assoc, map_transition,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [reassoc_of% (truncationOverSucc_comp_truncationOverIso B S hS h η.contains
      ξ.contains n)]
  exact ⟨isoOfCompatibleMaps hp R.r r' R.comp_transition hr' θ hθ hθt,
    isoOfCompatibleMaps_hom_app_comp hp R.r r' R.comp_transition hr' θ hθ hθt⟩

/-- **The approximation of a realizing object is the realized formal object.** If `x` realizes
`ξ`, then the formal object that the approximation functor of **Stacks 07X6** attaches to `x` is
isomorphic to `ξ`. -/
theorem Realization.nonempty_approximationIso (hp : p.IsFiberedInGroupoids) {x : F}
    {hx : p.obj x = baseOver B S hS ξ.base hA} (R : Realization ξ hA x hx) :
    Nonempty ((approximationFunctor B S hS p hp).obj R.completeLocalObject ≅ ξ) := by
  obtain ⟨r', hbase, -, hr', -, hsch⟩ := (approximationFunctorData B S hS p hp).2
  obtain ⟨I, -⟩ := nonempty_iso_of_realization_aux hp R _ _ _
    (chosenBase_eq B S hS p R.completeLocalObject.obj) (hbase _) (r' _) (hr' _) (hsch _)
  exact ⟨I⟩

/-- **A realized formal object is effective** (**Stacks 07X7**). -/
theorem isEffective_of_realization (hp : p.IsFiberedInGroupoids) {x : F}
    {hx : p.obj x = baseOver B S hS ξ.base hA} (R : Realization ξ hA x hx) :
    IsEffective B S hS p hp ξ :=
  ⟨R.completeLocalObject, (R.nonempty_approximationIso hp)⟩

/-- If the components of an isomorphism of formal objects are compatible with arrows to an
object, so are those of its inverse. -/
private theorem inv_app_comp_eq {ξ η : FormalObject B S hS p} {x : F} {a : ∀ n, ξ.level n ⟶ x}
    {b : ∀ n, η.level n ⟶ x} {I : η ≅ ξ} (h : ∀ n, I.hom.app n ≫ a n = b n) (n : ℕ) :
    I.inv.app n ≫ b n = a n :=
  have hII : I.inv.app n ≫ I.hom.app n = 𝟙 _ := congrArg (fun g => Hom.app g n) I.inv_hom_id
  by rw [← h n, ← Category.assoc, hII, Category.id_comp]

/-- **A morphism of formal objects between realized formal objects comes from a morphism of the
realizing objects**, provided the approximation functor is full (the fullness half of
**Stacks 07X8**). The morphism `m : x ⟶ x'` is compatible with the realizations, and its image in
the site is the map of complete local bases of the given morphism of formal objects. -/
theorem Realization.exists_hom (hp : p.IsFiberedInGroupoids)
    (hfull : (approximationFunctor B S hS p hp).Full)
    {ξ' : FormalObject B S hS p} {hA' : B.Contains (Spec (.of ξ'.base.R))}
    {x x' : F} {hx : p.obj x = baseOver B S hS ξ.base hA}
    {hx' : p.obj x' = baseOver B S hS ξ'.base hA'}
    (R : Realization ξ hA x hx) (R' : Realization ξ' hA' x' hx') (ψ : ξ ⟶ ξ') :
    ∃ m : x ⟶ x', (∀ n, R.r n ≫ m = ψ.app n ≫ R'.r n) ∧
      ∀ a, ψ.IsBaseMap a →
        (BigFppfOver.toScheme B S hS).map (eqToHom hx.symm ≫ p.map m ≫ eqToHom hx') = a := by
  obtain ⟨r', hbase, -, hr', hnat, hsch⟩ := (approximationFunctorData B S hS p hp).2
  obtain ⟨I, hI⟩ := nonempty_iso_of_realization_aux hp R _ _ _
    (chosenBase_eq B S hS p R.completeLocalObject.obj) (hbase _) (r' _) (hr' _) (hsch _)
  obtain ⟨I', hI'⟩ := nonempty_iso_of_realization_aux hp R' _ _ _
    (chosenBase_eq B S hS p R'.completeLocalObject.obj) (hbase _) (r' _) (hr' _) (hsch _)
  let mt := (approximationFunctor B S hS p hp).preimage (I.hom ≫ ψ ≫ I'.inv)
  have hmt : (approximationFunctor B S hS p hp).map mt = I.hom ≫ ψ ≫ I'.inv :=
    (approximationFunctor B S hS p hp).map_preimage _
  have hII : ∀ n, I.inv.app n ≫ I.hom.app n = 𝟙 _ := fun n =>
    congrArg (fun g => Hom.app g n) I.inv_hom_id
  have hinv' : ∀ n, I'.inv.app n ≫ r' R'.completeLocalObject n = R'.r n :=
    inv_app_comp_eq hI'
  have hinv : ∀ n, I.inv.app n ≫ r' R.completeLocalObject n = R.r n := inv_app_comp_eq hI
  have hcomp : ∀ n, R.r n ≫ mt.1.1 = ψ.app n ≫ R'.r n := by
    intro n
    have e1 : R.r n ≫ mt.1.1 = I.inv.app n ≫ (r' _ n ≫ mt.1.1) :=
      (congrArg (fun g => g ≫ mt.1.1) (hinv n).symm).trans (Category.assoc _ _ _)
    have e2 : r' R.completeLocalObject n ≫ mt.1.1 =
        (I.hom.app n ≫ ψ.app n ≫ I'.inv.app n) ≫ r' R'.completeLocalObject n :=
      (hnat _ _ mt n).symm.trans (congrArg (fun g => Hom.app g n ≫ r' _ n) hmt)
    rw [e1, e2]
    simp only [Category.assoc]
    rw [hinv' n, ← Category.assoc, hII n, Category.id_comp]
    rfl
  refine ⟨mt.1.1, hcomp, fun a ha => ?_⟩
  let := ξ.base.complete
  apply hom_ext_of_adicThickening
  intro n
  have h : p.map (R.r n) ≫ p.map mt.1.1 = p.map (ψ.app n) ≫ p.map (R'.r n) :=
    (p.map_comp _ _).symm.trans ((congrArg p.map (hcomp n)).trans (p.map_comp _ _))
  rw [R.map_eq, R'.map_eq] at h
  have key : restrictionToBase B S hS ξ.base hA ξ.contains n ≫
      (eqToHom hx.symm ≫ p.map mt.1.1 ≫ eqToHom hx') =
      (eqToHom (ξ.level_eq n).symm ≫ p.map (ψ.app n) ≫ eqToHom (ξ'.level_eq n)) ≫
        restrictionToBase B S hS ξ'.base hA' ξ'.contains n := by
    calc _ = eqToHom (ξ.level_eq n).symm ≫ ((eqToHom (ξ.level_eq n) ≫
            restrictionToBase B S hS ξ.base hA ξ.contains n ≫ eqToHom hx.symm) ≫
            p.map mt.1.1) ≫ eqToHom hx' := by simp
      _ = eqToHom (ξ.level_eq n).symm ≫ (p.map (ψ.app n) ≫ eqToHom (ξ'.level_eq n) ≫
            restrictionToBase B S hS ξ'.base hA' ξ'.contains n ≫ eqToHom hx'.symm) ≫
            eqToHom hx' :=
          congrArg (fun g => eqToHom (ξ.level_eq n).symm ≫ g ≫ eqToHom hx') h
      _ = _ := by simp
  have hs := ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
    ((congrArg (BigFppfOver.toScheme B S hS).map key).trans
      ((BigFppfOver.toScheme B S hS).map_comp _ _))
  exact hs.trans (ha.2 n)

/-- The core of `Deformation.Artin.FormalObject.exists_realization_of_isEffective`, with the chosen
complete local base of the effectivity witness replaced by an arbitrary one, so that the equation
identifying it with the base of the approximation can be substituted. -/
private theorem exists_realization_aux (hp : p.IsFiberedInGroupoids)
    (η : FormalObject B S hS p) (z : F) (A' : FormalBase S)
    (hA' : B.Contains (Spec (.of A'.R))) (hzA' : p.obj z = baseOver B S hS A' hA')
    (hbase : η.base = A')
    (r' : ∀ n, η.level n ⟶ z) (hr' : ∀ n, η.transition n ≫ r' (n + 1) = r' n)
    (hsch : ∀ n, (BigFppfOver.toScheme B S hS).map
        (eqToHom (η.level_eq n).symm ≫ p.map (r' n) ≫ eqToHom hzA') =
      adicThickeningι η.base.R (maximalIdeal η.base.R) n ≫
        eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) hbase))
    (e : η ≅ ξ) :
    ∃ (x : F) (hx : p.obj x = baseOver B S hS ξ.base hA), Nonempty (Realization ξ hA x hx) := by
  subst hbase
  have hr'map := fun n => map_eq_of_toScheme_map_eq η hA' hzA' (r' n) (hsch n)
  let b := e.inv.baseMap
  have hb := e.inv.baseMap_spec
  let g₀ : baseOver B S hS ξ.base hA ⟶ baseOver B S hS η.base hA' :=
    Over.homMk (ObjectProperty.homMk b) (by
      apply ObjectProperty.hom_ext
      exact hb.1)
  have hg₀ : ∀ n, restrictionToBase B S hS ξ.base hA ξ.contains n ≫ g₀ =
      (eqToHom (ξ.level_eq n).symm ≫ p.map (e.inv.app n) ≫ eqToHom (η.level_eq n)) ≫
        restrictionToBase B S hS η.base hA' η.contains n := by
    intro n
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      restrictionToBase_toScheme, restrictionToBase_toScheme]
    exact (hb.2 n).symm
  obtain ⟨x, φ, hφ⟩ := hp.exists_lift (g₀ ≫ eqToHom hzA'.symm) z rfl
  let := hφ
  have hx : p.obj x = baseOver B S hS ξ.base hA :=
    IsHomLift.domain_eq p (g₀ ≫ eqToHom hzA'.symm) φ
  have hφmap : p.map φ = eqToHom hx ≫ g₀ ≫ eqToHom hzA'.symm := by
    rw [IsHomLift.fac' p (g₀ ≫ eqToHom hzA'.symm) φ]
    simp
  let f : ∀ n, p.obj (ξ.level n) ⟶ p.obj x := fun n =>
    eqToHom (ξ.level_eq n) ≫ restrictionToBase B S hS ξ.base hA ξ.contains n ≫ eqToHom hx.symm
  have hf : ∀ n, f n ≫ p.map φ = p.map (e.inv.app n ≫ r' n) := by
    intro n
    rw [hφmap, CategoryTheory.Functor.map_comp, hr'map n]
    simp only [f, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [reassoc_of% (hg₀ n)]
    simp
  choose r hr using fun n => (hp.unique_lift φ (e.inv.app n ≫ r' n) (f n) (hf n)).exists
  have uniq : ∀ {a : F} (ψ : a ⟶ z) (c₁ c₂ : a ⟶ x),
      p.map c₁ = p.map c₂ → c₁ ≫ φ = ψ → c₂ ≫ φ = ψ → c₁ = c₂ := by
    intro a ψ c₁ c₂ hpc h₁ h₂
    obtain ⟨χ, -, hχ⟩ := hp.unique_lift φ ψ (p.map c₁) (by rw [← Functor.map_comp, h₁])
    exact (hχ c₁ ⟨rfl, h₁⟩).trans (hχ c₂ ⟨hpc.symm, h₂⟩).symm
  refine ⟨x, hx, ⟨{ r := r, comp_transition := fun n => ?_, map_eq := fun n => (hr n).1 }⟩⟩
  refine uniq (e.inv.app n ≫ r' n) _ _ ?_ ?_ (hr n).2
  · rw [CategoryTheory.Functor.map_comp, (hr (n + 1)).1, (hr n).1, map_transition]
    simp only [f, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [reassoc_of% (restrictionToBase_succ B S hS ξ.base hA ξ.contains n)]
  · rw [Category.assoc, (hr (n + 1)).2, ← Category.assoc, e.inv.naturality n,
      Category.assoc, hr' n]

/-- **An effective formal object whose base belongs to the site is realized by an object over its
own base.** The approximation functor of **Stacks 07X6** produces the restrictions of an object
over the *chosen* complete local base of that object, which is only isomorphic to the base of the
given formal object; the realizing object is the pullback of the effectivity witness along that
isomorphism, the map of complete local bases induced by the isomorphism of formal objects. -/
theorem exists_realization_of_isEffective (hp : p.IsFiberedInGroupoids)
    (heff : IsEffective B S hS p hp ξ) :
    ∃ (x : F) (hx : p.obj x = baseOver B S hS ξ.base hA), Nonempty (Realization ξ hA x hx) := by
  obtain ⟨z, ⟨e⟩⟩ := heff
  obtain ⟨r', hbase, -, hr', -, hsch⟩ := (approximationFunctorData B S hS p hp).2
  exact exists_realization_aux hp _ _ _ _ (chosenBase_eq B S hS p z.obj) (hbase z) (r' z)
    (hr' z) (hsch z) e

/-! ### Transport along equalities -/

/-- The ring isomorphism between the rings of two equal complete local bases. -/
def _root_.Deformation.Artin.FormalBase.ringEquivOfEq {A₁ A₂ : FormalBase S} (h : A₁ = A₂) :
    A₁.R ≃+* A₂.R := by
  subst h
  exact RingEquiv.refl _

/-- The spectrum of `Deformation.Artin.FormalBase.ringEquivOfEq` is the identification of the two
spectra. -/
theorem _root_.Deformation.Artin.FormalBase.specMap_ringEquivOfEq {A₁ A₂ : FormalBase S}
    (h : A₁ = A₂) :
    Spec.map (CommRingCat.ofHom (FormalBase.ringEquivOfEq h).toRingHom) =
      eqToHom (congrArg (fun A : FormalBase S => Spec (.of A.R)) h).symm := by
  subst h
  exact Spec.map_id _

/-- The spectrum of the inverse of `Deformation.Artin.FormalBase.ringEquivOfEq` is the
identification of the two spectra. -/
theorem _root_.Deformation.Artin.FormalBase.specMap_ringEquivOfEq_symm {A₁ A₂ : FormalBase S}
    (h : A₁ = A₂) :
    Spec.map (CommRingCat.ofHom (FormalBase.ringEquivOfEq h).symm.toRingHom) =
      eqToHom (congrArg (fun A : FormalBase S => Spec (.of A.R)) h) := by
  subst h
  exact Spec.map_id _

/-- `Deformation.Artin.FormalBase.ringEquivOfEq` is compatible with the structure morphisms. -/
theorem _root_.Deformation.Artin.FormalBase.specMap_ringEquivOfEq_toS {A₁ A₂ : FormalBase S}
    (h : A₁ = A₂) :
    Spec.map (CommRingCat.ofHom (FormalBase.ringEquivOfEq h).toRingHom) ≫ A₁.toS = A₂.toS := by
  subst h
  exact (congrArg (· ≫ A₁.toS) (Spec.map_id _)).trans (Category.id_comp _)

/-- The inverse of `Deformation.Artin.FormalBase.ringEquivOfEq` is the one of the reversed
equality. -/
theorem _root_.Deformation.Artin.FormalBase.ringEquivOfEq_symm {A₁ A₂ : FormalBase S}
    (h : A₁ = A₂) : (FormalBase.ringEquivOfEq h).symm = FormalBase.ringEquivOfEq h.symm := by
  subst h
  rfl

/-- A realization of a formal object is a realization of any formal object equal to it, by the
same object. -/
def Realization.ofEq {ξ ξ' : FormalObject B S hS p} (h : ξ = ξ')
    {hA : B.Contains (Spec (.of ξ.base.R))} {hA' : B.Contains (Spec (.of ξ'.base.R))}
    {x : F} {hx : p.obj x = baseOver B S hS ξ.base hA}
    (hx' : p.obj x = baseOver B S hS ξ'.base hA') (R : Realization ξ hA x hx) :
    Realization ξ' hA' x hx' := by
  subst h
  exact R

end FormalObject

end Deformation.Artin

end
