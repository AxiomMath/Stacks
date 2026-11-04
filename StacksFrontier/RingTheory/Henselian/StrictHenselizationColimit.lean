module

public import StacksFrontier.RingTheory.Etale.FinitelyPresentable
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
import Mathlib.Algebra.Category.Ring.FinitePresentation
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite

/-!
# The strict henselization as a colimit of étale algebras

Let `p` be a prime ideal of a ring `R` and let `κ(p) ⊆ κ^sep` be a separable algebraic closure.
Consider the triples `(S, q, φ)` of an étale `R`-algebra `S`, a prime `q` of `S` over `p` and a
`κ(p)`-embedding `φ : κ(q) → κ^sep`. Such a triple is the same as an étale `R`-algebra `S` with an
`R`-algebra map `S → κ^sep`, whose kernel is `q`; a morphism of triples is an `R`-algebra map
compatible with the maps to `κ^sep`. The category of triples is filtered, and the strict
henselization `(R_p)^{sh}` is canonically the colimit of the algebras `S` and also of the local
rings `S_q`.

## Main definitions

* `CommAlgCat.AugmentedEtale R L`: the category of étale `R`-algebras with an `R`-algebra map to
  a field `L`.
* `CommAlgCat.AugmentedEtale.prime A`: the kernel of the augmentation, a prime ideal.
* `CommAlgCat.AugmentedEtale.forget R L`: the diagram of the algebras `S`.
* `CommAlgCat.AugmentedEtale.localization R L`: the diagram of the local rings `S_q`, with the
  localization maps `CommAlgCat.AugmentedEtale.toLocalization R L`.

## Main results

* `IsLocalRing.IsHenselization.isFiltered_augmentedEtale_and_isColimit`: Stacks 04GW.

## Implementation notes

The result is proved for an arbitrary field `L` over `κ(p)` and an arbitrary henselization `Rsh`
of `R_p` with residue field `L`: for `L = κ^sep` a separable algebraic closure this is the strict
henselization, and for `L = κ(p)` it recovers Lemma 04GV. The source identifies the colimit with
the strict henselization constructed in Lemma 04GP; here the colimit is identified with any ring
satisfying the characterization of Definition 04GQ, which by Lemma 08HT is the same thing.

The identification is canonical once a `κ(p)`-isomorphism `e : L ≅ κ(Rsh)` is fixed (such an `e`
exists by the definition of a henselization with residue field `L`, and is unique only up to the
Galois action when `L = κ^sep`): the colimit maps `S → Rsh` are the unique `R`-algebra maps whose
reduction `S → κ(Rsh)` is the augmentation `S → L` followed by `e` (Lemma 08HR), and the maps
`S_q → Rsh` are their extensions along `S → S_q`.

## References

* [StacksProject 04GW](https://stacks.math.columbia.edu/tag/04GW)
* [StacksProject 04GV](https://stacks.math.columbia.edu/tag/04GV)
* [StacksProject 04GQ](https://stacks.math.columbia.edu/tag/04GQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace CommAlgCat

variable (R : Type u) [CommRing R] (L : Type u) [Field L] [Algebra R L]

/-- The category of étale `R`-algebras `S` together with an `R`-algebra map `S → L` to a field;
morphisms are `R`-algebra maps compatible with the augmentations. For `L = κ^sep` a separable
algebraic closure of `κ(p)` these are the triples `(S, q, φ)` of Stacks 04GW. -/
abbrev AugmentedEtale : Type (u + 1) :=
  CostructuredArrow (CommAlgCat.etale.{u} R).ι (CommAlgCat.of R L)

namespace AugmentedEtale

variable {R L}

/-- The prime of an augmented étale algebra: the kernel of its augmentation. -/
def prime (A : AugmentedEtale R L) : Ideal (A.left.obj : Type u) :=
  RingHom.ker A.hom.hom

/-- The prime of an augmented étale algebra is a prime ideal. -/
instance (A : AugmentedEtale R L) : A.prime.IsPrime := RingHom.ker_isPrime _

/-- The underlying algebra of an augmented étale algebra is étale over `R`. -/
instance (A : AugmentedEtale R L) : Algebra.Etale R (A.left.obj : Type u) := A.left.property

/-- The `R`-algebra map underlying a morphism of augmented étale algebras. -/
abbrev map {A B : AugmentedEtale R L} (h : A ⟶ B) :
    (A.left.obj : Type u) →ₐ[R] (B.left.obj : Type u) :=
  ((CommAlgCat.etale.{u} R).ι.map h.left).hom

/-- The identity morphism has the identity as underlying map. -/
theorem map_id (A : AugmentedEtale R L) : map (𝟙 A) = AlgHom.id R _ := by
  simp [map]

/-- Underlying maps of morphisms compose. -/
theorem map_comp {A B C : AugmentedEtale R L} (f : A ⟶ B) (g : B ⟶ C) :
    map (f ≫ g) = (map g).comp (map f) :=
  congrArg CommAlgCat.Hom.hom ((CommAlgCat.etale.{u} R).ι.map_comp f.left g.left)

/-- Morphisms are compatible with the augmentations. -/
theorem hom_map {A B : AugmentedEtale R L} (f : A ⟶ B) (x : (A.left.obj : Type u)) :
    B.hom.hom (map f x) = A.hom.hom x :=
  ConcreteCategory.congr_hom (CostructuredArrow.w f) x

/-- Morphisms pull back the prime. -/
theorem prime_eq_comap {A B : AugmentedEtale R L} (f : A ⟶ B) :
    A.prime = B.prime.comap (map f) := by
  ext x
  simp only [prime, RingHom.mem_ker, Ideal.mem_comap]
  rw [hom_map]

variable (R L)

/-- The diagram sending an augmented étale algebra `S` to the `R`-algebra `S`. -/
abbrev forget : AugmentedEtale R L ⥤ CommAlgCat.{u} R :=
  CostructuredArrow.proj _ _ ⋙ (CommAlgCat.etale.{u} R).ι

/-- The diagram sending an augmented étale algebra `S` with prime `q` to the local ring `S_q`. -/
noncomputable abbrev localization : AugmentedEtale R L ⥤ CommAlgCat.{u} R where
  obj A := CommAlgCat.of R (Localization.AtPrime A.prime)
  map f := CommAlgCat.ofHom (Localization.localAlgHom _ _ (map f) (prime_eq_comap f))
  map_id A := CommAlgCat.hom_ext <| IsLocalization.algHom_ext A.prime.primeCompl <|
    AlgHom.ext fun x => by simp [map_id]
  map_comp {A _ _} f g := CommAlgCat.hom_ext <| AlgHom.coe_ringHom_injective <|
    IsLocalization.ringHom_ext A.prime.primeCompl <| RingHom.ext fun x => by
      simp [map_comp, Localization.localRingHom_to_map]

/-- The localization maps `S → S_q`. -/
noncomputable def toLocalization : forget R L ⟶ localization R L where
  app A := CommAlgCat.ofHom
    (IsScalarTower.toAlgHom R (A.left.obj : Type u) (Localization.AtPrime A.prime))
  naturality A B f := CommAlgCat.hom_ext <| AlgHom.ext fun x => by simp [localization, map]

end AugmentedEtale

end CommAlgCat

attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace CommAlgCat.AugmentedEtale

variable {R : Type u} [CommRing R] {L : Type u} [Field L] [Algebra R L]

/-- Two maps out of `S_q` agreeing on `S` are equal. -/
private theorem localization_hom_ext (A : AugmentedEtale R L) {T : CommAlgCat.{u} R}
    {f g : (localization R L).obj A ⟶ T}
    (h : (toLocalization R L).app A ≫ f = (toLocalization R L).app A ≫ g) : f = g :=
  CommAlgCat.hom_ext <| IsLocalization.algHom_ext A.prime.primeCompl <|
    congrArg CommAlgCat.Hom.hom h

/-- Every cocone over the augmented étale algebras inverts the elements outside their primes. -/
private theorem cocone_isUnit (c : Cocone (forget R L)) (A : AugmentedEtale R L)
    (x : A.prime.primeCompl) : IsUnit ((c.ι.app A).hom (x : (A.left.obj : Type u))) := by
  obtain ⟨B, f, hf⟩ := CommAlgCat.exists_costructuredArrow_etale_hom_isUnit R L A x x.property
  rw [← ConcreteCategory.congr_hom (c.w f) (x : (A.left.obj : Type u))]
  exact hf.map (c.ι.app B).hom

/-- The extension `S_q → c.pt` of the leg `S → c.pt` of a cocone. -/
private noncomputable def localizedLeg (c : Cocone (forget R L)) (A : AugmentedEtale R L) :
    (localization R L).obj A ⟶ c.pt :=
  CommAlgCat.ofHom (IsLocalization.liftAlgHom (A := R) (R := (A.left.obj : Type u))
    (P := (c.pt : Type u)) (S := Localization.AtPrime A.prime)
    (f := ((c.ι.app A).hom : (A.left.obj : Type u) →ₐ[R] c.pt)) (cocone_isUnit c A))

private theorem toLocalization_app_apply (A : AugmentedEtale R L) (x : (A.left.obj : Type u)) :
    ((toLocalization R L).app A).hom x = algebraMap _ (Localization.AtPrime A.prime) x := rfl

private theorem localizedLeg_fac (c : Cocone (forget R L)) (A : AugmentedEtale R L) :
    (toLocalization R L).app A ≫ localizedLeg c A = c.ι.app A := by
  ext x
  rw [CommAlgCat.hom_comp, AlgHom.comp_apply, toLocalization_app_apply]
  exact IsLocalization.lift_eq (S := Localization.AtPrime A.prime) (cocone_isUnit c A) x

/-- A cocone over the augmented étale algebras, extended along the localizations `S → S_q`. -/
private noncomputable abbrev localizedCocone (c : Cocone (forget R L)) :
    Cocone (localization R L) where
  pt := c.pt
  ι.app := localizedLeg c
  ι.naturality A B f := localization_hom_ext A <| by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    rw [← Category.assoc, ← (toLocalization R L).naturality, Category.assoc, localizedLeg_fac,
      localizedLeg_fac]
    exact c.w f

/-- Extending a colimit cocone along the localizations gives a colimit cocone. -/
private noncomputable def isColimitLocalizedCocone {c : Cocone (forget R L)} (hc : IsColimit c) :
    IsColimit (localizedCocone c) where
  desc s := hc.desc ((Cocone.precompose (toLocalization R L)).obj s)
  fac s A := localization_hom_ext A <| by
    rw [← Category.assoc]
    exact (congrArg (· ≫ _) (localizedLeg_fac c A)).trans
      (hc.fac ((Cocone.precompose (toLocalization R L)).obj s) A)
  uniq s m hm := hc.hom_ext fun A => by
    rw [hc.fac, ← localizedLeg_fac c A, Category.assoc]
    exact congrArg ((toLocalization R L).app A ≫ ·) (hm A)

end CommAlgCat.AugmentedEtale

namespace IsLocalRing.IsHenselization

open CommAlgCat CommAlgCat.AugmentedEtale

variable {R : Type u} [CommRing R] {p : Ideal R} [p.IsPrime] {L : Type u} [Field L] [Algebra R L]
  [Algebra p.ResidueField L] {Rsh : Type u} [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
  [Algebra (Localization.AtPrime p) Rsh]

omit [Algebra R L] in
/-- **The residue field of a henselization of `R_p` with residue field `L` is `L` over `R`.** If
`L` is an extension of `κ(p)` compatibly with `R → κ(p)`, the isomorphism `L ≅ κ(Rsh)` of the
definition is compatible with the two maps out of `R`. -/
theorem exists_residueFieldEquiv_algebraMap [Algebra R L] [IsScalarTower R p.ResidueField L]
    [IsScalarTower R (Localization.AtPrime p) Rsh]
    [IsHenselization (Localization.AtPrime p) L Rsh] :
    ∃ e : L ≃+* ResidueField Rsh, ∀ r : R, e (algebraMap R L r) = algebraMap R (ResidueField Rsh) r
    := by
  obtain ⟨e, he⟩ := exists_residueFieldEquiv (R := Localization.AtPrime p) (L := L) (Rh := Rsh)
  refine ⟨e, fun r => ?_⟩
  rw [IsScalarTower.algebraMap_apply R p.ResidueField L,
    IsScalarTower.algebraMap_apply R (Localization.AtPrime p) p.ResidueField,
    ResidueField.algebraMap_eq, he, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R Rsh (ResidueField Rsh), ResidueField.algebraMap_eq]

variable (e : L ≃+* ResidueField Rsh)
  (he : ∀ r : R, e (algebraMap R L r) = algebraMap R (ResidueField Rsh) r)

include he in
/-- The augmentation of an augmented étale algebra followed by `e : L ≅ κ(Rsh)`. -/
private noncomputable abbrev residueLift (A : AugmentedEtale R L) :
    (A.left.obj : Type u) →ₐ[R] ResidueField Rsh :=
  { toRingHom := e.toRingHom.comp A.hom.hom.toRingHom
    commutes' := fun r => (congrArg e (A.hom.hom.commutes r)).trans (he r) }

include he in
/-- The augmentation `Rsh → κ(Rsh) ≅ L`, as an `R`-algebra map. -/
private theorem exists_aug :
    ∃ aug : Rsh →ₐ[R] L, ∀ y, e (aug y) = residue Rsh y := by
  refine ⟨{ toRingHom := e.symm.toRingHom.comp (residue Rsh), commutes' := fun r => ?_ },
    fun y => e.apply_symm_apply (residue Rsh y)⟩
  refine e.injective ((e.apply_symm_apply _).trans ?_)
  rw [he, IsScalarTower.algebraMap_apply R Rsh (ResidueField Rsh), ResidueField.algebraMap_eq]

variable (p) [IsHenselization (Localization.AtPrime p) L Rsh]

include p he

private theorem existsUnique_leg (A : AugmentedEtale R L) :
    ∃! f : (A.left.obj : Type u) →ₐ[R] Rsh, ∀ x, residue Rsh (f x) = e (A.hom.hom x) :=
  have := henselian (R := Localization.AtPrime p) (L := L) (Rh := Rsh)
  HenselianLocalRing.existsUnique_algHom_residue_of_etale (residueLift e he A)

/-- The canonical map `S → Rsh` of an augmented étale algebra. -/
private noncomputable def leg (A : AugmentedEtale R L) : (A.left.obj : Type u) →ₐ[R] Rsh :=
  (existsUnique_leg p e he A).exists.choose

private theorem residue_leg (A : AugmentedEtale R L) (x : (A.left.obj : Type u)) :
    residue Rsh (leg p e he A x) = e (A.hom.hom x) :=
  (existsUnique_leg p e he A).exists.choose_spec x

private theorem eq_leg {A : AugmentedEtale R L} (f : (A.left.obj : Type u) →ₐ[R] Rsh)
    (hf : ∀ x, residue Rsh (f x) = e (A.hom.hom x)) : f = leg p e he A :=
  (existsUnique_leg p e he A).unique hf (residue_leg p e he A)

private theorem leg_comp_map {A B : AugmentedEtale R L} (h : A ⟶ B) :
    (leg p e he B).comp (map h) = leg p e he A :=
  eq_leg p e he _ fun x => by rw [AlgHom.comp_apply, residue_leg, hom_map]

/-- The canonical cocone of the augmented étale algebras over `Rsh`. -/
private noncomputable def canonicalι :
    forget R L ⟶ (Functor.const _).obj (CommAlgCat.of R Rsh) where
  app A := CommAlgCat.ofHom (leg p e he A)
  naturality _ _ h := by
    ext x
    exact AlgHom.congr_fun (leg_comp_map p e he h) x

/-- The canonical cocone exhibits `Rsh` as the colimit of the augmented étale algebras. -/
private theorem nonempty_isColimit_canonical [IsScalarTower R (Localization.AtPrime p) Rsh] :
    Nonempty (IsColimit (Cocone.mk _ (canonicalι p e he))) := by
  obtain ⟨aug, haug⟩ := exists_aug e he
  obtain ⟨J, _, _, pres, hpres⟩ := CommAlgCat.ind_etale_comp
    (CommAlgCat.ind_etale_atPrime R (Localization.AtPrime p) p)
    (ind_etale_of_universe_le (R := Localization.AtPrime p) (L := L) (Rh := Rsh))
  let obj (j : J) : AugmentedEtale R L := CostructuredArrow.mk (Y := ⟨pres.diag.obj j, hpres j⟩)
    (CommAlgCat.ofHom (aug.comp (pres.ι.app j).hom))
  have hstage (j : J) : (canonicalι p e he).app (obj j) = pres.ι.app j :=
    CommAlgCat.hom_ext (eq_leg p e he _ fun x => (haug _).symm).symm
  let mapj {i j : J} (g : i ⟶ j) : obj i ⟶ obj j :=
    CostructuredArrow.homMk (ObjectProperty.homMk (pres.diag.map g))
      (CommAlgCat.hom_ext (AlgHom.ext fun x =>
        congrArg aug (ConcreteCategory.congr_hom (pres.w g) x)))
  let d (s : Cocone (forget R L)) : Cocone pres.diag :=
    { pt := s.pt
      ι := { app j := s.ι.app (obj j), naturality i j g := s.w (mapj g) } }
  refine ⟨{ desc s := pres.isColimit.desc (d s), fac s A := ?_, uniq s m hm := ?_ }⟩
  · have : IsFinitelyPresentable.{u} ((forget R L).obj A) :=
      CommAlgCat.isFinitelyPresentable_of_etale A.left.obj
    obtain ⟨j, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit pres.isColimit
      ((canonicalι p e he).app A)
    have hgx (x : (A.left.obj : Type u)) :
        (pres.ι.app j).hom (g.hom x) = leg p e he A x :=
      ConcreteCategory.congr_hom hg x
    let a : A ⟶ obj j := CostructuredArrow.homMk (ObjectProperty.homMk g)
      (CommAlgCat.hom_ext (AlgHom.ext fun x => e.injective (by
        rw [CommAlgCat.hom_comp, AlgHom.comp_apply, CostructuredArrow.mk_hom_eq_self,
          CommAlgCat.hom_ofHom, AlgHom.comp_apply, haug, ObjectProperty.ι_map]
        exact (congrArg (residue Rsh) (hgx x)).trans (residue_leg p e he A x))))
    rw [← hg, Category.assoc, pres.isColimit.fac]
    exact s.w a
  · exact pres.isColimit.hom_ext fun j => by rw [pres.isColimit.fac, ← hstage]; exact hm (obj j)

variable (Rsh) in
/-- **The strict henselization as a colimit of étale algebras** (Stacks 04GW). Let `p` be a prime
of `R`, let `L` be an extension of `κ(p)` (a separable algebraic closure `κ^sep`, in the source),
let `Rsh` be a henselization of `R_p` with residue field `L` (the strict henselization
`(R_p)^{sh}`), and fix an isomorphism `e : L ≅ κ(Rsh)` compatible with the maps from `R`. The
category of étale `R`-algebras `S` with an `R`-algebra map `S → L` — the triples `(S, q, φ)` — is
filtered, and `Rsh` is canonically the colimit of the algebras `S` and also of the local rings
`S_q`, where `q` is the kernel of `S → L`. The canonical maps `S → Rsh` are the unique `R`-algebra
maps whose reduction is `S → L ≅ κ(Rsh)`, and the maps `S_q → Rsh` extend them. -/
@[stacks 04GW "A triple `(S, q, φ)` is an étale `R`-algebra with an `R`-algebra map to `κ^sep`,
whose kernel is `q`. The strict henselization of `R_p` with respect to `κ^sep` is
`IsHenselization (Localization.AtPrime p) κsep Rsh`; the statement is proved for any extension `L`
of `κ(p)`. `canonically` is the characterization of the colimit maps `S → Rsh`: given the
identification `e : κ^sep ≅ κ(Rsh)`, they are the unique maps reducing to `S → κ^sep ≅ κ(Rsh)`;
the maps `S_q → Rsh` extend them along `S → S_q`."]
theorem isFiltered_augmentedEtale_and_isColimit [IsScalarTower R (Localization.AtPrime p) Rsh] :
    IsFiltered (AugmentedEtale R L) ∧
      ∃ ι : forget R L ⟶ (Functor.const _).obj (CommAlgCat.of R Rsh),
        (∀ A x, residue Rsh ((ι.app A).hom x) = e (A.hom.hom x)) ∧
        (∀ ι' : forget R L ⟶ (Functor.const _).obj (CommAlgCat.of R Rsh),
          (∀ A x, residue Rsh ((ι'.app A).hom x) = e (A.hom.hom x)) → ι' = ι) ∧
        Nonempty (IsColimit (Cocone.mk _ ι)) ∧
        ∃ ιLoc : localization R L ⟶ (Functor.const _).obj (CommAlgCat.of R Rsh),
          (∀ A, (toLocalization R L).app A ≫ ιLoc.app A = ι.app A) ∧
          Nonempty (IsColimit (Cocone.mk _ ιLoc)) := by
  obtain ⟨hc⟩ := nonempty_isColimit_canonical p e he
  exact ⟨CommAlgCat.isFiltered_costructuredArrow_etale R L, canonicalι p e he,
    fun A x => residue_leg p e he A x, fun ι' h => NatTrans.ext <| funext fun A =>
      CommAlgCat.hom_ext (eq_leg p e he (ι'.app A).hom (h A)), ⟨hc⟩,
    (localizedCocone (Cocone.mk _ (canonicalι p e he))).ι,
    localizedLeg_fac _, ⟨isColimitLocalizedCocone hc⟩⟩

end IsLocalRing.IsHenselization
