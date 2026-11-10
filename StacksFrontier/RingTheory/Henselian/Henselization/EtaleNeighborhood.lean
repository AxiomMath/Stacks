module

public import StacksFrontier.RingTheory.Etale.FinitelyPresentable
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
import Mathlib.Algebra.Category.Ring.FinitePresentation
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite

/-!
# The henselization as a colimit of étale neighborhoods

Let `p` be a prime ideal of a ring `R`. An *étale neighborhood* of `p` is a pair `(S, q)` of an
étale `R`-algebra `S` and a prime `q` of `S` over `p` with `κ(p) = κ(q)`; such a pair is the same
as an étale `R`-algebra `S` with an `R`-algebra map `S → κ(p)`, whose kernel is `q`. The category
of étale neighborhoods is filtered, and the henselization `(R_p)^h` is canonically the colimit of
the algebras `S` and also of the local rings `S_q`.

## Main definitions

* `Ideal.EtaleNeighborhood p`: the category of étale `R`-algebras augmented to `κ(p)`.
* `Ideal.EtaleNeighborhood.prime A`: the prime of an étale neighborhood `A`, the kernel of its
  augmentation.
* `Ideal.EtaleNeighborhood.forget p`: the diagram of the algebras `S`.
* `Ideal.EtaleNeighborhood.localization p`: the diagram of the local rings `S_q`, with the
  localization maps `Ideal.EtaleNeighborhood.toLocalization p`.

## Main results

* `IsLocalRing.IsHenselization.isFiltered_etaleNeighborhood_and_isColimit`: Stacks 04GV.

## Implementation notes

The canonical maps `S → (R_p)^h` are pinned by the residue condition: `S → (R_p)^h → κ((R_p)^h)`
is the augmentation `S → κ(p)` followed by the residue field isomorphism `κ(p) ≅ κ((R_p)^h)`; by
Lemma 08HR this determines them. The localized cocone is pinned by extending these maps along the
localizations `S → S_q`.

## References

* [StacksProject 04GV](https://stacks.math.columbia.edu/tag/04GV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace Ideal

variable {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]

/-- The category of étale neighborhoods `(S, q)` of `p` with `κ(q) = κ(p)`, as étale `R`-algebras
`S` with an `R`-algebra map `S → κ(p)`; morphisms are compatible with the augmentations. -/
noncomputable abbrev EtaleNeighborhood : Type (u + 1) :=
  CostructuredArrow (CommAlgCat.etale.{u} R).ι (CommAlgCat.of R p.ResidueField)

namespace EtaleNeighborhood

variable {p}

/-- The prime of an étale neighborhood: the kernel of its augmentation to `κ(p)`. -/
noncomputable def prime (A : EtaleNeighborhood p) : Ideal (A.left.obj : Type u) :=
  RingHom.ker A.hom.hom

/-- The prime of an étale neighborhood is a prime ideal. -/
instance (A : EtaleNeighborhood p) : A.prime.IsPrime := RingHom.ker_isPrime _

/-- The algebra of an étale neighborhood is étale over `R`. -/
instance (A : EtaleNeighborhood p) : Algebra.Etale R (A.left.obj : Type u) := A.left.property

/-- The `R`-algebra map underlying a morphism of étale neighborhoods. -/
abbrev map {A B : EtaleNeighborhood p} (h : A ⟶ B) :
    (A.left.obj : Type u) →ₐ[R] (B.left.obj : Type u) :=
  ((CommAlgCat.etale.{u} R).ι.map h.left).hom

/-- The identity morphism has the identity as underlying map. -/
theorem map_id (A : EtaleNeighborhood p) : map (𝟙 A) = AlgHom.id R _ := by
  simp [map]

/-- Underlying maps of morphisms compose. -/
theorem map_comp {A B C : EtaleNeighborhood p} (f : A ⟶ B) (g : B ⟶ C) :
    map (f ≫ g) = (map g).comp (map f) :=
  congrArg CommAlgCat.Hom.hom ((CommAlgCat.etale.{u} R).ι.map_comp f.left g.left)

/-- Morphisms of étale neighborhoods are compatible with the augmentations. -/
theorem hom_map {A B : EtaleNeighborhood p} (f : A ⟶ B) (x : (A.left.obj : Type u)) :
    B.hom.hom (map f x) = A.hom.hom x :=
  ConcreteCategory.congr_hom (CostructuredArrow.w f) x

/-- Morphisms of étale neighborhoods pull back the prime. -/
theorem prime_eq_comap {A B : EtaleNeighborhood p} (f : A ⟶ B) :
    A.prime = B.prime.comap (map f) := by
  ext x
  simp only [prime, RingHom.mem_ker, Ideal.mem_comap]
  rw [hom_map]

variable (p)

/-- The diagram sending an étale neighborhood `(S, q)` to the `R`-algebra `S`. -/
abbrev forget : EtaleNeighborhood p ⥤ CommAlgCat.{u} R :=
  CostructuredArrow.proj _ _ ⋙ (CommAlgCat.etale.{u} R).ι

/-- The diagram sending an étale neighborhood `(S, q)` to the local ring `S_q`. -/
noncomputable abbrev localization : EtaleNeighborhood p ⥤ CommAlgCat.{u} R where
  obj A := CommAlgCat.of R (Localization.AtPrime A.prime)
  map f := CommAlgCat.ofHom (Localization.localAlgHom _ _ (map f) (prime_eq_comap f))
  map_id A := CommAlgCat.hom_ext <| IsLocalization.algHom_ext A.prime.primeCompl <|
    AlgHom.ext fun x => by simp [map_id]
  map_comp {A _ _} f g := CommAlgCat.hom_ext <| AlgHom.toRingHom_injective <|
    IsLocalization.ringHom_ext A.prime.primeCompl <| RingHom.ext fun x => by
      simp [map_comp, Localization.localRingHom_to_map]

/-- The localization maps `S → S_q`. -/
noncomputable def toLocalization : forget p ⟶ localization p where
  app A := CommAlgCat.ofHom
    (IsScalarTower.toAlgHom R (A.left.obj : Type u) (Localization.AtPrime A.prime))
  naturality A B f := CommAlgCat.hom_ext <| AlgHom.ext fun x => by simp [localization, map]

end EtaleNeighborhood

end Ideal

attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace Ideal.EtaleNeighborhood

variable {R : Type u} [CommRing R] {p : Ideal R} [p.IsPrime]

/-- Two maps out of `S_q` agreeing on `S` are equal. -/
private theorem localization_hom_ext (A : EtaleNeighborhood p) {T : CommAlgCat.{u} R}
    {f g : (localization p).obj A ⟶ T}
    (h : (toLocalization p).app A ≫ f = (toLocalization p).app A ≫ g) : f = g :=
  CommAlgCat.hom_ext <| IsLocalization.algHom_ext A.prime.primeCompl <|
    congrArg CommAlgCat.Hom.hom h

/-- Every cocone over the étale neighborhoods inverts the elements outside their primes: such an
element becomes a unit in a localization, which is again an étale neighborhood. -/
private theorem cocone_isUnit (c : Cocone (forget p)) (A : EtaleNeighborhood p)
    (x : A.prime.primeCompl) : IsUnit ((c.ι.app A).hom (x : (A.left.obj : Type u))) := by
  obtain ⟨B, f, hf⟩ := CommAlgCat.exists_costructuredArrow_etale_hom_isUnit R p.ResidueField A x
    x.property
  rw [← ConcreteCategory.congr_hom (c.w f) (x : (A.left.obj : Type u))]
  exact hf.map (c.ι.app B).hom

/-- The extension `S_q → c.pt` of the leg `S → c.pt` of a cocone. -/
private noncomputable def localizedLeg (c : Cocone (forget p)) (A : EtaleNeighborhood p) :
    (localization p).obj A ⟶ c.pt :=
  CommAlgCat.ofHom (IsLocalization.liftAlgHom (A := R) (R := (A.left.obj : Type u))
    (P := (c.pt : Type u)) (S := Localization.AtPrime A.prime)
    (f := ((c.ι.app A).hom : (A.left.obj : Type u) →ₐ[R] c.pt)) (cocone_isUnit c A))

/-- The localization maps are the algebra maps. -/
private theorem toLocalization_app_apply (A : EtaleNeighborhood p) (x : (A.left.obj : Type u)) :
    ((toLocalization p).app A).hom x = algebraMap _ (Localization.AtPrime A.prime) x := rfl

/-- The extended leg restricts to the given leg on `S`. -/
private theorem localizedLeg_fac (c : Cocone (forget p)) (A : EtaleNeighborhood p) :
    (toLocalization p).app A ≫ localizedLeg c A = c.ι.app A := by
  ext x
  rw [CommAlgCat.hom_comp, AlgHom.comp_apply, toLocalization_app_apply]
  exact IsLocalization.lift_eq (S := Localization.AtPrime A.prime) (cocone_isUnit c A) x

/-- A cocone over the étale neighborhoods, extended along the localizations `S → S_q`. -/
private noncomputable abbrev localizedCocone (c : Cocone (forget p)) :
    Cocone (localization p) where
  pt := c.pt
  ι.app := localizedLeg c
  ι.naturality A B f := localization_hom_ext A <| by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    rw [← Category.assoc, ← (toLocalization p).naturality, Category.assoc, localizedLeg_fac,
      localizedLeg_fac]
    exact c.w f

/-- Extending a colimit cocone along the localizations gives a colimit cocone. -/
private noncomputable def isColimitLocalizedCocone {c : Cocone (forget p)} (hc : IsColimit c) :
    IsColimit (localizedCocone c) where
  desc s := hc.desc ((Cocone.precompose (toLocalization p)).obj s)
  fac s A := localization_hom_ext A <| by
    rw [← Category.assoc]
    exact (congrArg (· ≫ _) (localizedLeg_fac c A)).trans
      (hc.fac ((Cocone.precompose (toLocalization p)).obj s) A)
  uniq s m hm := hc.hom_ext fun A => by
    rw [hc.fac, ← localizedLeg_fac c A, Category.assoc]
    exact congrArg ((toLocalization p).app A ≫ ·) (hm A)

end Ideal.EtaleNeighborhood

namespace IsLocalRing.IsHenselization

open Ideal

variable {R : Type u} [CommRing R] {p : Ideal R} [p.IsPrime] {Rh : Type u} [CommRing Rh]
  [IsLocalRing Rh] [Algebra R Rh] [Algebra (Localization.AtPrime p) Rh]
  [IsScalarTower R (Localization.AtPrime p) Rh]
  [IsHenselization (Localization.AtPrime p) (ResidueField (Localization.AtPrime p)) Rh]
  [IsLocalHom (algebraMap (Localization.AtPrime p) Rh)]

omit [IsLocalRing Rh] [IsHenselization (Localization.AtPrime p)
  (ResidueField (Localization.AtPrime p)) Rh] in
/-- The residue field map `κ(p) → κ(Rh)` is compatible with the structure maps from `R`. -/
private theorem residueField_map_algebraMap [IsLocalRing Rh] (r : R) :
    ResidueField.map (algebraMap (Localization.AtPrime p) Rh) (algebraMap R p.ResidueField r) =
      algebraMap R (ResidueField Rh) r := by
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime p) p.ResidueField,
    ResidueField.algebraMap_eq, ResidueField.map_residue, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R Rh (ResidueField Rh), ResidueField.algebraMap_eq]

variable (Rh) in
/-- The augmentation of an étale neighborhood followed by `κ(p) → κ(Rh)`. -/
private noncomputable abbrev residueLift (A : EtaleNeighborhood p) :
    (A.left.obj : Type u) →ₐ[R] ResidueField Rh :=
  { toRingHom := (ResidueField.map (algebraMap (Localization.AtPrime p) Rh)).comp
      A.hom.hom.toRingHom
    commutes' := fun r =>
      (congrArg (ResidueField.map _) (A.hom.hom.commutes r)).trans (residueField_map_algebraMap r) }

/-- The canonical map from an étale neighborhood to a henselization. -/
private theorem existsUnique_leg (A : EtaleNeighborhood p) :
    ∃! f : (A.left.obj : Type u) →ₐ[R] Rh, ∀ x, residue Rh (f x) = residueLift Rh A x :=
  have := henselian (R := Localization.AtPrime p) (L := ResidueField (Localization.AtPrime p))
    (Rh := Rh)
  HenselianLocalRing.existsUnique_algHom_residue_of_etale (residueLift Rh A)

omit [IsLocalRing Rh] [IsHenselization (Localization.AtPrime p)
  (ResidueField (Localization.AtPrime p)) Rh] in
/-- Unfolding `residueLift`. -/
private theorem residueLift_apply [IsLocalRing Rh] (A : EtaleNeighborhood p)
    (x : (A.left.obj : Type u)) :
    residueLift Rh A x = ResidueField.map (algebraMap (Localization.AtPrime p) Rh) (A.hom.hom x) :=
  rfl

variable (p Rh) in
/-- The canonical map `S → Rh` of an étale neighborhood `(S, q)`: the unique `R`-algebra map
inducing `κ(q) = κ(p) ≅ κ(Rh)` on residue fields. -/
private noncomputable def leg (A : EtaleNeighborhood p) : (A.left.obj : Type u) →ₐ[R] Rh :=
  (existsUnique_leg A).exists.choose

/-- The canonical map induces the residue field isomorphism. -/
private theorem residue_leg (A : EtaleNeighborhood p) (x : (A.left.obj : Type u)) :
    residue Rh (leg p Rh A x) = residueLift Rh A x :=
  (existsUnique_leg A).exists.choose_spec x

/-- The canonical map is the only map inducing the residue field isomorphism. -/
private theorem eq_leg {A : EtaleNeighborhood p} (f : (A.left.obj : Type u) →ₐ[R] Rh)
    (hf : ∀ x, residue Rh (f x) = residueLift Rh A x) : f = leg p Rh A :=
  (existsUnique_leg A).unique hf (residue_leg A)

/-- The canonical maps are compatible with morphisms of étale neighborhoods. -/
private theorem leg_comp_map {A B : EtaleNeighborhood p} (h : A ⟶ B) :
    (leg p Rh B).comp (EtaleNeighborhood.map h) = leg p Rh A :=
  eq_leg _ fun x => by
    rw [AlgHom.comp_apply, residue_leg, residueLift_apply, residueLift_apply,
      EtaleNeighborhood.hom_map]

variable (p Rh) in
/-- The canonical cocone of the étale neighborhoods over `Rh`. -/
private noncomputable def canonicalι :
    EtaleNeighborhood.forget p ⟶ (Functor.const _).obj (CommAlgCat.of R Rh) where
  app A := CommAlgCat.ofHom (leg p Rh A)
  naturality _ _ h := by
    ext x
    exact AlgHom.congr_fun (leg_comp_map (Rh := Rh) h) x

omit [IsLocalRing Rh] [IsHenselization (Localization.AtPrime p)
  (ResidueField (Localization.AtPrime p)) Rh]
  [IsLocalHom (algebraMap (Localization.AtPrime p) Rh)] in
/-- The inverse `Rh → κ(Rh) ≅ κ(p)` of the residue field isomorphism, as an `R`-algebra map. -/
private theorem exists_aug [IsLocalRing Rh] [IsLocalHom (algebraMap (Localization.AtPrime p) Rh)]
    (hbij : Function.Bijective (ResidueField.map (algebraMap (Localization.AtPrime p) Rh))) :
    ∃ aug : Rh →ₐ[R] p.ResidueField,
      ∀ y, ResidueField.map (algebraMap (Localization.AtPrime p) Rh) (aug y) = residue Rh y := by
  let e := RingEquiv.ofBijective _ hbij
  refine ⟨{ toRingHom := e.symm.toRingHom.comp (residue Rh), commutes' := fun r => ?_ },
    fun y => e.apply_symm_apply (residue Rh y)⟩
  refine e.injective ((e.apply_symm_apply _).trans ?_)
  rw [RingEquiv.ofBijective_apply, residueField_map_algebraMap,
    IsScalarTower.algebraMap_apply R Rh (ResidueField Rh), ResidueField.algebraMap_eq]

/-- The canonical cocone exhibits `Rh` as the colimit of the étale neighborhoods: this is Lemma
08HR on the stages of an ind-étale presentation of `Rh`, together with the finite presentability of
étale algebras. -/
@[sga "4 VIII 4.1" "more general"]
private theorem nonempty_isColimit_canonical :
    Nonempty (IsColimit (Cocone.mk _ (canonicalι p Rh))) := by
  obtain ⟨aug, haug⟩ := exists_aug (p := p) (Rh := Rh) residueField_map_bijective
  obtain ⟨J, _, _, pres, hpres⟩ := CommAlgCat.ind_etale_comp
    (CommAlgCat.ind_etale_atPrime R (Localization.AtPrime p) p)
    (ind_etale_of_universe_le (R := Localization.AtPrime p)
      (L := ResidueField (Localization.AtPrime p)) (Rh := Rh))
  let obj (j : J) : EtaleNeighborhood p := CostructuredArrow.mk (Y := ⟨pres.diag.obj j, hpres j⟩)
    (CommAlgCat.ofHom (aug.comp (pres.ι.app j).hom))
  have hstage (j : J) : (canonicalι p Rh).app (obj j) = pres.ι.app j := by
    refine CommAlgCat.hom_ext (eq_leg _ fun x => ?_).symm
    rw [residueLift_apply]
    exact (haug _).symm
  let mapj {i j : J} (g : i ⟶ j) : obj i ⟶ obj j :=
    CostructuredArrow.homMk (ObjectProperty.homMk (pres.diag.map g))
      (CommAlgCat.hom_ext (AlgHom.ext fun x =>
        congrArg aug (ConcreteCategory.congr_hom (pres.w g) x)))
  let d (s : Cocone (EtaleNeighborhood.forget p)) : Cocone pres.diag :=
    { pt := s.pt
      ι := { app j := s.ι.app (obj j), naturality i j g := s.w (mapj g) } }
  refine ⟨{ desc s := pres.isColimit.desc (d s), fac s A := ?_, uniq s m hm := ?_ }⟩
  · have : IsFinitelyPresentable.{u} ((EtaleNeighborhood.forget p).obj A) :=
      CommAlgCat.isFinitelyPresentable_of_etale A.left.obj
    obtain ⟨j, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit pres.isColimit
      ((canonicalι p Rh).app A)
    have hgx (x : (A.left.obj : Type u)) : (pres.ι.app j).hom (g.hom x) = leg p Rh A x :=
      ConcreteCategory.congr_hom hg x
    let a : A ⟶ obj j := CostructuredArrow.homMk (ObjectProperty.homMk g)
      (CommAlgCat.hom_ext (AlgHom.ext fun x => (residueField_map_bijective (Rh := Rh)).1 (by
        rw [CommAlgCat.hom_comp, AlgHom.comp_apply, CostructuredArrow.mk_hom_eq_self,
          CommAlgCat.hom_ofHom, AlgHom.comp_apply, haug, ObjectProperty.ι_map]
        exact (congrArg (residue Rh) (hgx x)).trans ((residue_leg A x).trans
          (residueLift_apply A x)))))
    rw [← hg, Category.assoc, pres.isColimit.fac]
    exact s.w a
  · exact pres.isColimit.hom_ext fun j => by rw [pres.isColimit.fac, ← hstage]; exact hm (obj j)

variable (p Rh) in
/-- **The henselization as a colimit of étale neighborhoods** (Stacks 04GV). Let `p` be a prime of
`R` and let `Rh` be a henselization of `R_p`. The category of étale neighborhoods `(S, q)` of `p`
with `κ(q) = κ(p)` is filtered, and `Rh` is canonically the colimit of the algebras `S` and also of
the local rings `S_q`. The canonical maps `S → Rh` are the unique `R`-algebra maps inducing
`κ(q) = κ(p) ≅ κ(Rh)` on residue fields, and the maps `S_q → Rh` extend them. -/
@[stacks 04GV "Étale neighborhoods `(S, q)` with `κ(p) = κ(q)` are étale `R`-algebras with an
augmentation to `κ(p)`, whose kernel is `q`. `canonically` is the characterization of the colimit
maps `S → (R_p)^h`: the unique family inducing the identity of `κ(p) = κ((R_p)^h)` on residue
fields; the maps `S_q → (R_p)^h` are pinned by extending them along `S → S_q`. The henselization is
`IsHenselization` with residue field `κ(p)`.", sga "4 VIII 4.1" "more general"]
theorem isFiltered_etaleNeighborhood_and_isColimit :
    IsFiltered (EtaleNeighborhood p) ∧
      ∃ ι : EtaleNeighborhood.forget p ⟶ (Functor.const _).obj (CommAlgCat.of R Rh),
        (∀ A x, residue Rh ((ι.app A).hom x) =
          ResidueField.map (algebraMap (Localization.AtPrime p) Rh) (A.hom.hom x)) ∧
        (∀ ι' : EtaleNeighborhood.forget p ⟶ (Functor.const _).obj (CommAlgCat.of R Rh),
          (∀ A x, residue Rh ((ι'.app A).hom x) =
            ResidueField.map (algebraMap (Localization.AtPrime p) Rh) (A.hom.hom x)) → ι' = ι) ∧
        Nonempty (IsColimit (Cocone.mk _ ι)) ∧
        ∃ ιLoc : EtaleNeighborhood.localization p ⟶ (Functor.const _).obj (CommAlgCat.of R Rh),
          (∀ A, (EtaleNeighborhood.toLocalization p).app A ≫ ιLoc.app A = ι.app A) ∧
          Nonempty (IsColimit (Cocone.mk _ ιLoc)) := by
  obtain ⟨hc⟩ := nonempty_isColimit_canonical (p := p) (Rh := Rh)
  exact ⟨CommAlgCat.isFiltered_costructuredArrow_etale R p.ResidueField, canonicalι p Rh,
    fun A x => residue_leg A x, fun ι' h => NatTrans.ext <| funext fun A =>
      CommAlgCat.hom_ext (eq_leg (Rh := Rh) (ι'.app A).hom (h A)), ⟨hc⟩,
    (EtaleNeighborhood.localizedCocone (Cocone.mk _ (canonicalι p Rh))).ι,
    EtaleNeighborhood.localizedLeg_fac _, ⟨EtaleNeighborhood.isColimitLocalizedCocone hc⟩⟩

end IsLocalRing.IsHenselization
