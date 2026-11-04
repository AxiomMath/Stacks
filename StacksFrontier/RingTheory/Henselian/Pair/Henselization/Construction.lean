module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import StacksFrontier.Algebra.Category.CommAlgCat.FilteredColimits
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Unramified.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Henselian.AbsolutelyIntegrallyClosed
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.RingTheory.Flat.Nilpotent
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.Pair.Limits
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Ideal.SmulTop

/-!
# Henselization of a pair: construction

The inclusion of henselian pairs into pairs has a left adjoint `(A, I) ↦ (A^h, I^h)`. This file
constructs `A^h` as the filtered colimit of the étale `A`-algebras equipped with an augmentation
to `A / I`. It sets up the index category of such pairs, shows that it is essentially small and
filtered, defines the henselization as the colimit, and constructs the augmentation `A^h → A / I`
together with the maps from each stage to a henselian pair under `(A, I)`.

The henselian property and the universal property of this construction are proved in
`StacksFrontier.RingTheory.Henselian.Pair.Henselization.UniversalProperty`.

## Main definitions

* `henselization`: the henselization of a pair, as a colimit of étale algebras.
* `ind_henselization`: the henselization is a filtered colimit of étale algebras.

## References

* [Stacks: Tag 0EM7](https://stacks.math.columbia.edu/tag/0EM7)
-/

-- Not `@[expose]`: the public constructions in this file (`henselization` and friends) are
-- defined in terms of private auxiliary diagrams, so their bodies must stay unexposed.
public section

open CategoryTheory CategoryTheory.Limits IsLocalRing Polynomial
open scoped TensorProduct
open Stacks.Henselization.EtaleColimit

universe u v w

section

section

variable (R : Type u) [CommRing R] (I : Ideal R)

/-! ### The index category of pairs -/

attribute [local instance] etale_essentiallySmall

/-- The category of étale `R`-algebras equipped with an augmentation to `R ⧸ I`. -/
private abbrev Pairs : Type (u + 1) :=
  CostructuredArrow (CommAlgCat.etale.{u} R).ι (CommAlgCat.of R (R ⧸ I))

/-- The algebra underlying a pair is étale over `R`. -/
private theorem Pairs.etale (A : Pairs R I) : Algebra.Etale R (A.left.obj : Type u) :=
  A.left.property

attribute [local instance] Pairs.etale

/-- The category of pairs is essentially `u`-small. -/
private theorem essentiallySmall_pairs : EssentiallySmall.{u} (Pairs R I) := inferInstance

attribute [local instance] essentiallySmall_pairs

/-- The algebra `R` augmented by its quotient map to `R ⧸ I`. -/
private noncomputable def Pairs.unit : Pairs R I :=
  CostructuredArrow.mk (Y := ⟨CommAlgCat.of R R, inferInstance⟩)
    (CommAlgCat.ofHom (Algebra.ofId R (R ⧸ I)))

/-- The `R`-algebra map underlying a morphism of pairs. -/
private noncomputable abbrev Pairs.map {A B : Pairs R I} (h : A ⟶ B) :
    (A.left.obj : Type u) →ₐ[R] (B.left.obj : Type u) :=
  ((CommAlgCat.etale.{u} R).ι.map h.left).hom

/-- A morphism of pairs is determined by its underlying algebra map. -/
private theorem Pairs.hom_ext {A B : Pairs R I} (u v : A ⟶ B)
    (h : Pairs.map R I u = Pairs.map R I v) : u = v := by
  have h' : (CommAlgCat.etale.{u} R).ι.map u.left = (CommAlgCat.etale.{u} R).ι.map v.left :=
    CommAlgCat.hom_ext h
  exact CostructuredArrow.hom_ext _ _ ((CommAlgCat.etale.{u} R).ι.map_injective h')

/-- Underlying algebra maps compose. -/
private theorem Pairs.map_comp {A B C : Pairs R I} (u : A ⟶ B) (v : B ⟶ C)
    (x : (A.left.obj : Type u)) :
    Pairs.map R I (u ≫ v) x = Pairs.map R I v (Pairs.map R I u x) :=
  ConcreteCategory.congr_hom ((CommAlgCat.etale.{u} R).ι.map_comp u.left v.left) x

/-- A morphism of pairs is compatible with the augmentations. -/
private theorem Pairs.aug_map {A B : Pairs R I} (u : A ⟶ B) (x : (A.left.obj : Type u)) :
    B.hom.hom (Pairs.map R I u x) = A.hom.hom x :=
  ConcreteCategory.congr_hom (CostructuredArrow.w u) x

/-- If the augmentation of `g` is nonzero in the pair `A`, then `A` has a morphism to the pair
`(S[1/g], α)`: the localization is again étale over `R`, and the augmentation extends to it because
it sends `g` to a unit. In the new pair `g` becomes invertible. -/
private theorem Pairs.exists_away (A : Pairs R I) (g : (A.left.obj : Type u))
    (hg : IsUnit (A.hom.hom g)) :
    ∃ (C : Pairs R I) (h : A ⟶ C), IsUnit (Pairs.map R I h g) := by
  have hEt' : Algebra.Etale R (Localization.Away g) :=
    Algebra.Etale.comp R (A.left.obj : Type u) (Localization.Away g)
  have hunits : ∀ y : Submonoid.powers g, IsUnit (A.hom.hom (y : (A.left.obj : Type u))) := by
    intro y
    obtain ⟨n, hn⟩ := y.2
    simp only [← hn, map_pow]
    exact hg.pow n
  obtain ⟨aug, haug⟩ : ∃ aug : Localization.Away g →ₐ[R] R ⧸ I,
      ∀ x : (A.left.obj : Type u),
        aug (algebraMap (A.left.obj : Type u) (Localization.Away g) x) = A.hom.hom x :=
    ⟨IsLocalization.liftAlgHom (M := Submonoid.powers g) (S := Localization.Away g)
      (f := A.hom.hom) hunits, fun x => IsLocalization.lift_eq hunits x⟩
  refine ⟨CostructuredArrow.mk
      (Y := ⟨CommAlgCat.of R (Localization.Away g), hEt'⟩) (CommAlgCat.ofHom aug), ?_⟩
  refine ⟨CostructuredArrow.homMk (ObjectProperty.homMk
      (CommAlgCat.ofHom (IsScalarTower.toAlgHom R (A.left.obj : Type u)
        (Localization.Away g))))
      (CommAlgCat.hom_ext (AlgHom.ext haug)), ?_⟩
  show IsUnit ((IsScalarTower.toAlgHom R (A.left.obj : Type u) (Localization.Away g)) g)
  exact IsLocalization.map_units (M := Submonoid.powers g) (Localization.Away g)
    ⟨g, Submonoid.mem_powers g⟩

/-- Any two pairs map to a common pair, namely their tensor product over `R` augmented by the
product of the two augmentations. -/
private theorem Pairs.cocone_objs (A B : Pairs R I) :
    ∃ (C : Pairs R I) (_ : A ⟶ C) (_ : B ⟶ C), True := by
  have hT : Algebra.Etale R (TensorProduct R (A.left.obj : Type u) (B.left.obj : Type u)) :=
    Algebra.Etale.comp R (A.left.obj : Type u)
      (TensorProduct R (A.left.obj : Type u) (B.left.obj : Type u))
  refine ⟨CostructuredArrow.mk (Y := ⟨CommAlgCat.of R
      (TensorProduct R (A.left.obj : Type u) (B.left.obj : Type u)), hT⟩)
      (CommAlgCat.ofHom (Algebra.TensorProduct.lift A.hom.hom B.hom.hom
        fun _ _ ↦ Commute.all _ _)),
    CostructuredArrow.homMk (ObjectProperty.homMk
      (CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft (R := R) (S := R)))) ?_,
    CostructuredArrow.homMk (ObjectProperty.homMk
      (CommAlgCat.ofHom (Algebra.TensorProduct.includeRight (R := R)))) ?_, trivial⟩
  · ext x; simp
  · ext x; simp

/-- For an étale `R`-algebra `S` and `R`-algebra maps `f g : S → T` which agree after composing
with `φ`, the image under `φ` of the image of the diagonal idempotent `e` under `f ⊗ g` is `1`. -/
private theorem map_lift_elem_eq_one {S T U : Type*} [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra R U] [Algebra.Etale R S]
    (f g : S →ₐ[R] T) (φ : T →ₐ[R] U) (h : φ.comp f = φ.comp g) :
    φ (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
      (Algebra.FormallyUnramified.elem R S)) = 1 := by
  have hcomp : φ.comp (Algebra.TensorProduct.lift f g fun _ _ => Commute.all _ _) =
      (φ.comp f).comp (Algebra.TensorProduct.lmul' R) := by
    refine Algebra.TensorProduct.ext' fun x y => ?_
    simpa using congrArg (φ (f x) * ·) (AlgHom.congr_fun h.symm y)
  rw [← AlgHom.comp_apply, hcomp, AlgHom.comp_apply,
    show (Algebra.TensorProduct.lmul' R) (Algebra.FormallyUnramified.elem R S) = 1 from
      Algebra.FormallyUnramified.lmul_elem, map_one]

/-- For an étale `R`-algebra `S`, the maps `f g : S → T` agree after multiplying by the image of
the diagonal idempotent under `f ⊗ g`. -/
private theorem mul_lift_elem_eq {S T : Type*} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra.Etale R S] (f g : S →ₐ[R] T) (x : S) :
    f x * Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
        (Algebra.FormallyUnramified.elem R S) =
      g x * Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
        (Algebra.FormallyUnramified.elem R S) := by
  simpa [mul_comm] using
    congrArg (Algebra.TensorProduct.lift f g fun _ _ => Commute.all _ _)
      (Algebra.FormallyUnramified.one_tmul_mul_elem (R := R) (S := S) x).symm

/-- Any two parallel morphisms of pairs are equalized after a further morphism. -/
private theorem Pairs.cocone_maps {A B : Pairs R I} (f g : A ⟶ B) :
    ∃ (C : Pairs R I) (h : B ⟶ C), f ≫ h = g ≫ h := by
  set θ := Algebra.TensorProduct.lift (Pairs.map R I f) (Pairs.map R I g)
    (fun _ _ => Commute.all _ _) with hθ
  set e := Algebra.FormallyUnramified.elem R (A.left.obj : Type u) with he
  have haug : B.hom.hom (θ e) = 1 :=
    map_lift_elem_eq_one R _ _ B.hom.hom
      (AlgHom.ext fun x => (Pairs.aug_map R I f x).trans (Pairs.aug_map R I g x).symm)
  obtain ⟨C, h, hu⟩ := Pairs.exists_away R I B (θ e) (by rw [haug]; exact isUnit_one)
  refine ⟨C, h, Pairs.hom_ext R I _ _ (AlgHom.ext fun x => ?_)⟩
  have key : Pairs.map R I f x * θ e = Pairs.map R I g x * θ e :=
    mul_lift_elem_eq R _ _ x
  rw [Pairs.map_comp, Pairs.map_comp]
  refine hu.mul_right_cancel ?_
  rw [← map_mul, ← map_mul, key]

/-- The category of pairs is filtered. -/
private theorem isFiltered_pairs : IsFiltered (Pairs R I) :=
  have : IsFilteredOrEmpty (Pairs R I) :=
    { cocone_objs := fun A B ↦ Pairs.cocone_objs R I A B
      cocone_maps := fun {_ _} f g ↦ Pairs.cocone_maps R I f g }
  { nonempty := ⟨Pairs.unit R I⟩ }

attribute [local instance] isFiltered_pairs

/-! ### The colimit -/

/-- A `u`-small model of the category of pairs. -/
private abbrev Index : Type u := SmallModel (Pairs R I)

/-- The diagram of étale `R`-algebras indexed by the small model of the category of pairs. -/
private noncomputable def diagram : Index R I ⥤ CommAlgCat.{u} R :=
  (equivSmallModel (Pairs R I)).inverse ⋙
    CostructuredArrow.proj (CommAlgCat.etale.{u} R).ι (CommAlgCat.of R (R ⧸ I)) ⋙
      (CommAlgCat.etale.{u} R).ι

/-- The **henselization** of `R`: the colimit of the diagram of pairs. -/
@[ega "IV 18.6.5" "more general",
  sga "3 X 4.4",
  sga "4 VIII 4.1",
  sga "4 XII 6.13",
  sga "4 XIX 1.1" "more general",
  sga "4 XIX 1.5",
  sga "4 XV 2.3" "more general",
  sga "7 XIV 2.2",
  sga "7 XV 1.1.3",
  sga "7 XV 3.3.3" "partial"]
public noncomputable def henselization : CommAlgCat.{u} R := by
  exact colimit (diagram R I)

/-- The henselization is a filtered colimit of étale `R`-algebras. -/
public theorem ind_henselization :
    (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R (henselization R I : Type u)) :=
  ⟨Index R I, inferInstance, IsFiltered.of_equivalence (equivSmallModel (Pairs R I)),
    { diag := diagram R I
      ι := (colimit.cocone (diagram R I)).ι
      isColimit := colimit.isColimit _ },
    fun i ↦ Pairs.etale R I ((equivSmallModel (Pairs R I)).inverse.obj i)⟩

private abbrev pairsFunctor : Pairs R I ⥤ CommAlgCat.{u} R :=
  CostructuredArrow.proj (CommAlgCat.etale.{u} R).ι (CommAlgCat.of R (R ⧸ I)) ⋙
    (CommAlgCat.etale.{u} R).ι

/-- Reindexing the diagram along the equivalence with the small model identifies `pairsFunctor`
with the diagram, up to the unit of the equivalence. -/
private noncomputable def pairsIsoDiagram :
    pairsFunctor R I ≅ (equivSmallModel (Pairs R I)).functor ⋙ diagram R I :=
  (Functor.leftUnitor (pairsFunctor R I)).symm ≪≫
    Functor.isoWhiskerRight (equivSmallModel (Pairs R I)).unitIso (pairsFunctor R I) ≪≫
      Functor.associator _ _ _

/-- The colimit cocone of the henselization, indexed by the category of pairs itself rather than
by its small model. -/
private noncomputable def pairsCocone : Cocone (pairsFunctor R I) :=
  (Cocone.precompose (pairsIsoDiagram R I).hom).obj
    (Cocone.whisker (equivSmallModel (Pairs R I)).functor (colimit.cocone (diagram R I)))

/-- The cocone over the category of pairs is a colimit cocone. -/
private noncomputable def pairsCoconeIsColimit : IsColimit (pairsCocone R I) :=
  (IsColimit.precomposeHomEquiv (pairsIsoDiagram R I) _).symm
    (IsColimit.whiskerEquivalence (colimit.isColimit (diagram R I)) (equivSmallModel (Pairs R I)))

/-- The `R`-algebra map from a pair into `R^h`, i.e. the structure map of the colimit cocone. -/
private noncomputable abbrev stageHom (A : Pairs R I) :
    (A.left.obj : Type u) →ₐ[R] (henselization R I : Type u) := ((pairsCocone R I).ι.app A).hom

/-- A morphism of pairs does not change the element of `R^h` that a point of a pair determines. -/
private theorem stageHom_map {A B : Pairs R I} (u : A ⟶ B) (y : (A.left.obj : Type u)) :
    stageHom R I B (Pairs.map R I u y) = stageHom R I A y :=
  ConcreteCategory.congr_hom ((pairsCocone R I).w u) y

/-- Every element of `R^h` comes from a pair. -/
private theorem exists_stage (x : (henselization R I : Type u)) :
    ∃ (A : Pairs R I) (y : (A.left.obj : Type u)), stageHom R I A y = x :=
  CommAlgCat.exists_app_eq (pairsCoconeIsColimit R I) x

/-- The cocone of augmentations: every pair comes with an `R`-algebra map to `R ⧸ I`,
compatibly with morphisms of pairs. -/
private noncomputable def augPairsCocone : Cocone (pairsFunctor R I) where
  pt := CommAlgCat.of R (R ⧸ I)
  ι := { app := fun A => A.hom
         naturality := fun A B u => by simpa using CostructuredArrow.w u }

/-- The **augmentation** `R^h → R ⧸ I`, induced by the augmentations of the pairs. -/
private noncomputable def aug : (henselization R I : Type u) →ₐ[R] R ⧸ I :=
  ((pairsCoconeIsColimit R I).desc (augPairsCocone R I)).hom

/-- The augmentation of `R^h` restricts on each stage to the augmentation of that pair. -/
private theorem aug_stageHom (A : Pairs R I) (y : (A.left.obj : Type u)) :
    aug R I (stageHom R I A y) = A.hom.hom y :=
  ConcreteCategory.congr_hom ((pairsCoconeIsColimit R I).fac (augPairsCocone R I) A) y

/-- The augmentation composed with `R → R^h` is the quotient map of `R`. -/
private theorem aug_algebraMap (r : R) :
    aug R I (algebraMap R (henselization R I : Type u) r) = Ideal.Quotient.mk I r :=
  (aug R I).commutes r

/-- An element in the kernel of the augmentation of a pair is killed by an element which the
augmentation sends to one. -/
private theorem Pairs.exists_annihilator (A : Pairs R I)
    (y : (A.left.obj : Type u)) (hy : A.hom.hom y = 0) :
    ∃ g : (A.left.obj : Type u), A.hom.hom g = 1 ∧
      g * y ∈ I.map (algebraMap R (A.left.obj : Type u)) := by
  let S := (A.left.obj : Type u)
  let J : Ideal S := I.map (algebraMap R S)
  let q : S →ₐ[R] S ⧸ J := Ideal.Quotient.mkₐ R J
  have hJ : J ≤ RingHom.ker A.hom.hom.toRingHom := by
    show I.map (algebraMap R S) ≤ RingHom.ker A.hom.hom.toRingHom
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    show A.hom.hom (algebraMap R S r) = 0
    convert (A.hom.hom.commutes r).trans ((Ideal.Quotient.eq_zero_iff_mem).2 hr) using 1
    rfl
  let αbar : S ⧸ J →ₐ[R] R ⧸ I :=
    Ideal.Quotient.liftₐ J A.hom.hom (fun a ha => RingHom.mem_ker.mp (hJ ha))
  let ρ : R ⧸ I →ₐ[R] S ⧸ J :=
    Ideal.quotientMapₐ J (Algebra.ofId R S) I.le_comap_map
  let θ : S ⊗[R] S →ₐ[R] S ⧸ J :=
    Algebra.TensorProduct.lift q (ρ.comp A.hom.hom) (fun _ _ => Commute.all _ _)
  let e := Algebra.FormallyUnramified.elem R S
  have hαbarρ : αbar.comp ρ = AlgHom.id R (R ⧸ I) := by
    apply AlgHom.ext
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (αbar.comp ρ).commutes r
  have hαbarq : αbar.comp q = A.hom.hom := Ideal.Quotient.liftₐ_comp J A.hom.hom _
  have hone : αbar (θ e) = 1 :=
    map_lift_elem_eq_one R q (ρ.comp A.hom.hom) αbar
      (by rw [hαbarq, ← AlgHom.comp_assoc, hαbarρ, AlgHom.id_comp])
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (θ e)
  change q g = θ e at hg
  have hgα : A.hom.hom g = 1 := by rw [← hαbarq, AlgHom.comp_apply, hg, hone]
  have hmul : q (g * y) = 0 := by
    have h : q y * θ e = ρ (A.hom.hom y) * θ e := mul_lift_elem_eq R q (ρ.comp A.hom.hom) y
    rw [map_mul, hg, mul_comm, h, hy, map_zero, zero_mul]
  exact ⟨g, hgα, (Ideal.Quotient.eq_zero_iff_mem).mp hmul⟩

/-- A kernel element of a stage augmentation enters the extended ideal after passing to a
later étale neighborhood. -/
private theorem Pairs.exists_mem_map (A : Pairs R I) (y : (A.left.obj : Type u))
    (hy : A.hom.hom y = 0) :
    ∃ (C : Pairs R I) (h : A ⟶ C),
      Pairs.map R I h y ∈ I.map (algebraMap R (C.left.obj : Type u)) := by
  obtain ⟨g, hg, hgy⟩ := Pairs.exists_annihilator R I A y hy
  obtain ⟨C, h, hu⟩ := Pairs.exists_away R I A g (by rw [hg]; exact isUnit_one)
  refine ⟨C, h, (Ideal.unit_mul_mem_iff_mem _ hu).1 ?_⟩
  rw [← map_mul]
  exact Stacks.Henselization.EtaleColimit.mem_map_of_algHom R (Pairs.map R I h) hgy

/-- Elements of the colimit whose augmentation is a unit become units after a suitable
localization of a stage. -/
private theorem isUnit_iff_aug_isUnit (x : (henselization R I : Type u)) :
    IsUnit x ↔ IsUnit (aug R I x) := by
  refine ⟨fun hx => hx.map (aug R I), fun hx => ?_⟩
  obtain ⟨A, y, rfl⟩ := exists_stage R I x
  rw [aug_stageHom] at hx
  obtain ⟨C, h, hu⟩ := Pairs.exists_away R I A y hx
  rw [← stageHom_map R I h y]
  exact hu.map (stageHom R I C)

/-- The quotient of the henselization by the extended ideal is the original quotient. -/
private theorem ker_aug :
    RingHom.ker (aug R I).toRingHom = I.map (algebraMap R (henselization R I : Type u)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨A, y, rfl⟩ := exists_stage R I x
    change aug R I (stageHom R I A y) = 0 at hx
    rw [aug_stageHom] at hx
    obtain ⟨C, h, hy⟩ := Pairs.exists_mem_map R I A y hx
    rw [← stageHom_map R I h y]
    exact Stacks.Henselization.EtaleColimit.mem_map_of_algHom R (stageHom R I C) hy
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    show aug R I (algebraMap R (henselization R I : Type u) r) = 0
    rw [aug_algebraMap]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 hr

/-- The extended ideal lies in the Jacobson radical. -/
private theorem map_le_jacobson :
    I.map (algebraMap R (henselization R I : Type u)) ≤
      (⊥ : Ideal (henselization R I : Type u)).jacobson := by
  rw [← ker_aug R I]
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  apply (isUnit_iff_aug_isUnit R I _).2
  change aug R I x = 0 at hx
  simp [hx]

/-- Maps from an étale algebra to a Zariski pair are determined by their reductions modulo
the ideal. -/
private theorem unique_etale_map_of_quotient {S : Type u} {B : Type v}
    [CommRing S] [CommRing B] [Algebra R S] [Algebra.Etale R S] [Algebra R B]
    (J : Ideal B) (hJ : J ≤ (⊥ : Ideal B).jacobson)
    (f g : S →ₐ[R] B)
    (hfg : (Ideal.Quotient.mkₐ R J).comp f = (Ideal.Quotient.mkₐ R J).comp g) :
    f = g := by
  have hunit : IsUnit (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
      (Algebra.FormallyUnramified.elem R S)) := by
    refine Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hJ ?_)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one]
    exact sub_eq_zero.2 (map_lift_elem_eq_one R f g (Ideal.Quotient.mkₐ R J) hfg)
  exact AlgHom.ext fun x => hunit.mul_right_cancel (mul_lift_elem_eq R f g x)

/-- The étale lifting criterion for a henselian target pair produces a map from each étale
neighborhood of `R/I` to the target, with prescribed reduction. -/
private theorem Pairs.exists_map_to_henselian {B : Type v} [CommRing B] [Algebra R B]
    (J : Ideal B) (hB : HenselianPair B J)
    (hIJ : I ≤ J.comap (algebraMap R B)) (A : Pairs R I) :
    ∃ g : (A.left.obj : Type u) →ₐ[R] B,
      (Ideal.Quotient.mkₐ R J).comp g =
        (Ideal.quotientMapₐ J (Algebra.ofId R B) hIJ).comp A.hom.hom := by
  let S := (A.left.obj : Type u)
  let β : R ⧸ I →ₐ[R] B ⧸ J :=
    Ideal.quotientMapₐ J (Algebra.ofId R B) hIJ
  let q : B →ₐ[R] B ⧸ J := Ideal.Quotient.mkₐ R J
  let σR : B ⊗[R] S →ₐ[R] B ⧸ J :=
    Algebra.TensorProduct.lift q (β.comp A.hom.hom) (fun _ _ => Commute.all _ _)
  let σ : B ⊗[R] S →ₐ[B] B ⧸ J :=
    { σR.toRingHom with
      commutes' := fun b => by
        show σR (b ⊗ₜ[R] 1) = Ideal.Quotient.mk J b
        simp [σR, q, Algebra.TensorProduct.lift_tmul] }
  have hE : Algebra.Etale B (B ⊗[R] S) := Algebra.Etale.baseChange R S B
  have hLift := ((henselianPair_tfae B J).out 1 2).mp hB
  obtain ⟨τ, hτ⟩ := hLift (B ⊗[R] S) σ
  let g : S →ₐ[R] B :=
    (τ.restrictScalars R).comp (Algebra.TensorProduct.includeRight (R := R) (A := B))
  refine ⟨g, AlgHom.ext fun y => ?_⟩
  have h := congrArg (fun φ : B ⊗[R] S →ₐ[B] B ⧸ J => φ (1 ⊗ₜ[R] y)) hτ
  simpa [g, σ, σR, β, q, Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.includeRight_apply] using h

/-- Every stage element has the same class modulo the extended ideal as an element of `R`. -/
private theorem stage_sub_mem (A : Pairs R I) (y : (A.left.obj : Type u)) :
    ∃ r : R, A.hom.hom y = Ideal.Quotient.mk I r ∧
      stageHom R I A y - algebraMap R (henselization R I : Type u) r ∈
        I.map (algebraMap R (henselization R I : Type u)) := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (A.hom.hom y)
  refine ⟨r, hr.symm, ?_⟩
  rw [← ker_aug R I, RingHom.mem_ker]
  show aug R I (stageHom R I A y - algebraMap R (henselization R I : Type u) r) = 0
  rw [map_sub, aug_stageHom, aug_algebraMap, ← hr, sub_self]

/-- A map out of the colimit into a pair has its reduction on every stage fixed by the
augmentation. -/
private theorem map_stage_reduction {B : Type v} [CommRing B] [Algebra R B]
    (J : Ideal B) (hIJ : I ≤ J.comap (algebraMap R B))
    (g : (henselization R I : Type u) →ₐ[R] B) (A : Pairs R I) :
    (Ideal.Quotient.mkₐ R J).comp (g.comp (stageHom R I A)) =
      (Ideal.quotientMapₐ J (Algebra.ofId R B) hIJ).comp A.hom.hom := by
  apply AlgHom.ext
  intro y
  obtain ⟨r, hr, hmem⟩ := stage_sub_mem R I A y
  have hmap : g (stageHom R I A y) - algebraMap R B r ∈ J := by
    have hm := Stacks.Henselization.EtaleColimit.mem_map_of_algHom R g hmem
    exact (Ideal.map_le_iff_le_comap.mpr hIJ) (by
      simpa only [map_sub, g.commutes] using hm)
  show Ideal.Quotient.mk J (g (stageHom R I A y)) =
    (Ideal.quotientMapₐ J (Algebra.ofId R B) hIJ) (A.hom.hom y)
  let β : R ⧸ I →ₐ[R] B ⧸ J :=
    Ideal.quotientMapₐ J (Algebra.ofId R B) hIJ
  show Ideal.Quotient.mk J (g (stageHom R I A y)) = β (A.hom.hom y)
  rw [hr]
  have hb : β (Ideal.Quotient.mk I r) = Ideal.Quotient.mk J (algebraMap R B r) := by
    convert β.commutes r using 1 <;> rfl
  rw [hb]
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (Ideal.Quotient.eq_zero_iff_mem).2 hmap

/-- The uniquely determined map from a stage to a henselian target. -/
private noncomputable def Pairs.map_to_henselian {B : Type v} [CommRing B] [Algebra R B]
    (J : Ideal B) (hB : HenselianPair B J)
    (hIJ : I ≤ J.comap (algebraMap R B)) (A : Pairs R I) :
    (A.left.obj : Type u) →ₐ[R] B :=
  Classical.choose (Pairs.exists_map_to_henselian R I J hB hIJ A)

private theorem Pairs.map_to_henselian_spec {B : Type v} [CommRing B] [Algebra R B]
    (J : Ideal B) (hB : HenselianPair B J)
    (hIJ : I ≤ J.comap (algebraMap R B)) (A : Pairs R I) :
    (Ideal.Quotient.mkₐ R J).comp (Pairs.map_to_henselian R I J hB hIJ A) =
      (Ideal.quotientMapₐ J (Algebra.ofId R B) hIJ).comp A.hom.hom :=
  Classical.choose_spec (Pairs.exists_map_to_henselian R I J hB hIJ A)

/-- The stage maps commute with arrows of étale neighborhoods. -/
private theorem Pairs.map_to_henselian_natural {B : Type v} [CommRing B] [Algebra R B]
    (J : Ideal B) (hB : HenselianPair B J)
    (hIJ : I ≤ J.comap (algebraMap R B)) {A C : Pairs R I} (u : A ⟶ C) :
    (Pairs.map_to_henselian R I J hB hIJ C).comp (Pairs.map R I u) =
      Pairs.map_to_henselian R I J hB hIJ A := by
  apply unique_etale_map_of_quotient R J hB.1
  apply AlgHom.ext
  intro y
  have hC := AlgHom.congr_fun (Pairs.map_to_henselian_spec R I J hB hIJ C)
    (Pairs.map R I u y)
  have hA := AlgHom.congr_fun (Pairs.map_to_henselian_spec R I J hB hIJ A) y
  simp only [AlgHom.comp_apply] at hC hA ⊢
  rw [hC, Pairs.aug_map R I u y, hA]

end

end

end
