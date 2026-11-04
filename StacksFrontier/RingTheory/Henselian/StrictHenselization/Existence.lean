module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.Henselian
public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.Category.CommAlgCat.FilteredColimits
public import StacksFrontier.RingTheory.Henselian.Henselization.Existence

@[expose] public section

universe u v w

namespace Stacks.StrictHenselization.EtaleColimit
open Stacks.Henselization.EtaleColimit

/-!
# The étale colimit construction of the strict henselization

Let `(R, 𝔪, κ)` be a local ring and let `κ ⊆ κ^sep` be a separable algebraic closure. The strict
henselization is built as the colimit of the *category of triples*: an object is an étale
`R`-algebra `S` together with a prime `𝔮` of `S` lying over `𝔪` and an embedding
`α : κ(𝔮) → κ^sep` of extensions of `κ`, and a morphism `(S, 𝔮, α) → (S', 𝔮', α')` is an
`R`-algebra map `φ` with `φ⁻¹(𝔮') = 𝔮` compatibly with the embeddings.

## Implementation notes

*Triples are augmentations to `κ^sep`.* A prime `𝔮` of an `R`-algebra `S` lying over `𝔪` together
with an embedding `κ(𝔮) → κ^sep` over `κ` is the same datum as an `R`-algebra map
`α : S → κ^sep`: given `α`, its kernel is such a prime and `κ(ker α) → κ^sep` is the induced
embedding, and given `(𝔮, α)`, the composite `S → κ(𝔮) → κ^sep` is such an `α`. Under this
dictionary a morphism of triples is exactly a morphism of `R`-algebras over `κ^sep`. So the
category of triples is `CategoryTheory.CostructuredArrow` of the inclusion of the étale
`R`-algebras into `CommAlgCat R` over the object `κ^sep`, which is how it is spelled here; the
prime ideals never have to be carried around.

*The construction is run for an arbitrary augmentation field.* It is set up for an arbitrary field
`L` which is an `R`-algebra by a local ring map: `augColimit R L` is the colimit of the category of
étale `R`-algebras augmented to `L`, it is a local ring with maximal ideal `𝔪 · augColimit R L`, it
is henselian, and it is a filtered colimit of étale `R`-algebras. Taking `L = κ` gives the
henselization, taking `L = κ^sep` gives the strict henselization: the augmentation is surjective as
soon as `L` is separable algebraic over `κ` (`aug_surjective`).

*Smallness.* An étale algebra is of finite presentation, hence of finite type, so the étale
objects of `CommAlgCat R` form an essentially `u`-small object property
(`etale_essentiallySmall`, via `FGAlgCatSkeleton`). Since `CommAlgCat.{u} R` is locally `u`-small,
the category of triples is then essentially `u`-small, and the colimit may be taken over its small
model, which is what `ObjectProperty.ind.{u}` asks for.
-/


open CategoryTheory CategoryTheory.Limits IsLocalRing


/-! ### Primes of an étale algebra lying over the maximal ideal -/

section

variable (R : Type u) [CommRing R] [IsLocalRing R] {S : Type u} [CommRing S] [Algebra R S]

/-- The localization of an `R`-algebra at a prime lying over `𝔪` is a local `R`-algebra. -/
private theorem isLocalHom_algebraMap_atPrime (q : Ideal S) [q.IsPrime]
    [q.LiesOver (maximalIdeal R)] : IsLocalHom (algebraMap R (Localization.AtPrime q)) := by
  refine ((local_hom_TFAE (algebraMap R (Localization.AtPrime q))).out 4 1).1 fun r hr => ?_
  rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply R S (Localization.AtPrime q)]
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q _).2
    ((Ideal.mem_of_liesOver q (maximalIdeal R) r).1 hr)

/-- Let `S` be an étale `R`-algebra and `𝔮` a prime of `S` lying over `𝔪`. Then an element of `𝔮`
becomes a member of `𝔪 S` after multiplication by some `g ∉ 𝔮`. -/
@[sga "7 VIII 7.3.5.3" "partial"]
private theorem exists_mul_mem_map_maximalIdeal [Algebra.Etale R S] (q : Ideal S) [q.IsPrime]
    [q.LiesOver (maximalIdeal R)] {y : S} (hy : y ∈ q) :
    ∃ g ∉ q, g * y ∈ (maximalIdeal R).map (algebraMap R S) := by
  have := isLocalHom_algebraMap_atPrime R q
  have h : algebraMap S (Localization.AtPrime q) y ∈ maximalIdeal (Localization.AtPrime q) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q y).2 hy
  rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R),
    IsScalarTower.algebraMap_eq R S (Localization.AtPrime q), ← Ideal.map_map] at h
  exact (IsLocalization.algebraMap_mem_map_algebraMap_iff (M := q.primeCompl)
    (S := Localization.AtPrime q) _ _).1 h

end

/-! ### The index category of pairs -/

section

variable (R : Type u) [CommRing R] [IsLocalRing R] (L : Type u) [Field L] [Algebra R L]
  [IsLocalHom (algebraMap R L)]

attribute [local instance] etale_essentiallySmall

/-- For a field `L` which is an `R`-algebra by a local ring map, the kernel of `R → L` is the
maximal ideal of `R`. -/
private theorem algebraMap_eq_zero_iff (r : R) :
    algebraMap R L r = 0 ↔ r ∈ maximalIdeal R := by
  rw [← maximalIdeal_comap (algebraMap R L), Ideal.mem_comap, maximalIdeal_eq_bot, Ideal.mem_bot]

/-- The **category of pairs**: an étale `R`-algebra together with an augmentation to the field `L`,
i.e. an `R`-algebra map to `L`. -/
private abbrev Pairs : Type (u + 1) :=
  CostructuredArrow (CommAlgCat.etale.{u} R).ι (CommAlgCat.of R L)

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- The algebra underlying a pair is étale over `R`. -/
private theorem Pairs.etale (A : Pairs R L) : Algebra.Etale R (A.left.obj : Type u) :=
  A.left.property

attribute [local instance] Pairs.etale

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- The category of pairs is essentially `u`-small. -/
private theorem essentiallySmall_pairs : EssentiallySmall.{u} (Pairs R L) := inferInstance

attribute [local instance] essentiallySmall_pairs

/-- The `R`-algebra map underlying a morphism of pairs. -/
private noncomputable abbrev Pairs.map {A B : Pairs R L} (h : A ⟶ B) :
    (A.left.obj : Type u) →ₐ[R] (B.left.obj : Type u) :=
  ((CommAlgCat.etale.{u} R).ι.map h.left).hom

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- A morphism of pairs is determined by its underlying algebra map. -/
private theorem Pairs.hom_ext {A B : Pairs R L} (u v : A ⟶ B)
    (h : Pairs.map R L u = Pairs.map R L v) : u = v :=
  CostructuredArrow.hom_ext _ _
    ((CommAlgCat.etale.{u} R).ι.map_injective (CommAlgCat.hom_ext h))

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- Underlying algebra maps compose. -/
private theorem Pairs.map_comp {A B C : Pairs R L} (u : A ⟶ B) (v : B ⟶ C)
    (x : (A.left.obj : Type u)) :
    Pairs.map R L (u ≫ v) x = Pairs.map R L v (Pairs.map R L u x) :=
  ConcreteCategory.congr_hom ((CommAlgCat.etale.{u} R).ι.map_comp u.left v.left) x

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- A morphism of pairs is compatible with the augmentations. -/
private theorem Pairs.aug_map {A B : Pairs R L} (u : A ⟶ B) (x : (A.left.obj : Type u)) :
    B.hom.hom (Pairs.map R L u x) = A.hom.hom x :=
  ConcreteCategory.congr_hom (CostructuredArrow.w u) x

/-- The pair given by an étale `R`-algebra `S` together with an augmentation `α : S →ₐ[R] L`. -/
private def Pairs.ofAug (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (α : S →ₐ[R] L) : Pairs R L :=
  CostructuredArrow.mk (Y := ⟨CommAlgCat.of R S, inferInstanceAs (Algebra.Etale R S)⟩)
    (CommAlgCat.ofHom α)

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- The augmentation of `Pairs.ofAug R L S α` is `α`. -/
private theorem Pairs.hom_ofAug (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (α : S →ₐ[R] L) (x : S) : (Pairs.ofAug R L S α).hom.hom x = α x := rfl

/-- A morphism from a pair `A` to `Pairs.ofAug R L S α`, given an `R`-algebra map `φ` out of the
algebra underlying `A` which is compatible with the two augmentations. -/
private def Pairs.homToOfAug (A : Pairs R L) (S : Type u) [CommRing S] [Algebra R S]
    [Algebra.Etale R S] (α : S →ₐ[R] L) (φ : (A.left.obj : Type u) →ₐ[R] S)
    (h : ∀ x, α (φ x) = A.hom.hom x) : A ⟶ Pairs.ofAug R L S α :=
  CostructuredArrow.homMk (ObjectProperty.homMk (CommAlgCat.ofHom φ))
    (CommAlgCat.hom_ext (AlgHom.ext h))

/-- The pair given by `R` itself, augmented by the structure map `R → L`. -/
private noncomputable def Pairs.unit : Pairs R L := Pairs.ofAug R L R (Algebra.ofId R L)

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- If the augmentation of `g` is nonzero in the pair `A`, then `A` has a morphism to a pair in
which `g` becomes a unit. -/
private theorem Pairs.exists_away (A : Pairs R L) (g : (A.left.obj : Type u))
    (hg : A.hom.hom g ≠ 0) :
    ∃ (C : Pairs R L) (h : A ⟶ C), IsUnit (Pairs.map R L h g) := by
  have hunits : ∀ y : Submonoid.powers g, IsUnit (A.hom.hom (y : (A.left.obj : Type u))) := by
    rintro ⟨-, n, rfl⟩
    rw [map_pow]
    exact (isUnit_iff_ne_zero.2 hg).pow n
  have : Algebra.Etale R (Localization.Away g) :=
    Algebra.Etale.comp R (A.left.obj : Type u) (Localization.Away g)
  obtain ⟨lift, hlift⟩ : ∃ lift : Localization.Away g →ₐ[R] L,
      ∀ x : (A.left.obj : Type u),
        lift (algebraMap (A.left.obj : Type u) (Localization.Away g) x) = A.hom.hom x :=
    ⟨IsLocalization.liftAlgHom (M := Submonoid.powers g) (S := Localization.Away g)
      (f := A.hom.hom) hunits, fun x => IsLocalization.lift_eq hunits x⟩
  refine ⟨Pairs.ofAug R L (Localization.Away g) lift,
    Pairs.homToOfAug R L A _ _
      (IsScalarTower.toAlgHom R (A.left.obj : Type u) (Localization.Away g)) hlift, ?_⟩
  show IsUnit (IsScalarTower.toAlgHom R (A.left.obj : Type u) (Localization.Away g) g)
  exact IsLocalization.map_units (M := Submonoid.powers g) (Localization.Away g)
    ⟨g, Submonoid.mem_powers g⟩

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- Any two pairs map to a common pair, namely their tensor product over `R` augmented by the
product of the two augmentations. -/
private theorem Pairs.cocone_objs (A B : Pairs R L) :
    ∃ (C : Pairs R L) (_ : A ⟶ C) (_ : B ⟶ C), True := by
  have : Algebra.Etale R (TensorProduct R (A.left.obj : Type u) (B.left.obj : Type u)) :=
    Algebra.Etale.comp R (A.left.obj : Type u)
      (TensorProduct R (A.left.obj : Type u) (B.left.obj : Type u))
  exact ⟨Pairs.ofAug R L (TensorProduct R (A.left.obj : Type u) (B.left.obj : Type u))
      (Algebra.TensorProduct.lift A.hom.hom B.hom.hom fun _ _ ↦ Commute.all _ _),
    Pairs.homToOfAug R L A _ _ (Algebra.TensorProduct.includeLeft (R := R) (S := R))
      (fun x => by simp),
    Pairs.homToOfAug R L B _ _ (Algebra.TensorProduct.includeRight (R := R))
      (fun x => by simp), trivial⟩

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- Any two parallel morphisms of pairs are equalized after a further morphism. -/
private theorem Pairs.cocone_maps {A B : Pairs R L} (f g : A ⟶ B) :
    ∃ (C : Pairs R L) (h : B ⟶ C), f ≫ h = g ≫ h := by
  set θ := Algebra.TensorProduct.lift (Pairs.map R L f) (Pairs.map R L g)
    (fun _ _ => Commute.all _ _) with hθ
  set e := Algebra.FormallyUnramified.elem R (A.left.obj : Type u) with he
  have hcomm : B.hom.hom.comp θ = A.hom.hom.comp (Algebra.TensorProduct.lmul' R) :=
    Algebra.TensorProduct.ext' fun x y => by
      simp only [AlgHom.coe_comp, Function.comp_apply, hθ, Algebra.TensorProduct.lift_tmul,
        Algebra.TensorProduct.lmul'_apply_tmul, map_mul, Pairs.aug_map R L f x,
        Pairs.aug_map R L g y]
  have haug : B.hom.hom (θ e) = 1 := by
    simpa [he, Algebra.FormallyUnramified.lmul_elem] using
      congrArg (fun m : TensorProduct R (A.left.obj : Type u) (A.left.obj : Type u)
        →ₐ[R] L => m e) hcomm
  have key : ∀ x, Pairs.map R L f x * θ e = Pairs.map R L g x * θ e := fun x => by
    simpa [hθ, he, Algebra.TensorProduct.lift_tmul] using
      (congrArg θ (Algebra.FormallyUnramified.one_tmul_mul_elem
        (R := R) (S := (A.left.obj : Type u)) x)).symm
  obtain ⟨C, h, hu⟩ := Pairs.exists_away R L B (θ e) (by rw [haug]; exact one_ne_zero)
  refine ⟨C, h, Pairs.hom_ext R L _ _ (AlgHom.ext fun x => ?_)⟩
  rw [Pairs.map_comp, Pairs.map_comp]
  exact hu.mul_right_cancel (by rw [← map_mul, ← map_mul, key x])

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- The category of pairs is filtered. -/
@[sga "4 VIII 4.1" "more general"]
private theorem isFiltered_pairs : IsFiltered (Pairs R L) :=
  have : IsFilteredOrEmpty (Pairs R L) :=
    { cocone_objs := fun A B ↦ Pairs.cocone_objs R L A B
      cocone_maps := fun {_ _} f g ↦ Pairs.cocone_maps R L f g }
  { nonempty := ⟨Pairs.unit R L⟩ }

attribute [local instance] isFiltered_pairs

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- The category of étale `R`-algebras augmented to a field `L` is filtered. -/
theorem _root_.CommAlgCat.isFiltered_costructuredArrow_etale :
    IsFiltered (CostructuredArrow (CommAlgCat.etale.{u} R).ι (CommAlgCat.of R L)) :=
  isFiltered_pairs R L

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- If the augmentation of `g` is nonzero, then `A` maps to an augmented étale algebra in which `g`
becomes a unit. -/
theorem _root_.CommAlgCat.exists_costructuredArrow_etale_hom_isUnit
    (A : CostructuredArrow (CommAlgCat.etale.{u} R).ι (CommAlgCat.of R L))
    (g : (A.left.obj : Type u)) (hg : A.hom.hom g ≠ 0) :
    ∃ (C : CostructuredArrow (CommAlgCat.etale.{u} R).ι (CommAlgCat.of R L)) (h : A ⟶ C),
      IsUnit (((CommAlgCat.etale.{u} R).ι.map h.left).hom g) :=
  Pairs.exists_away R L A g hg

/-- The kernel of the augmentation of a pair lies over `𝔪`. -/
private theorem Pairs.liesOver_ker (A : Pairs R L) :
    (RingHom.ker A.hom.hom : Ideal (A.left.obj : Type u)).LiesOver (maximalIdeal R) :=
  ⟨Ideal.ext fun r => by
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, algebraMap_eq_zero_iff]⟩

/-- If the augmentation of a pair kills `y`, then after one morphism of pairs `y` lies in the ideal
generated by `𝔪`. -/
private theorem Pairs.exists_mem_map_maximalIdeal (A : Pairs R L) (y : (A.left.obj : Type u))
    (hy : A.hom.hom y = 0) :
    ∃ (C : Pairs R L) (u : A ⟶ C),
      Pairs.map R L u y ∈ (maximalIdeal R).map (algebraMap R (C.left.obj : Type u)) := by
  have hq : (RingHom.ker A.hom.hom : Ideal (A.left.obj : Type u)).IsPrime := RingHom.ker_isPrime _
  have := Pairs.liesOver_ker R L A
  obtain ⟨g, hg, hgy⟩ :=
    exists_mul_mem_map_maximalIdeal R (RingHom.ker A.hom.hom : Ideal (A.left.obj : Type u))
      (RingHom.mem_ker.2 hy)
  obtain ⟨C, u, hu⟩ := Pairs.exists_away R L A g fun h => hg (RingHom.mem_ker.2 h)
  obtain ⟨w, hw⟩ := hu.exists_left_inv
  refine ⟨C, u, ?_⟩
  have h1 : Pairs.map R L u g * Pairs.map R L u y ∈
      (maximalIdeal R).map (algebraMap R (C.left.obj : Type u)) := by
    rw [← map_mul]
    exact Stacks.Henselization.EtaleColimit.mem_map_of_algHom R (Pairs.map R L u) hgy
  rw [show Pairs.map R L u y = w * (Pairs.map R L u g * Pairs.map R L u y) by
    rw [← mul_assoc, hw, one_mul]]
  exact Ideal.mul_mem_left _ _ h1

/-! ### The colimit -/

/-- A `u`-small model of the category of pairs. -/
private abbrev Index : Type u := SmallModel (Pairs R L)

/-- The diagram of étale `R`-algebras indexed by the small model of the category of pairs. -/
private noncomputable def diagram : Index R L ⥤ CommAlgCat.{u} R :=
  (equivSmallModel (Pairs R L)).inverse ⋙
    CostructuredArrow.proj (CommAlgCat.etale.{u} R).ι (CommAlgCat.of R L) ⋙
      (CommAlgCat.etale.{u} R).ι

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- Every object of the diagram is an étale `R`-algebra. -/
private theorem etale_diagram_obj (i : Index R L) :
    Algebra.Etale R ((diagram R L).obj i) :=
  ((equivSmallModel (Pairs R L)).inverse.obj i).left.property

/-- The **augColimit** of `R`: the colimit of the diagram of pairs. -/
private noncomputable abbrev augColimit : CommAlgCat.{u} R := colimit (diagram R L)

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- The augColimit is a filtered colimit of étale `R`-algebras. -/
private theorem ind_augColimit :
    (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R (augColimit R L : Type u)) :=
  ⟨Index R L, inferInstance, IsFiltered.of_equivalence (equivSmallModel (Pairs R L)),
    { diag := diagram R L
      ι := (colimit.cocone (diagram R L)).ι
      isColimit := colimit.isColimit _ }, etale_diagram_obj R L⟩

/-- The functor `(S, α) ↦ S` from pairs to `R`-algebras. -/
private abbrev pairsFunctor : Pairs R L ⥤ CommAlgCat.{u} R :=
  CostructuredArrow.proj (CommAlgCat.etale.{u} R).ι (CommAlgCat.of R L) ⋙
    (CommAlgCat.etale.{u} R).ι

/-- Reindexing the diagram along the equivalence with the small model identifies `pairsFunctor`
with the diagram, up to the unit of the equivalence. -/
private noncomputable def pairsIsoDiagram :
    pairsFunctor R L ≅ (equivSmallModel (Pairs R L)).functor ⋙ diagram R L :=
  (Functor.leftUnitor (pairsFunctor R L)).symm ≪≫
    Functor.isoWhiskerRight (equivSmallModel (Pairs R L)).unitIso (pairsFunctor R L) ≪≫
      Functor.associator _ _ _

/-- The colimit cocone of the augColimit, indexed by the category of pairs itself rather than
by its small model. -/
private noncomputable def pairsCocone : Cocone (pairsFunctor R L) :=
  (Cocone.precompose (pairsIsoDiagram R L).hom).obj
    (Cocone.whisker (equivSmallModel (Pairs R L)).functor (colimit.cocone (diagram R L)))

/-- The cocone over the category of pairs is a colimit cocone. -/
private noncomputable def pairsCoconeIsColimit : IsColimit (pairsCocone R L) :=
  (IsColimit.precomposeHomEquiv (pairsIsoDiagram R L) _).symm
    (IsColimit.whiskerEquivalence (colimit.isColimit (diagram R L)) (equivSmallModel (Pairs R L)))

/-- The `R`-algebra map from a pair into `colim`, i.e. the structure map of the colimit cocone. -/
private noncomputable abbrev stageHom (A : Pairs R L) :
    (A.left.obj : Type u) →ₐ[R] (augColimit R L : Type u) := ((pairsCocone R L).ι.app A).hom

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- A morphism of pairs does not change the element of `colim` that a triple determines. -/
private theorem stageHom_map {A B : Pairs R L} (u : A ⟶ B) (y : (A.left.obj : Type u)) :
    stageHom R L B (Pairs.map R L u y) = stageHom R L A y :=
  ConcreteCategory.congr_hom ((pairsCocone R L).w u) y

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- Every element of `colim` comes from a triple `(S, α, f)`. -/
private theorem exists_stage (x : (augColimit R L : Type u)) :
    ∃ (A : Pairs R L) (y : (A.left.obj : Type u)), stageHom R L A y = x :=
  CommAlgCat.exists_app_eq (pairsCoconeIsColimit R L) x

/-- The cocone of augmentations: every pair comes with an `R`-algebra map to `L`, compatibly with
morphisms of pairs. -/
private noncomputable def augPairsCocone : Cocone (pairsFunctor R L) where
  pt := CommAlgCat.of R L
  ι := { app := fun A => A.hom
         naturality := fun A B u => by simpa using CostructuredArrow.w u }

/-- The **augmentation** `R^{sh} → L`, induced by the augmentations of the pairs. -/
private noncomputable def aug : (augColimit R L : Type u) →ₐ[R] L :=
  ((pairsCoconeIsColimit R L).desc (augPairsCocone R L)).hom

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- The augmentation of `colim` restricts on each stage to the augmentation of that pair. -/
private theorem aug_stageHom (A : Pairs R L) (y : (A.left.obj : Type u)) :
    aug R L (stageHom R L A y) = A.hom.hom y :=
  ConcreteCategory.congr_hom ((pairsCoconeIsColimit R L).fac (augPairsCocone R L) A) y

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- The augmentation composed with `R → colim` is the structure map `R → L`. -/
private theorem aug_algebraMap (r : R) :
    aug R L (algebraMap R (augColimit R L : Type u) r) = algebraMap R L r :=
  (aug R L).commutes r

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- An element of `colim` is a unit exactly when its augmentation is nonzero. -/
private theorem isUnit_iff_aug_ne_zero (x : (augColimit R L : Type u)) :
    IsUnit x ↔ aug R L x ≠ 0 := by
  refine ⟨fun hx => (hx.map (aug R L)).ne_zero, fun hx => ?_⟩
  obtain ⟨A, y, rfl⟩ := exists_stage R L x
  rw [aug_stageHom] at hx
  obtain ⟨C, h, hu⟩ := Pairs.exists_away R L A y hx
  rw [← stageHom_map R L h y]
  exact hu.map (stageHom R L C)

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- `colim` is nontrivial, since it maps to the field `L`. -/
private theorem nontrivial_augColimit : Nontrivial (augColimit R L : Type u) :=
  (aug R L).toRingHom.domain_nontrivial

attribute [local instance] nontrivial_augColimit

/-! ### The colimit is local with maximal ideal `𝔪 R^{sh}` -/

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- The colimit is a local ring. -/
private theorem isLocalRing_augColimit : IsLocalRing (augColimit R L : Type u) := by
  refine IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add fun a b hab => ?_
  rw [isUnit_iff_aug_ne_zero, map_add] at hab
  rw [isUnit_iff_aug_ne_zero, isUnit_iff_aug_ne_zero]
  by_contra hc
  push Not at hc
  exact hab (by rw [hc.1, hc.2, add_zero])

attribute [local instance] isLocalRing_augColimit

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- The maximal ideal of `colim` is the kernel of the augmentation. -/
private theorem mem_maximalIdeal_iff_aug_eq_zero (x : (augColimit R L : Type u)) :
    x ∈ maximalIdeal (augColimit R L : Type u) ↔ aug R L x = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_aug_ne_zero, not_not]

/-- The structural map `R → R^{sh}` is local. -/
private theorem isLocalHom_algebraMap_augColimit :
    IsLocalHom (algebraMap R (augColimit R L : Type u)) :=
  ⟨fun r hr => by
    rw [isUnit_iff_aug_ne_zero, aug_algebraMap, Ne, algebraMap_eq_zero_iff, mem_maximalIdeal,
      mem_nonunits_iff, not_not] at hr
    exact hr⟩

attribute [local instance] isLocalHom_algebraMap_augColimit

/-- `𝔪 R^{sh}` is the maximal ideal of `colim`. -/
private theorem map_maximalIdeal_augColimit :
    (maximalIdeal R).map (algebraMap R (augColimit R L : Type u)) =
      maximalIdeal (augColimit R L : Type u) := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun r hr => ?_) fun x hx => ?_
  · rw [Ideal.mem_comap, mem_maximalIdeal_iff_aug_eq_zero, aug_algebraMap, algebraMap_eq_zero_iff]
    exact hr
  · rw [mem_maximalIdeal_iff_aug_eq_zero] at hx
    obtain ⟨A, y, rfl⟩ := exists_stage R L x
    rw [aug_stageHom] at hx
    obtain ⟨C, u, hmem⟩ := Pairs.exists_mem_map_maximalIdeal R L A y hx
    rw [← stageHom_map R L u y]
    exact Stacks.Henselization.EtaleColimit.mem_map_of_algHom R (stageHom R L C) hmem

/-! ### Points and polynomials living on a single pair -/

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- Any finite set of elements of `colim` is in the image of a single pair. -/
private theorem exists_stage_finset (s : Finset (augColimit R L : Type u)) :
    ∃ A : Pairs R L, ∀ x ∈ s, ∃ y : (A.left.obj : Type u), stageHom R L A y = x :=
  Stacks.Henselization.EtaleColimit.exists_app_eq_finset R (pairsCocone R L)
    (pairsCoconeIsColimit R L) s

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- A monic polynomial over `colim` and an element of `colim` come from a single pair, the
polynomial from a monic polynomial. -/
private theorem exists_stage_polynomial (p : Polynomial (augColimit R L : Type u))
    (hp : p.Monic) (a₀ : (augColimit R L : Type u)) :
    ∃ (A : Pairs R L) (Q : Polynomial (A.left.obj : Type u)) (b : (A.left.obj : Type u)),
      Q.Monic ∧ Q.map (stageHom R L A).toRingHom = p ∧ stageHom R L A b = a₀ := by
  classical
  obtain ⟨A, hA⟩ := exists_stage_finset R L (insert a₀ (p.support.image p.coeff))
  obtain ⟨b, hb⟩ := hA a₀ (Finset.mem_insert_self _ _)
  have hlifts : p ∈ Polynomial.lifts (stageHom R L A).toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ∈ p.support
    · exact hA (p.coeff n) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hn))
    · rw [Polynomial.notMem_support_iff.1 hn]
      exact ⟨0, map_zero _⟩
  obtain ⟨Q, hQ1, -, hQ3⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hp
  exact ⟨A, Q, b, hQ3, hQ1, hb⟩

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- A polynomial over a pair has the same image in `colim[T]` as its image over any later pair. -/
private theorem stageHom_map_polynomial {A C : Pairs R L} (u : A ⟶ C)
    (Q : Polynomial (A.left.obj : Type u)) :
    (Q.map (Pairs.map R L u).toRingHom).map (stageHom R L C).toRingHom
      = Q.map (stageHom R L A).toRingHom := by
  rw [Polynomial.map_map,
    show (stageHom R L C).toRingHom.comp (Pairs.map R L u).toRingHom = (stageHom R L A).toRingHom
      from RingHom.ext fun y => stageHom_map R L u y]

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- The augmentation of `Q(b)`, for `Q` and `b` pushed forward from a pair to `colim`, is the value
at the augmentation of `b` of the image of `Q` under the augmentation of the pair. -/
private theorem aug_eval_map (A : Pairs R L) (Q : Polynomial (A.left.obj : Type u))
    (b : (A.left.obj : Type u)) :
    aug R L ((Q.map (stageHom R L A).toRingHom).eval (stageHom R L A b))
      = (Q.map A.hom.hom.toRingHom).eval (A.hom.hom b) := by
  rw [eval_map_toRingHom, eval_map_toRingHom, aug_stageHom]

/-! ### Adjoining a root -/

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- **Adjoining a root to a pair.** Let `(S, α)` be a pair, `Q ∈ S[T]` monic and `θ ∈ L` a simple
root of the image of `Q`, i.e. `Q^α(θ) = 0` and `(Q^α)'(θ) ≠ 0`. Then `(S, α)` maps to a pair in
which `Q` has a root with augmentation `θ`. -/
private theorem Pairs.exists_root (A : Pairs R L) (Q : Polynomial (A.left.obj : Type u))
    (hQ : Q.Monic) (θ : L) (h0 : (Q.map A.hom.hom.toRingHom).eval θ = 0)
    (h1 : ((Polynomial.derivative Q).map A.hom.hom.toRingHom).eval θ ≠ 0) :
    ∃ (C : Pairs R L) (u : A ⟶ C) (t : (C.left.obj : Type u)),
      (Q.map (Pairs.map R L u).toRingHom).eval t = 0 ∧ C.hom.hom t = θ := by
  let _ : Algebra (A.left.obj : Type u) L := A.hom.hom.toRingHom.toAlgebra
  have : IsScalarTower R (A.left.obj : Type u) L :=
    IsScalarTower.of_algebraMap_eq fun r => (A.hom.hom.commutes r).symm
  have haeval : ∀ T : Polynomial (A.left.obj : Type u),
      Polynomial.aeval θ T = (T.map A.hom.hom.toRingHom).eval θ := fun T => by
    rw [Polynomial.eval_map, Polynomial.aeval_def, RingHom.algebraMap_toAlgebra]
  obtain ⟨P, hPf, hPg⟩ : ∃ P : StandardEtalePair (A.left.obj : Type u),
      P.f = Q ∧ P.g = Polynomial.derivative Q :=
    ⟨⟨Q, hQ, Polynomial.derivative Q, ⟨Polynomial.derivative Q, 0, 2, by ring⟩⟩, rfl, rfl⟩
  have hmap : P.HasMap θ :=
    ⟨by rw [hPf, haeval]; exact h0, by rw [hPg, haeval]; exact isUnit_iff_ne_zero.2 h1⟩
  let _ : Algebra R P.Ring :=
    ((algebraMap (A.left.obj : Type u) P.Ring).comp
      (algebraMap R (A.left.obj : Type u))).toAlgebra
  have : IsScalarTower R (A.left.obj : Type u) P.Ring := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.Etale R P.Ring := Algebra.Etale.comp R (A.left.obj : Type u) P.Ring
  refine ⟨Pairs.ofAug R L P.Ring ((P.lift θ hmap).restrictScalars R),
    Pairs.homToOfAug R L A P.Ring _ (IsScalarTower.toAlgHom R (A.left.obj : Type u) P.Ring)
      (fun s => (P.lift θ hmap).commutes s), P.X, ?_, ?_⟩
  · show (Q.map (algebraMap (A.left.obj : Type u) P.Ring)).eval P.X = 0
    rw [Polynomial.eval_map, ← Polynomial.aeval_def, ← hPf]
    exact P.hasMap_X.1
  · rw [Pairs.hom_ofAug]
    exact P.lift_X _ hmap

omit [IsLocalRing R] [IsLocalHom (algebraMap R L)] in
/-- The augColimit is a henselian local ring. -/
private theorem henselianLocalRing_augColimit :
    HenselianLocalRing (augColimit R L : Type u) := by
  refine { is_henselian := fun p hp a₀ hpa₀ hunit => ?_ }
  obtain ⟨A, Q, b, hQ, hQmap, rfl⟩ := exists_stage_polynomial R L p hp a₀
  obtain ⟨C, u, t, ht0, htb⟩ := Pairs.exists_root R L A Q hQ (A.hom.hom b)
    (by rw [← aug_eval_map, hQmap]; exact (mem_maximalIdeal_iff_aug_eq_zero R L _).1 hpa₀)
    (by rw [← aug_eval_map, ← Polynomial.derivative_map, hQmap]
        exact (isUnit_iff_aug_ne_zero R L _).1 hunit)
  refine ⟨stageHom R L C t, ?_, ?_⟩
  · show Polynomial.eval (stageHom R L C t) p = 0
    rw [← hQmap, ← stageHom_map_polynomial R L u Q, eval_map_toRingHom, ht0, map_zero]
  · rw [mem_maximalIdeal_iff_aug_eq_zero, map_sub, aug_stageHom, aug_stageHom, htb, sub_self]

end

/-! ### The residue field of the colimit is `L` -/

section

variable (R : Type u) [CommRing R] [IsLocalRing R] (L : Type u) [Field L]
  [Algebra (ResidueField R) L] [Algebra R L] [IsScalarTower R (ResidueField R) L]

attribute [local instance] etale_essentiallySmall Pairs.etale essentiallySmall_pairs
  isFiltered_pairs nontrivial_augColimit isLocalRing_augColimit

/-- A polynomial over `R` is evaluated in `L` through the residue field: evaluating the image of
`Q` in `L[T]` is evaluating the image of its reduction `Q mod 𝔪`. -/
private theorem eval_map_algebraMap (Q : Polynomial R) (θ : L) :
    (Q.map (algebraMap R L)).eval θ = Polynomial.aeval θ (Q.map (residue R)) := by
  rw [IsScalarTower.algebraMap_eq R (ResidueField R) L, ResidueField.algebraMap_eq,
    ← Polynomial.map_map, Polynomial.eval_map, ← Polynomial.aeval_def]

variable [IsLocalHom (algebraMap R L)]

attribute [local instance] isLocalHom_algebraMap_augColimit

omit [IsLocalHom (algebraMap R L)] in
/-- The augmentation is surjective when `L` is separable algebraic over `κ`. -/
private theorem aug_surjective [Algebra.IsSeparable (ResidueField R) L] :
    Function.Surjective (aug R L) := by
  intro θ
  have hlifts : minpoly (ResidueField R) θ ∈ Polynomial.lifts (residue R) :=
    (Polynomial.lifts_iff_coeff_lifts _).2 fun _ => residue_surjective _
  obtain ⟨Q, hQmap, -, hQmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts
    (minpoly.monic (Algebra.IsSeparable.isIntegral (ResidueField R) θ))
  obtain ⟨C, -, t, -, ht⟩ := Pairs.exists_root R L (Pairs.unit R L) Q hQmonic θ
    (by change (Q.map (algebraMap R L)).eval θ = 0
        rw [eval_map_algebraMap, hQmap]
        exact minpoly.aeval _ _)
    (by change ((Polynomial.derivative Q).map (algebraMap R L)).eval θ ≠ 0
        rw [eval_map_algebraMap, ← Polynomial.derivative_map, hQmap]
        exact (Algebra.IsSeparable.isSeparable (ResidueField R) θ).aeval_derivative_ne_zero
          (minpoly.aeval _ _))
  exact ⟨stageHom R L C t, by rw [aug_stageHom, ht]⟩

/-- The augmentation, viewed on the residue field of the colimit. -/
private noncomputable def resToAug :
    ResidueField (augColimit R L : Type u) →+* L :=
  Ideal.Quotient.lift _ (aug R L).toRingHom
    fun a ha => (mem_maximalIdeal_iff_aug_eq_zero R L a).1 ha

omit [IsLocalRing R] [Algebra (ResidueField R) L] [IsScalarTower R (ResidueField R) L]
  [IsLocalHom (algebraMap R L)] in
private theorem resToAug_residue (x : (augColimit R L : Type u)) :
    resToAug R L (residue (augColimit R L : Type u) x) = aug R L x := rfl

omit [IsLocalHom (algebraMap R L)] in
/-- The augmentation induces a bijection of the residue field of the colimit with `L`. -/
private theorem bijective_resToAug [Algebra.IsSeparable (ResidueField R) L] :
    Function.Bijective (resToAug R L) :=
  ⟨(resToAug R L).injective, fun θ => by
    obtain ⟨x, hx⟩ := aug_surjective R L θ
    exact ⟨residue (augColimit R L : Type u) x, by rw [resToAug_residue, hx]⟩⟩

/-- The residue field of the colimit is `L`, as an isomorphism
`L ≃+* ResidueField (augColimit R L)` inverse to the one induced by the augmentation. -/
private noncomputable def residueFieldEquiv [Algebra.IsSeparable (ResidueField R) L] :
    L ≃+* ResidueField (augColimit R L : Type u) :=
  (RingEquiv.ofBijective (resToAug R L) (bijective_resToAug R L)).symm

omit [IsLocalHom (algebraMap R L)] in
private theorem residueFieldEquiv_symm_apply [Algebra.IsSeparable (ResidueField R) L]
    (y : ResidueField (augColimit R L : Type u)) :
    (residueFieldEquiv R L).symm y = resToAug R L y := rfl

omit [IsLocalHom (algebraMap R L)] in
/-- The isomorphism `residueFieldEquiv R L` is compatible with the two maps out of `R`. -/
private theorem residueFieldEquiv_algebraMap [Algebra.IsSeparable (ResidueField R) L] (x : R) :
    residueFieldEquiv R L (algebraMap (ResidueField R) L (residue R x)) =
      residue (augColimit R L : Type u) (algebraMap R (augColimit R L : Type u) x) := by
  refine (residueFieldEquiv R L).symm.injective ?_
  rw [RingEquiv.symm_apply_apply, residueFieldEquiv_symm_apply, resToAug_residue, aug_algebraMap,
    IsScalarTower.algebraMap_apply R (ResidueField R) L, ResidueField.algebraMap_eq]

end

/-- A field isomorphic to a separably closed field is separably closed. -/
public theorem isSepClosed_of_ringEquiv {K M : Type*} [Field K] [Field M] [IsSepClosed K]
    (e : K ≃+* M) : IsSepClosed M := by
  let _ : Algebra K M := e.toRingHom.toAlgebra
  have : Algebra.IsAlgebraic K M := ⟨fun x =>
    (show x = algebraMap K M (e.symm x) by simp [RingHom.algebraMap_toAlgebra]) ▸
      isAlgebraic_algebraMap _⟩
  exact Algebra.IsAlgebraic.isSepClosed (F := K) (E := M)

/-! ### The map from an ind-étale local `R`-algebra with residue field `κ` -/

section

variable (R : Type u) [CommRing R] [IsLocalRing R] (L : Type u) [Field L]
  [Algebra (ResidueField R) L] [Algebra R L] [IsScalarTower R (ResidueField R) L]
  (Rh : Type u) [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh] [IsLocalHom (algebraMap R Rh)]
  (hres : Function.Surjective (ResidueField.map (algebraMap R Rh)))

attribute [local instance] etale_essentiallySmall Pairs.etale essentiallySmall_pairs
  isFiltered_pairs nontrivial_augColimit isLocalRing_augColimit

include hres in
/-- If the residue field map of `R → Rh` is surjective it is an isomorphism `κ ≃ κ(Rh)`. -/
private noncomputable def residueFieldEquivOfSurjective : ResidueField R ≃+* ResidueField Rh :=
  RingEquiv.ofBijective _ ⟨(ResidueField.map (algebraMap R Rh)).injective, hres⟩

include hres in
/-- A local `R`-algebra `Rh` whose residue field map from `κ` is surjective is augmented to `L` by
`Rh → κ(Rh) ≃ κ → L`. -/
private noncomputable def augOfSurjective : Rh →ₐ[R] L :=
  { (algebraMap (ResidueField R) L).comp
      (((residueFieldEquivOfSurjective R Rh hres).symm : ResidueField Rh →+* ResidueField R).comp
        (residue Rh)) with
    commutes' := fun r => by
      change algebraMap (ResidueField R) L
          ((residueFieldEquivOfSurjective R Rh hres).symm (residue Rh (algebraMap R Rh r)))
        = algebraMap R L r
      rw [← ResidueField.map_residue,
        show ResidueField.map (algebraMap R Rh) (residue R r)
          = residueFieldEquivOfSurjective R Rh hres (residue R r) from rfl,
        RingEquiv.symm_apply_apply, IsScalarTower.algebraMap_apply R (ResidueField R) L,
        ResidueField.algebraMap_eq] }

include hres in
/-- The kernel of the augmentation of `Rh` is its maximal ideal. -/
private theorem augOfSurjective_eq_zero_iff (x : Rh) :
    augOfSurjective R L Rh hres x = 0 ↔ x ∈ maximalIdeal Rh := by
  have h : augOfSurjective R L Rh hres x = algebraMap (ResidueField R) L
      ((residueFieldEquivOfSurjective R Rh hres).symm (residue Rh x)) := rfl
  rw [h, map_eq_zero_iff _ (algebraMap (ResidueField R) L).injective,
    RingEquiv.map_eq_zero_iff, residue_eq_zero_iff]

variable [IsLocalHom (algebraMap R L)]

attribute [local instance] isLocalHom_algebraMap_augColimit

omit [IsLocalHom (algebraMap R L)] in
include hres in
/-- If `Rh` is a filtered colimit of étale `R`-algebras, it maps to the colimit `augColimit R L`
compatibly with the augmentations. -/
private theorem exists_algHom_of_ind
    (hRh : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R Rh)) :
    ∃ f : Rh →ₐ[R] (augColimit R L : Type u),
      ∀ x : Rh, aug R L (f x) = augOfSurjective R L Rh hres x := by
  obtain ⟨J, hJ, hJfil, pres, hpres⟩ := hRh
  let A : J → Pairs R L := fun j => CostructuredArrow.mk
    (Y := ⟨pres.diag.obj j, hpres j⟩)
    (CommAlgCat.ofHom ((augOfSurjective R L Rh hres).comp (pres.ι.app j).hom))
  let m : ∀ {i j : J}, (i ⟶ j) → (A i ⟶ A j) := fun {_ _} φ =>
    CostructuredArrow.homMk (ObjectProperty.homMk (pres.diag.map φ))
      (CommAlgCat.hom_ext (AlgHom.ext fun s => congrArg (augOfSurjective R L Rh hres)
        (ConcreteCategory.congr_hom (pres.w φ) s)))
  let d : Cocone pres.diag :=
    { pt := augColimit R L
      ι := { app := fun j => (pairsCocone R L).ι.app (A j)
             naturality := fun i j φ => by
              simp only [Functor.const_obj_map]
              exact (pairsCocone R L).w (m φ) } }
  refine ⟨(pres.isColimit.desc d).hom, fun x => ?_⟩
  obtain ⟨j, y, hy⟩ := CommAlgCat.exists_app_eq pres.isColimit x
  rw [← hy,
    show (pres.isColimit.desc d).hom ((pres.ι.app j).hom y) = stageHom R L (A j) y from
      ConcreteCategory.congr_hom (pres.isColimit.fac d j) y,
    aug_stageHom]
  rfl

end

section

attribute [local instance] etale_essentiallySmall Pairs.etale essentiallySmall_pairs
  isFiltered_pairs nontrivial_augColimit isLocalRing_augColimit

open scoped Classical in
/-- Let `R` be a local ring, `Rh` a local ind-étale `R`-algebra with `R → Rh` local and surjective
residue field map, and `κ ⊆ κ^sep` a separable algebraic closure of the residue field of `R`. Then
there is a strictly henselian local ind-étale `R`-algebra `Rsh` over `Rh`, with `Rh → Rsh` local,
whose maximal ideal is generated by the maximal ideal of `R` and whose residue field is `κ^sep`,
compatibly with the maps out of `R`. -/
public theorem solution (R : Type u) [CommRing R] [IsLocalRing R]
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh] [IsLocalHom (algebraMap R Rh)]
    (hRh : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R Rh))
    (hRhres : Function.Surjective (ResidueField.map (algebraMap R Rh)))
    (κsep : Type u) [Field κsep] [Algebra (ResidueField R) κsep]
    [IsSepClosure (ResidueField R) κsep] :
    ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : IsLocalRing Rsh) (_ : Algebra R Rsh)
      (_ : Algebra Rh Rsh) (_ : IsScalarTower R Rh Rsh) (_ : IsLocalHom (algebraMap Rh Rsh)),
      HenselianLocalRing Rsh ∧
      IsSepClosed (ResidueField Rsh) ∧
      (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R Rsh) ∧
      (maximalIdeal R).map (algebraMap R Rsh) = maximalIdeal Rsh ∧
      ∃ e : κsep ≃+* ResidueField Rsh, ∀ x : R,
        e (algebraMap (ResidueField R) κsep (residue R x)) = residue Rsh (algebraMap R Rsh x) := by
  let _ : Algebra R κsep := ((algebraMap (ResidueField R) κsep).comp (residue R)).toAlgebra
  have htower : IsScalarTower R (ResidueField R) κsep :=
    IsScalarTower.of_algebraMap_eq' (by rw [ResidueField.algebraMap_eq]; rfl)
  have hlocal : IsLocalHom (algebraMap R κsep) :=
    show IsLocalHom ((algebraMap (ResidueField R) κsep).comp (residue R)) from
      RingHom.isLocalHom_comp _ _
  have : IsSepClosed κsep := IsSepClosure.sep_closed (ResidueField R)
  obtain ⟨f, hf⟩ := exists_algHom_of_ind R κsep Rh hRhres hRh
  let _ : Algebra Rh (augColimit R κsep : Type u) := f.toRingHom.toAlgebra
  have htower' : IsScalarTower R Rh (augColimit R κsep : Type u) :=
    IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  refine ⟨(augColimit R κsep : Type u), inferInstance, isLocalRing_augColimit R κsep,
    inferInstance, inferInstance, htower', ⟨fun x hx => ?_⟩,
    henselianLocalRing_augColimit R κsep,
    isSepClosed_of_ringEquiv (residueFieldEquiv R κsep), ind_augColimit R κsep,
    map_maximalIdeal_augColimit R κsep,
    residueFieldEquiv R κsep, residueFieldEquiv_algebraMap R κsep⟩
  by_contra hnu
  exact (isUnit_iff_aug_ne_zero R κsep (f x)).1 hx
    (by rw [hf x]
        exact (augOfSurjective_eq_zero_iff R κsep Rh hRhres x).2
          ((mem_maximalIdeal x).2 (mem_nonunits_iff.2 hnu)))

end

end Stacks.StrictHenselization.EtaleColimit

/-!
# Existence of the strict henselization of a local ring

Let `(R, 𝔪, κ)` be a local ring and let `κ ⊆ κ^sep` be a separable algebraic closure of its
residue field. There is a local `R`-algebra `Rsh` which is strictly henselian (henselian with
separably closed residue field), is a filtered colimit of étale `R`-algebras, has `𝔪 Rsh` for its
maximal ideal, and has `κ^sep` for its residue field, compatibly with `κ ⊆ κ^sep`; moreover the
henselization `R → R^h` factors it, by a local ring map `R^h → Rsh`. That is the commutative
diagram
```
κ  →  κ   →  κ^sep
↑     ↑        ↑
R  →  R^h →  R^sh
```
of Stacks 04GP. Together with the uniqueness statement 08HT the last four properties pin `Rsh`
down up to isomorphism over `R`, and the local ring map `R → Rsh` is then called the strict
henselization of `R` with respect to `κ ⊆ κ^sep` (Definition 04GQ).

## Main results

* `IsLocalRing.exists_strictHenselization`: a local ring `R` with a separable algebraic closure
  `κ ⊆ κ^sep` of its residue field admits a local `R`-algebra which is strictly henselian,
  ind-étale over `R`, has maximal ideal `𝔪 Rsh` and has residue field `κ^sep`, and which receives
  a local ring map from any local ind-étale `R`-algebra with residue field `κ` — the henselization
  of `R` in particular.

## Implementation notes

*The middle column of the diagram is a hypothesis, not part of the existential.* `Rh` is given
as a local `R`-algebra with `R → Rh` local which is ind-étale with surjective residue field map,
which is what Lemma 04GN produces and what Lemma 04GS shows characterizes the henselization; the
conclusion then supplies the algebra structure `Rh → Rsh` over `R` (the middle square of the
diagram) with item (1). This is stronger than the existential form of 04GP and, by the uniqueness
of 08HT, equivalent to it. `HenselianLocalRing Rh` is *not* assumed: the map `Rh → Rsh` does not
need it, so the statement also covers the degenerate `Rh = R`.

*A filtered colimit of étale `R`-algebras is an ind-étale `R`-algebra.* Item (3) is
`(CommAlgCat.etale R).ind (CommAlgCat.of R Rsh)`: `CategoryTheory.ObjectProperty.ind P X` says
that `X` is the colimit of a filtered diagram all of whose values satisfy `P`, and the colimit is
taken in `CommAlgCat R`, so the diagram, the cocone and the structure map `R → Rsh` are all over
`R`. The index category is taken in the same universe as `R`, which is no restriction, since étale
algebras are of finite presentation and the category of triples used in the construction is
essentially small there.

*Strictly henselian.* Item (2) is `HenselianLocalRing Rsh` together with
`IsSepClosed (ResidueField Rsh)`, which is the definition (Definition 04GU) of a strictly
henselian local ring. The second half is a consequence of item (5).

*A separable algebraic closure is `IsSepClosure`.* `IsSepClosure κ κ^sep` is `IsSepClosed κ^sep`
together with `Algebra.IsSeparable κ κ^sep`, i.e. `κ ⊆ κ^sep` separable algebraic with `κ^sep`
separably closed, and `κ` is `IsLocalRing.ResidueField R`.

*Items (4) and (5).* `𝔪 Rsh` is `(maximalIdeal R).map (algebraMap R Rsh)`, the ideal generated by
the image of `𝔪`. Item (5) is an isomorphism `e : κ^sep ≃+* ResidueField Rsh` compatible with the
two maps out of `R`; since `residue R` is surjective this is the same as
`e.comp (algebraMap κ κ^sep) = ResidueField.map (algebraMap R Rsh)`, the commutativity of the
outer square of the diagram, and given item (4) the target is `Rsh/𝔪 Rsh`. Only the restriction of
`e` to `κ` is determined, as in 04GP: the diagram is chosen, and its right-hand square commutes
automatically, because a lift along the surjection `κ → ResidueField Rh` changes an element of
`Rh` by a member of `𝔪_{Rh}`, whose image lies in `𝔪_{Rsh}` as `Rh → Rsh` is local. For the same
reason `IsLocalHom (algebraMap R Rsh)` is not listed: it follows from item (1) and the scalar
tower.

## References

* [StacksProject 04GP](https://stacks.math.columbia.edu/tag/04GP)
* [StacksProject 04GN](https://stacks.math.columbia.edu/tag/04GN), the henselization `R → R^h`
* [StacksProject 04GQ](https://stacks.math.columbia.edu/tag/04GQ), the strict henselization
  `R → R^{sh}` with respect to `κ ⊆ κ^sep`
* [StacksProject 04GS](https://stacks.math.columbia.edu/tag/04GS), the universal property of `R^h`
* [StacksProject 08HT](https://stacks.math.columbia.edu/tag/08HT), uniqueness of `R^{sh}`

## Tags

strict henselization, henselization, strictly henselian, separable algebraic closure, ind-étale,
étale algebra, filtered colimit, residue field
-/



@[expose] public section

open CategoryTheory IsLocalRing in
/-- **Existence of the strict henselization of a local ring.** Let `(R, 𝔪, κ)` be a local ring,
let `κ ⊆ κ^sep` be a separable algebraic closure, and let `Rh` be a local `R`-algebra with
`R → Rh` local which is a filtered colimit of étale `R`-algebras with residue field `κ` (the
henselization of `R`). Then there is a commutative diagram `R → Rh → Rsh` over `κ → κ → κ^sep`
such that (1) `Rh → Rsh` is a local ring map, (2) `Rsh` is strictly henselian, (3) `Rsh` is a
filtered colimit of étale `R`-algebras, (4) `𝔪 Rsh` is the maximal ideal of `Rsh`, and (5) the
residue field of `Rsh` is `κ^sep`. -/
@[stacks 04GP "The diagram's middle column is a hypothesis: `Rh` is any local ind-étale
`R`-algebra with residue field `κ`, which by Lemmas 04GN and 04GS is the henselization; the
conclusion produces `Rsh` with the algebra structure over `Rh` and item (1). Strictly henselian is
`HenselianLocalRing` plus `IsSepClosed` on the residue field, `Rsh` a filtered colimit of étale
`R`-algebras is `(CommAlgCat.etale R).ind`, `𝔪 Rsh` is `Ideal.map`, and `κ^sep = Rsh/𝔪 Rsh` is an
isomorphism `κ^sep ≃+* ResidueField Rsh` compatible with the maps out of `R`. See the module
docstring.", ega "IV 18.8.8" "(i), part of (iii)"]
public theorem IsLocalRing.exists_strictHenselization (R : Type u) [CommRing R] [IsLocalRing R]
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh] [IsLocalHom (algebraMap R Rh)]
    (hRh : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R Rh))
    (hRhres : Function.Surjective (ResidueField.map (algebraMap R Rh)))
    (κsep : Type u) [Field κsep] [Algebra (ResidueField R) κsep]
    [IsSepClosure (ResidueField R) κsep] :
    ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : IsLocalRing Rsh) (_ : Algebra R Rsh)
      (_ : Algebra Rh Rsh) (_ : IsScalarTower R Rh Rsh) (_ : IsLocalHom (algebraMap Rh Rsh)),
      HenselianLocalRing Rsh ∧
      IsSepClosed (ResidueField Rsh) ∧
      (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R Rsh) ∧
      (maximalIdeal R).map (algebraMap R Rsh) = maximalIdeal Rsh ∧
      ∃ e : κsep ≃+* ResidueField Rsh, ∀ x : R,
        e (algebraMap (ResidueField R) κsep (residue R x)) = residue Rsh (algebraMap R Rsh x) :=
    by exact Stacks.StrictHenselization.EtaleColimit.solution R Rh hRh hRhres κsep

end
