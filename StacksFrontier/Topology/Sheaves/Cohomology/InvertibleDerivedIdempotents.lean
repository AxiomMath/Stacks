module

public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedLocalStalk
public import Mathlib.RingTheory.Idempotents
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections.DualBasisOne

/-!
# Product decompositions of a structure sheaf from global idempotents

Let `(X, 𝒪_X)` be a ringed space and let `(e_n)_{n ∈ ℤ}` be a family of global sections of `𝒪_X`
which are idempotent and pairwise orthogonal, and which are *locally finite and complete*: every
point has a neighbourhood on which all but finitely many `e_n` vanish and the remaining ones sum
to `1`. Then `𝒪_X = ∏_{n ∈ ℤ} e_n 𝒪_X` is a locally finite direct product decomposition of the
structure sheaf, the `n`-th factor being the sheaf of corner rings `U ↦ e_n 𝒪_X(U)`.

## Main definitions

* `Stacks.Cohomology.InvertibleDerived.LocallyFiniteIdempotents`: such a family.
* `Stacks.Cohomology.InvertibleDerived.LocallyFiniteIdempotents.factor`: the sheaf of corner rings
  `U ↦ e_n 𝒪_X(U)`.
* `Stacks.Cohomology.InvertibleDerived.LocallyFiniteIdempotents.productDecomposition`: the
  resulting `ProductDecomposition` of `𝒪_X`.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.InvertibleDerived

variable {X : RingedSpace.{u, u}}

/-- The restriction of a global section of `𝒪_X` to an open set. -/
public def globalRes (s : X.presheaf.obj (op ⊤)) (U : Opens X.carrier) : X.presheaf.obj (op U) :=
  X.presheaf.map (homOfLE le_top).op s

/-- Restricting the restriction of a global section to `U` further along `U ⟶ V` gives its
restriction to `V`. -/
public theorem map_globalRes (s : X.presheaf.obj (op ⊤)) {U V : Opens X.carrier} (f : op U ⟶ op V) :
    X.presheaf.map f (globalRes s U) = globalRes s V := by
  rw [globalRes, globalRes, ← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  rfl

/-- The restriction of a global section to `⊤` is the section itself. -/
public theorem globalRes_top (s : X.presheaf.obj (op ⊤)) : globalRes s ⊤ = s := by
  rw [globalRes, show (homOfLE le_top : (⊤ : Opens X.carrier) ⟶ ⊤) = 𝟙 _ from rfl, op_id,
    X.presheaf.map_id, ConcreteCategory.id_apply]

/-- Restriction of global sections to an open set is multiplicative. -/
public theorem globalRes_mul (s t : X.presheaf.obj (op ⊤)) (U : Opens X.carrier) :
    globalRes (s * t) U = globalRes s U * globalRes t U := map_mul _ s t

/-- Restriction of global sections to an open set is additive. -/
public theorem globalRes_add (s t : X.presheaf.obj (op ⊤)) (U : Opens X.carrier) :
    globalRes (s + t) U = globalRes s U + globalRes t U := map_add _ s t

/-- The restriction of the global section `1` is `1`. -/
public theorem globalRes_one (U : Opens X.carrier) :
    globalRes (1 : X.presheaf.obj (op ⊤)) U = 1 := map_one _

/-- The restriction of the global section `0` is `0`. -/
public theorem globalRes_zero (U : Opens X.carrier) :
    globalRes (0 : X.presheaf.obj (op ⊤)) U = 0 := map_zero _

/-- Two sections of `𝒪_X` which agree on the members of a covering agree. -/
public theorem presheaf_eq_of_locally_eq {ι : Type*} (U : ι → Opens X.carrier) (V : Opens X.carrier)
    (iUV : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U) (s t : X.presheaf.obj (op V))
    (h : ∀ i, X.presheaf.map (iUV i).op s = X.presheaf.map (iUV i).op t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' X.sheaf U V iUV hcover s t h

/-- A compatible family of sections of `𝒪_X` over the members of a covering glues uniquely. -/
public theorem presheaf_existsUnique_gluing {ι : Type*} (U : ι → Opens X.carrier)
    (V : Opens X.carrier) (iUV : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U)
    (sf : ∀ i, X.presheaf.obj (op (U i))) (h : TopCat.Presheaf.IsCompatible X.presheaf U sf) :
    ∃! s : X.presheaf.obj (op V), ∀ i, X.presheaf.map (iUV i).op s = sf i :=
  TopCat.Sheaf.existsUnique_gluing' X.sheaf U V iUV hcover sf h

section Scalars

open Stacks.SheafOfModules.DerivedMonoidal

/-- A section of `𝒪_X`, read as a scalar for `𝒪_X`-modules. -/
public abbrev ringSec {U : (Opens X.carrier)ᵒᵖ} (a : X.presheaf.obj U) :
    (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj U := a

/-- A section of the underlying abelian presheaf of an `𝒪_X`-module, read as a section of the
module. -/
public abbrev modSec {F : Mod X.sheaf} {U : (Opens X.carrier)ᵒᵖ} (m : F.val.presheaf.obj U) :
    F.val.obj U := m

end Scalars

/-- Multiplication by an idempotent `e` is multiplicative: `e(st) = (es)(et)`. -/
public theorem idem_mul_mul {R : Type*} [CommRing R] {e : R} (he : IsIdempotentElem e) (s t : R) :
    e * (s * t) = e * s * (e * t) := by
  rw [mul_mul_mul_comm, he.eq]

/-- Membership in the corner of an idempotent of a commutative ring. -/
public theorem mem_corner_iff_of_comm {R : Type*} [CommRing R] {e : R} (he : IsIdempotentElem e)
    {r : R} : r ∈ Subsemigroup.corner e ↔ e * r = r :=
  Subsemigroup.mem_corner_iff_mul_left he (Semigroup.mem_center_iff.mpr fun _ => mul_comm _ _)

/-- **A locally finite complete family of orthogonal idempotents** of `Γ(X, 𝒪_X)`: idempotent,
pairwise orthogonal, and such that every point has a neighbourhood on which all but finitely many
of them vanish and the others sum to `1`. -/
public structure LocallyFiniteIdempotents (X : RingedSpace.{u, u}) where
  /-- The idempotents. -/
  e : ℤ → X.presheaf.obj (op ⊤)
  /-- Each `e n` is idempotent. -/
  idem : ∀ n, IsIdempotentElem (e n)
  /-- Distinct idempotents are orthogonal. -/
  ortho : ∀ n m, n ≠ m → e n * e m = 0
  /-- Near every point finitely many of the idempotents survive, and they sum to `1`. -/
  locallyFinite : ∀ x : X.carrier, ∃ (V : Opens X.carrier) (S : Finset ℤ), x ∈ V ∧
    (∀ n ∉ S, globalRes (e n) V = 0) ∧ ∑ n ∈ S, globalRes (e n) V = 1

namespace ProductPresentationLimit

open Stacks.SheafOfModules.RingSheafProductFactor

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {ι : Type*}
  {R : Sheaf J CommRingCat.{u}} {factor : ι → Sheaf J CommRingCat.{u}}
  (hp : ProductPresentation R factor)

/-- The section of `R` with prescribed components. -/
public def glue (U : Cᵒᵖ) (a : ∀ n, (factor n).obj.obj U) : R.obj.obj U :=
  (hp.surjective U a).choose

/-- The components of the glued section are the prescribed ones. -/
public theorem π_glue (U : Cᵒᵖ) (a : ∀ n, (factor n).obj.obj U) (n : ι) :
    (hp.π n).hom.app U (glue hp U a) = a n :=
  (hp.surjective U a).choose_spec n

/-- The morphism into `R` with prescribed components. -/
public def lift (s : Fan factor) : s.pt ⟶ R :=
  ObjectProperty.homMk
    { app := fun U => CommRingCat.ofHom
        { toFun := fun t => glue hp U fun n => (s.proj n).hom.app U t
          map_one' := hp.injective fun n => by rw [π_glue]; simp
          map_mul' := fun t t' => hp.injective fun n => by
            rw [map_mul, π_glue, π_glue, π_glue]; simp
          map_zero' := hp.injective fun n => by rw [π_glue]; simp
          map_add' := fun t t' => hp.injective fun n => by
            rw [map_add, π_glue, π_glue, π_glue]; simp }
      naturality := fun U V f => by
        ext t
        refine hp.injective fun n => ?_
        have h1 := π_glue hp V (fun n => (s.proj n).hom.app V (s.pt.obj.map f t)) n
        have h2 := hp.app_map n f (glue hp U fun n => (s.proj n).hom.app U t)
        rw [π_glue] at h2
        exact h1.trans ((ConcreteCategory.congr_hom ((s.proj n).hom.naturality f) t).trans
          h2.symm) }

/-- The components of the lifted morphism are the legs of the fan. -/
public theorem lift_π (s : Fan factor) (n : ι) : lift hp s ≫ hp.π n = s.proj n := by
  ext U t
  exact π_glue hp U _ n

/-- **A product presentation is a limit fan.** -/
public def isLimit : IsLimit (Fan.mk R hp.π) :=
  Fan.IsLimit.mk _ (lift hp) (lift_π hp) fun s m hm => by
    ext U t
    refine hp.injective fun n => ?_
    have h1 := ConcreteCategory.congr_hom (congrArg (fun g => g.hom.app U) (hm n)) t
    have h2 := ConcreteCategory.congr_hom (congrArg (fun g => g.hom.app U) (lift_π hp s n)) t
    exact h1.trans h2.symm

end ProductPresentationLimit

namespace LocallyFiniteIdempotents

variable (E : LocallyFiniteIdempotents X)

/-- The restriction of each `e_n` to an open set is idempotent. -/
public theorem idem_res (n : ℤ) (U : Opens X.carrier) : IsIdempotentElem (globalRes (E.e n) U) := by
  have h := E.idem n
  unfold IsIdempotentElem at h ⊢
  rw [← globalRes_mul, h]

/-- The restrictions of distinct `e_n`, `e_m` to an open set are orthogonal. -/
public theorem ortho_res {n m : ℤ} (h : n ≠ m) (U : Opens X.carrier) :
    globalRes (E.e n) U * globalRes (E.e m) U = 0 := by
  rw [← globalRes_mul, E.ortho n m h, globalRes_zero]

/-- An open set on which only the idempotents indexed by `S` survive, and these sum to `1`. -/
public def IsSplitOn (V : Opens X.carrier) (S : Finset ℤ) : Prop :=
  (∀ n ∉ S, globalRes (E.e n) V = 0) ∧ ∑ n ∈ S, globalRes (E.e n) V = 1

/-- Being split is inherited by smaller open sets. -/
public theorem IsSplitOn.mono {V W : Opens X.carrier} {S : Finset ℤ} (h : E.IsSplitOn V S)
    (hWV : W ≤ V) : E.IsSplitOn W S := by
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [← map_globalRes (E.e n) (homOfLE hWV).op, show globalRes (E.e n) V = 0 from h.1 n hn,
      map_zero]
  · have h2 := congrArg (X.presheaf.map (homOfLE hWV).op) h.2
    rw [map_sum, map_one] at h2
    simpa only [map_globalRes] using h2

/-- Every point has a neighbourhood on which the family is split. -/
public theorem exists_isSplitOn (x : X.carrier) :
    ∃ (V : Opens X.carrier) (S : Finset ℤ), x ∈ V ∧ E.IsSplitOn V S :=
  E.locallyFinite x

/-- On a split open set every section is the sum of its components. -/
public theorem sum_res_mul {V : Opens X.carrier} {S : Finset ℤ} (h : E.IsSplitOn V S)
    (s : X.presheaf.obj (op V)) : ∑ n ∈ S, globalRes (E.e n) V * s = s := by
  rw [← Finset.sum_mul, h.2, one_mul]

/-- A section is determined by its components. -/
public theorem eq_of_res_mul_eq {U : Opens X.carrier} {s t : X.presheaf.obj (op U)}
    (h : ∀ n, globalRes (E.e n) U * s = globalRes (E.e n) U * t) : s = t := by
  classical
  choose V S hxV hV using fun x : U => E.exists_isSplitOn x.1
  refine presheaf_eq_of_locally_eq (fun x : U => U ⊓ V x)
    U (fun x => homOfLE inf_le_left) (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hx, hxV _⟩) s t
    fun x => ?_
  have hs := (hV x).mono E (inf_le_right : U ⊓ V x ≤ V x)
  rw [← E.sum_res_mul hs (X.presheaf.map _ s), ← E.sum_res_mul hs (X.presheaf.map _ t)]
  refine Finset.sum_congr rfl fun n _ => ?_
  have := congrArg (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V x ≤ U)).op) (h n)
  rwa [map_mul, map_mul, map_globalRes] at this

/-! ### The corner rings -/

/-- The ring of sections of the `n`-th factor over `U`: the corner `e_n 𝒪_X(U)`. -/
public abbrev Corner (n : ℤ) (U : Opens X.carrier) : Type u := (E.idem_res n U).Corner

/-- A section of the `n`-th corner over `U` is fixed by multiplication by `e_n`. -/
public theorem mem_corner (n : ℤ) {U : Opens X.carrier} (a : E.Corner n U) :
    globalRes (E.e n) U * a.1 = a.1 :=
  (mem_corner_iff_of_comm (E.idem_res n U)).mp a.2

/-- Where `e_n` vanishes, so does its corner. -/
public theorem corner_val_eq_zero {n : ℤ} {U : Opens X.carrier} (h : globalRes (E.e n) U = 0)
    (a : E.Corner n U) : a.1 = 0 :=
  (E.mem_corner n a).symm.trans (by simp only [h, zero_mul])

/-- The element `e_n s` of the corner, for a section `s` of `𝒪_X`. -/
public def toCorner (n : ℤ) {U : Opens X.carrier} (s : X.presheaf.obj (op U)) : E.Corner n U :=
  ⟨globalRes (E.e n) U * s, (mem_corner_iff_of_comm (E.idem_res n U)).mpr
    (by rw [← mul_assoc, (E.idem_res n U).eq])⟩

/-- The underlying section of `toCorner n s` is `e_n s`. -/
public theorem toCorner_val (n : ℤ) {U : Opens X.carrier} (s : X.presheaf.obj (op U)) :
    (E.toCorner n s).1 = globalRes (E.e n) U * s := rfl

/-- The unit of the corner ring of an idempotent `e` is `e`. -/
public theorem corner_one_val {R : Type*} [CommRing R] {e : R} (he : IsIdempotentElem e) :
    (1 : he.Corner).1 = e := rfl

/-- Multiplication in a corner ring is multiplication in the ambient ring. -/
public theorem corner_mul_val {R : Type*} [CommRing R] {e : R} {he : IsIdempotentElem e}
    (a b : he.Corner) : (a * b).1 = a.1 * b.1 := rfl

/-- Addition in a corner ring is addition in the ambient ring. -/
public theorem corner_add_val {R : Type*} [CommRing R] {e : R} {he : IsIdempotentElem e}
    (a b : he.Corner) : (a + b).1 = a.1 + b.1 := rfl

/-- The zero of a corner ring is the zero of the ambient ring. -/
public theorem corner_zero_val {R : Type*} [CommRing R] {e : R} (he : IsIdempotentElem e) :
    (0 : he.Corner).1 = 0 := rfl

/-- Two elements of a corner ring are equal when their underlying elements are. -/
public theorem corner_ext {R : Type*} [CommRing R] {e : R} {he : IsIdempotentElem e}
    {a b : he.Corner} (h : a.1 = b.1) : a = b := Subtype.ext h

/-- Two sections of the `n`-th corner over `U` are equal when their underlying sections are. -/
public theorem Corner.ext {n : ℤ} {U : Opens X.carrier} {a b : E.Corner n U} (h : a.1 = b.1) :
    a = b := Subtype.ext h

/-- Restriction of sections of the corner rings. -/
public def cornerMap (n : ℤ) {U V : Opens X.carrier} (f : op U ⟶ op V) :
    E.Corner n U →+* E.Corner n V where
  toFun a := ⟨X.presheaf.map f a.1, (mem_corner_iff_of_comm (E.idem_res n V)).mpr (by
    rw [← map_globalRes (E.e n) f, ← map_mul, E.mem_corner n a])⟩
  map_one' := Corner.ext E (map_globalRes (E.e n) f)
  map_mul' a b := Corner.ext E (map_mul _ a.1 b.1)
  map_zero' := Corner.ext E (map_zero (X.presheaf.map f).hom)
  map_add' a b := Corner.ext E (map_add _ a.1 b.1)

/-- The underlying section of a restricted corner section is the restriction in `𝒪_X`. -/
public theorem cornerMap_val (n : ℤ) {U V : Opens X.carrier} (f : op U ⟶ op V)
    (a : E.Corner n U) : (E.cornerMap n f a).1 = X.presheaf.map f a.1 := rfl

/-- The presheaf of corner rings `U ↦ e_n 𝒪_X(U)`. -/
public def factorPresheaf (n : ℤ) : (Opens X.carrier)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (E.Corner n U.unop)
  map f := CommRingCat.ofHom (E.cornerMap n f)
  map_id U := by
    ext a
    exact Corner.ext E (ConcreteCategory.congr_hom (X.presheaf.map_id U) a.1)
  map_comp f g := by
    ext a
    exact Corner.ext E (ConcreteCategory.congr_hom (X.presheaf.map_comp f g) a.1)

/-- The restriction maps of `factorPresheaf n` are those of `𝒪_X` on underlying sections. -/
public theorem factorPresheaf_map_val (n : ℤ) {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V)
    (a : E.Corner n U.unop) :
    ((E.factorPresheaf n).map f a).1 = X.presheaf.map f a.1 := rfl

/-- The presheaf of corner rings is a sheaf: a compatible family of sections of the corners glues
in `𝒪_X`, and the gluing lies in the corner because that is checked on the covering. -/
public theorem isSheaf_factorPresheaf (n : ℤ) :
    TopCat.Presheaf.IsSheaf (E.factorPresheaf n) := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr fun ι U sf hsf => ?_
  have hc : TopCat.Presheaf.IsCompatible X.presheaf U fun i => (sf i).1 :=
    fun i j => congrArg Subtype.val (hsf i j)
  obtain ⟨s, hs, hsu⟩ := presheaf_existsUnique_gluing U (iSup U) (fun i => Opens.leSupr U i)
    le_rfl _ hc
  have hmem : globalRes (E.e n) (iSup U) * s = s := by
    refine presheaf_eq_of_locally_eq U (iSup U) (fun i => Opens.leSupr U i) le_rfl _ _
      fun i => ?_
    rw [map_mul, map_globalRes, hs i]
    exact E.mem_corner n (sf i)
  refine ⟨⟨s, (mem_corner_iff_of_comm (E.idem_res n _)).mpr hmem⟩, fun i => Corner.ext E (hs i),
    fun t ht => Corner.ext E (hsu t.1 fun i => congrArg Subtype.val (ht i))⟩

/-- **The `n`-th factor**: the sheaf of corner rings `U ↦ e_n 𝒪_X(U)`. -/
public def factor (n : ℤ) : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u} :=
  ⟨E.factorPresheaf n, E.isSheaf_factorPresheaf n⟩

/-- Restriction commutes with the projection to the corner. -/
public theorem toCorner_naturality (n : ℤ) {U V : Opens X.carrier} (f : op U ⟶ op V)
    (s : X.presheaf.obj (op U)) :
    E.cornerMap n f (E.toCorner n s) = E.toCorner n (X.presheaf.map f s) :=
  Corner.ext E (by rw [cornerMap_val, toCorner_val, toCorner_val, map_mul, map_globalRes])

/-- The projection `𝒪_X(U) ⟶ e_n 𝒪_X(U)`, `s ↦ e_n s`, as a ring homomorphism. -/
public def toCornerHom (n : ℤ) (U : Opens X.carrier) : X.presheaf.obj (op U) →+* E.Corner n U where
  toFun s := E.toCorner n s
  map_one' := Corner.ext E (mul_one _)
  map_mul' s t := Corner.ext E (idem_mul_mul (E.idem_res n U) s t)
  map_zero' := Corner.ext E (mul_zero _)
  map_add' s t := Corner.ext E (mul_add _ s t)

/-- The underlying section of `toCornerHom n U s` is `e_n s`. -/
public theorem toCornerHom_val (n : ℤ) (U : Opens X.carrier) (s : X.presheaf.obj (op U)) :
    (E.toCornerHom n U s).1 = globalRes (E.e n) U * s := rfl

/-- The projection `𝒪_X ⟶ 𝒪_n` onto the `n`-th factor, as a morphism of sheaves of rings. -/
public def proj (n : ℤ) :
    (X.sheaf : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}) ⟶ E.factor n :=
  ObjectProperty.homMk
    { app := fun U => CommRingCat.ofHom (E.toCornerHom n U.unop)
      naturality := fun U V f => by
        ext s
        exact (E.toCorner_naturality n f s).symm }

/-- On sections over `U`, the projection onto the `n`-th factor is `s ↦ e_n s`. -/
public theorem proj_app_val (n : ℤ) (U : (Opens X.carrier)ᵒᵖ) (s : X.presheaf.obj U) :
    ((E.proj n).hom.app U s).1 = globalRes (E.e n) U.unop * s := rfl

/-- A section of `𝒪_X` over an open set on which only the idempotents in `S` survive is the sum
of the inclusions of its components. -/
public theorem eq_sum_of_isSplitOn {V : Opens X.carrier} {S : Finset ℤ} (h : E.IsSplitOn V S)
    (s : X.presheaf.obj (op V)) : s = ∑ n ∈ S, (E.toCorner n s).1 :=
  (E.sum_res_mul h s).symm

/-- **The sections of `𝒪_X` are the products of the sections of the factors**: the projections
`𝒪_X ⟶ 𝒪_n` exhibit `𝒪_X` as the product of the corner sheaves. -/
public def productPresentation :
    Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation
      (X.sheaf : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}) E.factor where
  π := E.proj
  injective U s t h := E.eq_of_res_mul_eq fun n => congrArg Subtype.val (h n)
  surjective U a := by
    classical
    choose V S hxV hV using fun x : U.unop => E.exists_isSplitOn x.1
    let W : U.unop → Opens X.carrier := fun x => U.unop ⊓ V x
    have hW : ∀ x, E.IsSplitOn (W x) (S x) := fun x => (hV x).mono E inf_le_right
    let ι : ∀ x, W x ⟶ U.unop := fun x => homOfLE inf_le_left
    -- the local candidates
    let sf : ∀ x, X.presheaf.obj (op (W x)) := fun x =>
      ∑ n ∈ S x, X.presheaf.map (ι x).op (a n).1
    -- the components of a local candidate
    have hcomp : ∀ x (m : ℤ) {Y : Opens X.carrier} (j : Y ⟶ W x),
        globalRes (E.e m) Y * X.presheaf.map j.op (sf x) =
          X.presheaf.map (j ≫ ι x).op (a m).1 := by
      intro x m Y j
      have hsY : E.IsSplitOn Y (S x) := (hW x).mono E j.le
      rw [map_sum, Finset.mul_sum]
      simp_rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp, ← op_comp]
      have hterm : ∀ n, globalRes (E.e m) Y * X.presheaf.map (j ≫ ι x).op (a n).1 =
          if n = m then X.presheaf.map (j ≫ ι x).op (a m).1 else 0 := by
        intro n
        have han := E.mem_corner n (a n)
        split_ifs with hnm
        · subst hnm
          rw [← map_globalRes (E.e n) (j ≫ ι x).op, ← map_mul, han]
        · rw [← han, map_mul, map_globalRes, ← mul_assoc, E.ortho_res (Ne.symm hnm), zero_mul]
      simp_rw [hterm]
      rw [Finset.sum_ite_eq']
      split_ifs with hm
      · rfl
      · have han := E.mem_corner m (a m)
        rw [← han, map_mul, map_globalRes, hsY.1 m hm, zero_mul]
    have hcompat : TopCat.Presheaf.IsCompatible X.presheaf W sf := by
      intro x y
      refine E.eq_of_res_mul_eq fun m => ?_
      rw [hcomp x m, hcomp y m]
      rfl
    obtain ⟨s, hs, -⟩ := presheaf_existsUnique_gluing W U.unop ι
      (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hx, hxV _⟩) sf hcompat
    refine ⟨s, fun m => Corner.ext E ?_⟩
    refine presheaf_eq_of_locally_eq W U.unop ι
      (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hx, hxV _⟩) _ _ fun x => ?_
    rw [proj_app_val, map_mul, map_globalRes, hs x]
    have := hcomp x m (𝟙 (W x))
    rwa [op_id, X.presheaf.map_id, ConcreteCategory.id_apply, Category.id_comp] at this

/-- **The product decomposition of `𝒪_X` cut out by a locally finite complete family of
orthogonal idempotents**: `𝒪_X = ∏_{n ∈ ℤ} e_n 𝒪_X`. -/
public def productDecomposition : ProductDecomposition X where
  factor := E.factor
  iso := (ProductPresentationLimit.isLimit E.productPresentation).conePointUniqueUpToIso
    (productIsProduct _)
  locallyFinite x := by
    obtain ⟨V, S, hxV, hV⟩ := E.exists_isSplitOn x
    refine ⟨V, hxV, (S : Set ℤ).toFinite.subset fun n hn => ?_⟩
    by_contra hnS
    refine hn ⟨fun a b => Corner.ext E ?_⟩
    exact (E.corner_val_eq_zero (hV.1 n hnS) a).trans (E.corner_val_eq_zero (hV.1 n hnS) b).symm

/-- The factors of `productDecomposition` are the corner sheaves `factor n`. -/
public theorem productDecomposition_factor : E.productDecomposition.factor = E.factor := rfl

/-- The projection of the decomposition onto its `n`-th factor is `s ↦ e_n s`. -/
public theorem productDecomposition_iso_hom_π (n : ℤ) :
    E.productDecomposition.iso.hom ≫ Pi.π E.factor n = E.proj n :=
  (ProductPresentationLimit.isLimit E.productPresentation).conePointUniqueUpToIso_hom_comp
    (productIsProduct _) ⟨n⟩

/-! ### Modules on which an idempotent acts as the identity -/

open Stacks.SheafOfModules.DerivedMonoidal

/-- `e_n` acts as the identity on the `𝒪_X`-module `F`. -/
public def ActsAsOne (n : ℤ) (F : Mod X.sheaf) : Prop :=
  ∀ (U : (Opens X.carrier)ᵒᵖ) (m : F.val.obj U), ringSec (U := U) (globalRes (E.e n) U.unop) • m = m

section ActsAsOne

variable {E} {n : ℤ} {F : Mod X.sheaf} (hF : E.ActsAsOne n F)

/-- The module structure over the corner `e_n 𝒪_X(U)` of the sections of a module on which `e_n`
acts as the identity. -/
public abbrev cornerModuleStruct (U : (Opens X.carrier)ᵒᵖ) :
    Module ((Stacks.SheafOfModules.Tensor.ringSheaf (E.factor n)).obj.obj U)
      (F.val.presheaf.obj U) where
  smul c m := ringSec (U := U) c.1 • modSec m
  one_smul m := hF U m
  mul_smul a b m := mul_smul (ringSec (U := U) a.1) (ringSec (U := U) b.1) (modSec m)
  smul_zero a := smul_zero (A := F.val.obj U) (ringSec (U := U) a.1)
  smul_add a m m' := smul_add (ringSec (U := U) a.1) (modSec m) (modSec m')
  add_smul a b m := add_smul (ringSec (U := U) a.1) (ringSec (U := U) b.1) (modSec m)
  zero_smul m := zero_smul _ (modSec m)

/-- **A module on which `e_n` acts as the identity, as a module over the `n`-th factor.** -/
public def factorModule :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (E.factor n)) :=
  letI := cornerModuleStruct hF
  { val := PresheafOfModules.ofPresheaf F.val.presheaf fun U _ f c m =>
      F.val.map_smul f (ringSec (U := U) c.1) (modSec m)
    isSheaf := F.isSheaf }

end ActsAsOne

/-- The `n`-th projection of the decomposition is `s ↦ e_n s`. -/
public theorem productDecomposition_proj (n : ℤ) :
    E.productDecomposition.proj n =
      (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map (E.proj n) := by
  rw [ProductDecomposition.proj]
  exact congrArg (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map
    (E.productDecomposition_iso_hom_π n)

/-- On sections over `U`, the `n`-th projection of `productDecomposition` is `r ↦ e_n r`. -/
public theorem productDecomposition_proj_app_val (n : ℤ) (U : (Opens X.carrier)ᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj U) :
    ((E.productDecomposition.proj n).hom.app U r).1 =
      ringSec (U := U) (globalRes (E.e n) U.unop) * r := by
  rw [productDecomposition_proj]
  rfl

section ActsAsOne

variable {E} {n : ℤ} {F : Mod X.sheaf} (hF : E.ActsAsOne n F)

include hF in
/-- On a module on which `e_n` acts as the identity, `(e_n r) • m = r • m`. -/
public theorem smul_eq_of_actsAsOne (U : (Opens X.carrier)ᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj U) (m : F.val.obj U) :
    (ringSec (U := U) (globalRes (E.e n) U.unop) * r) • m = r • m := by
  have hc : ringSec (U := U) (globalRes (E.e n) U.unop) * r =
      r * ringSec (U := U) (globalRes (E.e n) U.unop) :=
    mul_comm (G := ↑(X.presheaf.obj U)) (globalRes (E.e n) U.unop) r
  exact (congrArg (· • m) hc).trans ((mul_smul r _ m).trans (congrArg (r • ·) (hF U m)))

/-- The factor module of `F`, read back as an `𝒪_X`-module along `s ↦ e_n s`, is `F`. -/
public def restrictScalarsProjFactorModuleIso :
    (SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map (E.proj n))).obj
        (factorModule hF) ≅ F where
  hom := ⟨PresheafOfModules.homMk (𝟙 F.val.presheaf) fun U r m =>
    smul_eq_of_actsAsOne hF U r m⟩
  inv := ⟨PresheafOfModules.homMk (𝟙 F.val.presheaf) fun U r m =>
    (smul_eq_of_actsAsOne hF U r m).symm⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- **The factor module of `F`, read back as an `𝒪_X`-module, is `F`.** -/
public def toOXModFactorModuleIso :
    (E.productDecomposition.toOXMod n).obj (factorModule hF) ≅ F :=
  (eqToIso (congrArg SheafOfModules.restrictScalars (E.productDecomposition_proj n))).app _ ≪≫
    restrictScalarsProjFactorModuleIso hF

end ActsAsOne

section Invertible

variable {E} {n : ℤ} {F : Mod X.sheaf} (hF : E.ActsAsOne n F)

/-- **The factor module of `F` is invertible over the `n`-th factor** as soon as `F` is locally
freely generated over the corner rings by one section. -/
public theorem isInvertibleModule_factorModule
    (h : ∀ x : X.carrier, ∃ W : Opens X.carrier, x ∈ W ∧ ∃ s : F.val.obj (op W),
      ∀ (W' : Opens X.carrier) (hW' : W' ≤ W), Function.Bijective fun c : E.Corner n W' =>
        ringSec (U := op W') c.1 • F.val.map (homOfLE hW').op s) :
    Stacks.SheafOfModules.Tensor.IsInvertibleModule (E.factor n) (factorModule hF) := by
  choose W hxW s hs using h
  have hcov : (Opens.grothendieckTopology X.carrier).CoversTop W :=
    (Opens.coversTop_iff _ _).mpr (IsOpenCover.mk (top_le_iff.mp fun x _ =>
      Opens.mem_iSup.mpr ⟨x, hxW x⟩))
  exact Stacks.SheafOfModules.isInvertible_of_dualBasisOne _ _ hcov fun x =>
    Stacks.SheafOfModules.DualBasisOne.ofSmulBijective (W x) (s x) fun V =>
      hs x V.unop.left (leOfHom V.unop.hom)

end Invertible

end LocallyFiniteIdempotents

end Stacks.Cohomology.InvertibleDerived

end
