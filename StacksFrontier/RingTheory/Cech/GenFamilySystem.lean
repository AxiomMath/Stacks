module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# The system of finite generating families of an ideal

Fix a commutative ring `A` and an ideal `I ⊆ A`. A *generating family* of `I` is a finite family
`x : Fin n → A` with `Ideal.span (Set.range x) = I`; these are the objects `Gen A I`. The index
system of this file is the set of **nonempty finite sets** `S` of generating families, ordered by
inclusion, together with, for each such `S`, the **product family**

`famFun S c = ∏ x ∈ S, x.elts (c x)`,  `c` ranging over the choices of one index into each family
of `S`.

The point of the product family is the direction of the comparison maps. For `S ⊆ T` a choice `c`
for `T` restricts to a choice for `S`, and the corresponding value of the product family of `S`
*divides* the one of `T` — the extra factors are those of the families in `T \ S`. So all the
transition maps of the system go the right way, with no choices to be made, and the system is
filtered because a union of two nonempty finite sets dominates both.

## Main definitions

* `Stacks.GenFamily.Gen` — a finite generating family of `I`, and `Stacks.GenFamily.Gen.map`, its
  image under a ring map `φ : A →+* B` with `J = Ideal.map φ I`.
* `Stacks.GenFamily.GenSet` — a nonempty finite set of generating families of `I`, the index of
  the system, with `Stacks.GenFamily.GenSet.map` its transport along a ring map.
* `Stacks.GenFamily.Idx` — the choices of one index into each family of `S`, and
  `Stacks.GenFamily.famFun`, `Stacks.GenFamily.famCard`, `Stacks.GenFamily.fam` — the product
  family of `S`, as a function on `Idx S` and reindexed along `Fin (famCard S)`.
* `Stacks.GenFamily.idxLeFun`, `Stacks.GenFamily.idxLe` — the restriction of a choice along an
  inclusion `S ≤ T`, on `Idx` and on `Fin`.
* `Stacks.GenFamily.idxMapFun`, `Stacks.GenFamily.idxMap` — the restriction of a choice along the
  transport `S ↦ GenSet.map φ hJ S`, on `Idx` and on `Fin`.
* `Stacks.GenFamily.single` — the index given by a single generating family.

## Main results

* the `PartialOrder`, `SemilatticeSup`, `IsDirected` and
  `Stacks.GenFamily.GenSet.isFiltered` instances — **the index system is filtered** as soon as `I`
  is finitely generated (`Stacks.GenFamily.GenSet.nonempty`).
* `Stacks.GenFamily.famFun_dvd_of_le`, `Stacks.GenFamily.fam_dvd_of_le` — **the comparison
  divisibility**: along `S ≤ T` the product family of `S` divides that of `T`.
* `Stacks.GenFamily.map_famFun_dvd`, `Stacks.GenFamily.map_fam_dvd` — the same for a ring map: the
  image of the product family of `S` divides a power of the product family of `GenSet.map φ hJ S`.
* `Stacks.GenFamily.idxLe_refl`, `Stacks.GenFamily.idxLe_trans`,
  `Stacks.GenFamily.idxMapFun_id`, `Stacks.GenFamily.idxMap_id`,
  `Stacks.GenFamily.idxMapFun_comp`, `Stacks.GenFamily.idxMap_comp`,
  `Stacks.GenFamily.idxLeFun_idxMapFun`, `Stacks.GenFamily.idxLe_idxMap` — the coherence laws of
  the index maps.
* `Stacks.GenFamily.zeroLocus_range_fam`,
  `Stacks.GenFamily.zeroLocus_span_range_fam` — **the product family of `S` has the same zero
  locus as `I`**, together with `Stacks.GenFamily.range_fam_subset` and
  `Stacks.GenFamily.fg_span_range_fam`.
* `Stacks.GenFamily.exists_bijective_single` — the product family of a singleton is the single
  family itself, up to a bijection of the index.

## Implementation notes

`Idx S` is the dependent product `(x : {y // y ∈ S.carrier}) → Fin x.1.arity`; it is a `Fintype`,
and it **can be empty** — exactly when some family in `S` has arity `0`, i.e. when `I = ⊥`. No
`Nonempty (Idx S)` instance is provided and nothing below assumes one; in that case `fam S` is the
empty family, whose zero locus is still that of `I = ⊥`, namely everything.

The reindexing along `Fin (famCard S)` is by `Fintype.equivFin`, packaged as
`Stacks.GenFamily.idxEquiv`. Every statement about `fam` is deduced from the corresponding
statement about `famFun`.

Three kinds of index map appear, all of them "restrict a choice along a map of index sets", and all
of them definitionally so: `idxLeFun h c x = c ⟨x.1, h x.2⟩` and
`idxMapFun φ hJ S c x = c ⟨Gen.map φ hJ x.1, _⟩`. The second typechecks with **no cast**:
`(Gen.map φ hJ x.1).arity` is *definitionally* `x.1.arity`, the `arity` field being copied
verbatim. For the same reason the coherence laws between them (`idxMapFun_id`, `idxMapFun_comp`,
`idxLeFun_idxMapFun`) hold by `rfl` after `funext`, proof irrelevance in the `Subtype` making the
membership proofs agree.

Functoriality is only propositional at the level of `GenSet`, because `Finset.image` of the
identity is not the identity on the nose. So the composition laws are stated with the transport
`idxLeFun e.ge` along the `GenSet` equality `e` (`GenSet.map_id`, `GenSet.map_map`) inserted; this
needs no `cast`, since `idxLeFun` for an equality is again just "restrict along an inclusion".

The divisibility for a ring map is genuinely weaker than the one for `S ≤ T`: the map
`x ↦ Gen.map φ hJ x` on generating families need not be injective, so the image of the product
family of `S` is a product of `S.carrier.card` factors of the product family of
`GenSet.map φ hJ S`, possibly with repetitions. Hence the exponent `S.carrier.card`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.GenFamily

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-! ### Generating families -/

/-- **A finite family of elements of `A` spanning the ideal `I`.** -/
structure Gen (A : Type u) [CommRing A] (I : Ideal A) where
  /-- The number of elements of the family. -/
  arity : ℕ
  /-- The elements of the family. -/
  elts : Fin arity → A
  /-- The family spans `I`. -/
  span_eq : Ideal.span (Set.range elts) = I

namespace Gen

variable {I : Ideal A} {J : Ideal B} {K : Ideal C}

/-- Equality of generating families is decided classically. -/
instance : DecidableEq (Gen A I) := Classical.decEq _

/-- Every element of a generating family of `I` lies in `I`. -/
theorem elts_mem (x : Gen A I) (i : Fin x.arity) : x.elts i ∈ I :=
  x.span_eq.le (Ideal.subset_span (Set.mem_range_self i))

/-- **The image of a generating family under a ring map.** If `J = Ideal.map φ I` then the
pointwise images `φ (x.elts i)` form a generating family of `J`. -/
def map (φ : A →+* B) {J : Ideal B} (hJ : J = Ideal.map φ I) (x : Gen A I) : Gen B J where
  arity := x.arity
  elts i := φ (x.elts i)
  span_eq := by
    have h : Set.range (fun i => φ (x.elts i)) = φ '' Set.range x.elts := by
      rw [← Set.range_comp]
      rfl
    rw [h, ← Ideal.map_span, x.span_eq, hJ]

/-- The image of a generating family under a ring map has the same arity. -/
@[simp]
theorem map_arity (φ : A →+* B) (hJ : J = Ideal.map φ I) (x : Gen A I) :
    (map φ hJ x).arity = x.arity := rfl

/-- The elements of the image of a generating family are the images of its elements. -/
@[simp]
theorem map_elts (φ : A →+* B) (hJ : J = Ideal.map φ I) (x : Gen A I) (i : Fin x.arity) :
    (map φ hJ x).elts i = φ (x.elts i) := rfl

/-- **The image along the identity is the family itself**, on the nose. -/
theorem map_id (x : Gen A I) (hI : I = Ideal.map (RingHom.id A) I) :
    map (RingHom.id A) hI x = x := rfl

/-- **The images along two ring maps compose**, on the nose. -/
theorem map_map (φ : A →+* B) (ψ : B →+* C) (hJ : J = Ideal.map φ I) (hK : K = Ideal.map ψ J)
    (hKA : K = Ideal.map (ψ.comp φ) I) (x : Gen A I) :
    map ψ hK (map φ hJ x) = map (ψ.comp φ) hKA x := rfl

/-- **A finitely generated ideal has a generating family.** -/
theorem exists_of_fg (hI : I.FG) : Nonempty (Gen A I) := by
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hI
  exact ⟨⟨n, s, hs⟩⟩

end Gen

/-! ### The directed poset of finite nonempty sets of generating families -/

/-- **A nonempty finite set of generating families of `I`** — an object of the index system. -/
structure GenSet (A : Type u) [CommRing A] (I : Ideal A) where
  /-- The finite set of generating families. -/
  carrier : Finset (Gen A I)
  /-- It is nonempty. -/
  nonempty' : carrier.Nonempty

namespace GenSet

variable {I : Ideal A} {J : Ideal B} {K : Ideal C}

/-- Two indices with the same underlying finite set are equal. -/
@[ext]
theorem ext : ∀ {S T : GenSet A I}, S.carrier = T.carrier → S = T
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- **The order on the index system: inclusion of the underlying finite sets.** -/
instance instPartialOrder : PartialOrder (GenSet A I) where
  le S T := S.carrier ⊆ T.carrier
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ h₁ h₂ := Finset.Subset.trans h₁ h₂
  le_antisymm _ _ h₁ h₂ := ext (Finset.Subset.antisymm h₁ h₂)

/-- `S ≤ T` exactly when the underlying finite set of `S` is contained in that of `T`. -/
@[simp]
theorem le_iff {S T : GenSet A I} : S ≤ T ↔ S.carrier ⊆ T.carrier := Iff.rfl

/-- **The index system is a join-semilattice**, the join being the union: this is what makes it
filtered. -/
instance instSemilatticeSup : SemilatticeSup (GenSet A I) where
  sup S T := ⟨S.carrier ∪ T.carrier, S.nonempty'.mono Finset.subset_union_left⟩
  le_sup_left _ _ := Finset.subset_union_left
  le_sup_right _ _ := Finset.subset_union_right
  sup_le _ _ _ h₁ h₂ := Finset.union_subset h₁ h₂

/-- The underlying finite set of `S ⊔ T` is the union of those of `S` and `T`. -/
@[simp]
theorem sup_carrier (S T : GenSet A I) : (S ⊔ T).carrier = S.carrier ∪ T.carrier := rfl

/-- The index system is directed: `S ⊔ T` dominates both `S` and `T`. -/
instance instIsDirected : IsDirected (GenSet A I) (· ≤ ·) :=
  ⟨fun S T => ⟨S ⊔ T, le_sup_left, le_sup_right⟩⟩

/-- **The index system is nonempty as soon as `I` is finitely generated**: take the singleton on a
finite generating family. -/
theorem nonempty (hI : I.FG) : Nonempty (GenSet A I) := by
  obtain ⟨x⟩ := Gen.exists_of_fg hI
  exact ⟨⟨{x}, Finset.singleton_nonempty x⟩⟩

/-- **The index system of a finitely generated ideal is filtered.** It is a nonempty
join-semilattice, hence a nonempty directed partial order. -/
theorem isFiltered (hI : I.FG) : IsFiltered (GenSet A I) :=
  have := nonempty (I := I) hI
  inferInstance

/-- **The transport of an index along a ring map**: apply `Gen.map φ hJ` to every family of `S`. -/
def map (φ : A →+* B) (hJ : J = Ideal.map φ I) (S : GenSet A I) : GenSet B J where
  carrier := S.carrier.image (Gen.map φ hJ)
  nonempty' := S.nonempty'.image _

/-- The underlying finite set of the transport of `S` is the image of that of `S` under
`Gen.map φ hJ`. -/
@[simp]
theorem map_carrier (φ : A →+* B) (hJ : J = Ideal.map φ I) (S : GenSet A I) :
    (map φ hJ S).carrier = S.carrier.image (Gen.map φ hJ) := rfl

/-- **The transport along a ring map is monotone.** -/
theorem map_monotone (φ : A →+* B) (hJ : J = Ideal.map φ I) :
    Monotone (map φ hJ : GenSet A I → GenSet B J) :=
  fun _ _ h => Finset.image_subset_image h

/-- **The transport along the identity is the identity.** Only propositionally: `Finset.image` of
the identity is not the identity on the nose. -/
theorem map_id (S : GenSet A I) (hI : I = Ideal.map (RingHom.id A) I) :
    map (RingHom.id A) hI S = S := by
  refine ext ?_
  rw [map_carrier, show (Gen.map (RingHom.id A) hI : Gen A I → Gen A I) = id from
    funext fun x => Gen.map_id x hI, Finset.image_id]

/-- **The transports along two ring maps compose.** Only propositionally, for the same reason as
`Stacks.GenFamily.GenSet.map_id`. -/
theorem map_map (φ : A →+* B) (ψ : B →+* C) (hJ : J = Ideal.map φ I) (hK : K = Ideal.map ψ J)
    (hKA : K = Ideal.map (ψ.comp φ) I) (S : GenSet A I) :
    map ψ hK (map φ hJ S) = map (ψ.comp φ) hKA S := by
  refine ext ?_
  rw [map_carrier, map_carrier, map_carrier, Finset.image_image]
  exact Finset.image_congr fun x _ => Gen.map_map φ ψ hJ hK hKA x

end GenSet

/-! ### The product family -/

/-- **The index type of the product family of `S`**: one index into each family of `S`.

This type can be **empty** — precisely when some family of `S` has arity `0`, i.e. when `I = ⊥`.
No `Nonempty` instance is provided. -/
def Idx {I : Ideal A} (S : GenSet A I) : Type u := (x : {y // y ∈ S.carrier}) → Fin x.1.arity

namespace Idx

variable {I : Ideal A}

/-- The type of choices for `S` is finite. -/
instance instFintype (S : GenSet A I) : Fintype (Idx S) :=
  inferInstanceAs (Fintype ((x : {y // y ∈ S.carrier}) → Fin x.1.arity))

end Idx

variable {I : Ideal A} {J : Ideal B} {K : Ideal C}

/-- **The product family of `S`**: the product, over the families in `S`, of the chosen element of
each. -/
def famFun (S : GenSet A I) (c : Idx S) : A := ∏ x : {y // y ∈ S.carrier}, x.1.elts (c x)

/-- The number of members of the product family of `S`. -/
def famCard (S : GenSet A I) : ℕ := Fintype.card (Idx S)

/-- The reindexing of `Stacks.GenFamily.Idx S` along `Fin (famCard S)`. -/
def idxEquiv (S : GenSet A I) : Idx S ≃ Fin (famCard S) := Fintype.equivFin (Idx S)

/-- **The product family of `S`, indexed by `Fin (famCard S)`.** -/
def fam (S : GenSet A I) : Fin (famCard S) → A := fun k => famFun S ((idxEquiv S).symm k)

/-- The value of `fam S` at `k` is the value of `famFun S` at the choice corresponding to `k`. -/
theorem fam_apply (S : GenSet A I) (k : Fin (famCard S)) :
    fam S k = famFun S ((idxEquiv S).symm k) := rfl

/-- The value of `fam S` at the index of a choice `c` is `famFun S c`. -/
@[simp]
theorem fam_idxEquiv (S : GenSet A I) (c : Idx S) : fam S (idxEquiv S c) = famFun S c := by
  rw [fam_apply, Equiv.symm_apply_apply]

/-- The product family and its reindexing have the same values. -/
theorem range_fam_eq (S : GenSet A I) : Set.range (fam S) = Set.range (famFun S) :=
  (idxEquiv S).symm.surjective.range_comp (famFun S)

/-! ### The canonical index maps and the divisibility facts -/

/-- The inclusion of the index sets underlying an inclusion `S ≤ T` of indices. -/
def inclSub {S T : GenSet A I} (h : S ≤ T) (x : {y // y ∈ S.carrier}) : {y // y ∈ T.carrier} :=
  ⟨x.1, h x.2⟩

/-- The inclusion of index sets along `S ≤ T` is injective. -/
theorem inclSub_injective {S T : GenSet A I} (h : S ≤ T) :
    Function.Injective (inclSub h) := by
  intro a b hab
  have h1 : (inclSub h a).1 = (inclSub h b).1 := congrArg Subtype.val hab
  exact Subtype.ext h1

/-- **For `S ≤ T`, the restriction of a choice for `T` to a choice for `S`.** -/
def idxLeFun {S T : GenSet A I} (h : S ≤ T) (c : Idx T) : Idx S := fun x => c (inclSub h x)

/-- **For `S ≤ T`, the restriction of a choice for `T` to a choice for `S`**, through the
reindexings by `Fin`. -/
def idxLe {S T : GenSet A I} (h : S ≤ T) : Fin (famCard T) → Fin (famCard S) :=
  fun k => idxEquiv S (idxLeFun h ((idxEquiv T).symm k))

/-- Restriction of a choice along `S ≤ S` is the identity. -/
theorem idxLeFun_refl (S : GenSet A I) (c : Idx S) : idxLeFun (le_refl S) c = c := rfl

/-- Restriction of a choice along `T ≤ U` and then along `S ≤ T` is restriction along `S ≤ U`. -/
theorem idxLeFun_trans {S T U : GenSet A I} (h₁ : S ≤ T) (h₂ : T ≤ U) (c : Idx U) :
    idxLeFun h₁ (idxLeFun h₂ c) = idxLeFun (h₁.trans h₂) c := rfl

/-- **The comparison divisibility.** Along `S ≤ T` each value of the product family of `S` divides
the corresponding value of the product family of `T`: the latter is the former times the factors
contributed by the families of `T` outside `S`. -/
theorem famFun_dvd_of_le {S T : GenSet A I} (h : S ≤ T) (c : Idx T) :
    famFun S (idxLeFun h c) ∣ famFun T c := by
  have e : famFun S (idxLeFun h c)
      = ∏ z ∈ Finset.univ.image (inclSub h), z.1.elts (c z) := by
    rw [Finset.prod_image fun a _ b _ hab => inclSub_injective h hab]
    rfl
  rw [e, famFun]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)

/-- **The comparison divisibility**, through the reindexings by `Fin`. -/
theorem fam_dvd_of_le {S T : GenSet A I} (h : S ≤ T) (k : Fin (famCard T)) :
    fam S (idxLe h k) ∣ fam T k := by
  rw [idxLe, fam_idxEquiv]
  exact famFun_dvd_of_le h _

/-- The index map along `S ≤ S` is the identity. -/
@[simp]
theorem idxLe_refl (S : GenSet A I) : idxLe (le_refl S) = id := by
  funext k
  exact Equiv.apply_symm_apply _ _

/-- The index map along `S ≤ U` is the composite of those along `S ≤ T` and `T ≤ U`. -/
theorem idxLe_trans {S T U : GenSet A I} (h₁ : S ≤ T) (h₂ : T ≤ U) :
    idxLe (h₁.trans h₂) = idxLe h₁ ∘ idxLe h₂ := by
  funext k
  rw [Function.comp_apply, idxLe, idxLe, idxLe, Equiv.symm_apply_apply, idxLeFun_trans]

/-! ### The index maps of a ring map -/

/-- The map on index sets underlying the transport along a ring map. -/
def inclMap (φ : A →+* B) (hJ : J = Ideal.map φ I) (S : GenSet A I)
    (x : {y // y ∈ S.carrier}) : {y // y ∈ (GenSet.map φ hJ S).carrier} :=
  ⟨Gen.map φ hJ x.1, Finset.mem_image_of_mem _ x.2⟩

/-- **The restriction of a choice for `GenSet.map φ hJ S` to a choice for `S`.**

No cast appears: `(Gen.map φ hJ x.1).arity` is *definitionally* `x.1.arity`, the `arity` field
being copied verbatim by `Stacks.GenFamily.Gen.map`. -/
def idxMapFun (φ : A →+* B) (hJ : J = Ideal.map φ I) (S : GenSet A I)
    (c : Idx (GenSet.map φ hJ S)) : Idx S := fun x => c (inclMap φ hJ S x)

/-- **The restriction of a choice along the transport by a ring map**, through the reindexings by
`Fin`. -/
def idxMap (φ : A →+* B) (hJ : J = Ideal.map φ I) (S : GenSet A I) :
    Fin (famCard (GenSet.map φ hJ S)) → Fin (famCard S) :=
  fun k => idxEquiv S (idxMapFun φ hJ S ((idxEquiv (GenSet.map φ hJ S)).symm k))

/-- **The divisibility for a ring map.** The image of a value of the product family of `S` divides
the `S.carrier.card`-th power of the corresponding value of the product family of
`GenSet.map φ hJ S`.

The power is needed: `Gen.map φ hJ` need not be injective on `S.carrier`, so the image is a product
of `S.carrier.card` factors of `famFun (GenSet.map φ hJ S) c`, possibly repeated. -/
theorem map_famFun_dvd (φ : A →+* B) (hJ : J = Ideal.map φ I) (S : GenSet A I)
    (c : Idx (GenSet.map φ hJ S)) :
    φ (famFun S (idxMapFun φ hJ S c)) ∣ famFun (GenSet.map φ hJ S) c ^ S.carrier.card := by
  have e : φ (famFun S (idxMapFun φ hJ S c))
      = ∏ x : {y // y ∈ S.carrier}, (inclMap φ hJ S x).1.elts (c (inclMap φ hJ S x)) := by
    rw [famFun, map_prod]
    rfl
  have hcard : (Finset.univ : Finset {y // y ∈ S.carrier}).card = S.carrier.card := by
    simp
  rw [e, ← hcard, ← Finset.prod_const]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun x _ => ?_
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ (inclMap φ hJ S x))

/-- **The divisibility for a ring map**, through the reindexings by `Fin`. -/
theorem map_fam_dvd (φ : A →+* B) (hJ : J = Ideal.map φ I) (S : GenSet A I)
    (k : Fin (famCard (GenSet.map φ hJ S))) :
    φ (fam S (idxMap φ hJ S k)) ∣ fam (GenSet.map φ hJ S) k ^ S.carrier.card := by
  rw [idxMap, fam_idxEquiv]
  exact map_famFun_dvd φ hJ S _

/-! ### Coherence of the index maps -/

/-- **The index map of the identity is the transport along `GenSet.map_id`.** -/
theorem idxMapFun_id (S : GenSet A I) (hI : I = Ideal.map (RingHom.id A) I)
    (c : Idx (GenSet.map (RingHom.id A) hI S)) :
    idxMapFun (RingHom.id A) hI S c = idxLeFun (GenSet.map_id S hI).ge c := rfl

/-- **The index map of the identity is the transport along `GenSet.map_id`**, through the
reindexings by `Fin`. The two sides have the same type because `idxLe` for the inequality
`S ≤ GenSet.map (RingHom.id A) hI S` goes from `Fin (famCard (GenSet.map (RingHom.id A) hI S))` to
`Fin (famCard S)`; no cast is needed. -/
theorem idxMap_id (S : GenSet A I) (hI : I = Ideal.map (RingHom.id A) I) :
    idxMap (RingHom.id A) hI S = idxLe (GenSet.map_id S hI).ge := by
  rfl

/-- **The index maps of two ring maps compose**, modulo the transport along `GenSet.map_map`. -/
theorem idxMapFun_comp (φ : A →+* B) (ψ : B →+* C) (hJ : J = Ideal.map φ I)
    (hK : K = Ideal.map ψ J) (hKA : K = Ideal.map (ψ.comp φ) I) (S : GenSet A I)
    (c : Idx (GenSet.map ψ hK (GenSet.map φ hJ S))) :
    idxMapFun φ hJ S (idxMapFun ψ hK (GenSet.map φ hJ S) c)
      = idxMapFun (ψ.comp φ) hKA S
          (idxLeFun (GenSet.map_map φ ψ hJ hK hKA S).ge c) := rfl

/-- **The index maps of two ring maps compose**, modulo the transport along `GenSet.map_map`,
through the reindexings by `Fin`. -/
theorem idxMap_comp (φ : A →+* B) (ψ : B →+* C) (hJ : J = Ideal.map φ I)
    (hK : K = Ideal.map ψ J) (hKA : K = Ideal.map (ψ.comp φ) I) (S : GenSet A I) :
    idxMap φ hJ S ∘ idxMap ψ hK (GenSet.map φ hJ S)
      = idxMap (ψ.comp φ) hKA S ∘ idxLe (GenSet.map_map φ ψ hJ hK hKA S).ge := by
  funext k
  rw [Function.comp_apply, Function.comp_apply, idxMap, idxMap, idxMap, idxLe,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, idxMapFun_comp]

/-- **The index map of a ring map commutes with the comparison maps of the system.** -/
theorem idxLeFun_idxMapFun {S T : GenSet A I} (h : S ≤ T) (φ : A →+* B)
    (hJ : J = Ideal.map φ I) :
    idxMapFun φ hJ S ∘ idxLeFun (GenSet.map_monotone φ hJ h) =
      idxLeFun h ∘ idxMapFun φ hJ T := rfl

/-- **The index map of a ring map commutes with the comparison maps of the system**, through the
reindexings by `Fin`. -/
theorem idxLe_idxMap {S T : GenSet A I} (h : S ≤ T) (φ : A →+* B) (hJ : J = Ideal.map φ I) :
    idxMap φ hJ S ∘ idxLe (GenSet.map_monotone φ hJ h) =
      idxLe h ∘ idxMap φ hJ T := by
  funext k
  rw [Function.comp_apply, Function.comp_apply, idxMap, idxLe, idxLe, idxMap,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

/-! ### The zero locus of the product family -/

/-- **Every value of the product family of `S` lies in `I`**: it is a product with at least one
factor in `I`, `S` being nonempty. -/
theorem famFun_mem (S : GenSet A I) (c : Idx S) : famFun S c ∈ I := by
  obtain ⟨x, hx⟩ := S.nonempty'
  obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem (fun z : {y // y ∈ S.carrier} => z.1.elts (c z))
    (Finset.mem_univ (⟨x, hx⟩ : {y // y ∈ S.carrier}))
  rw [famFun, hd]
  exact Ideal.mul_mem_right _ _ (Gen.elts_mem x _)

/-- **The product family of `S` consists of elements of `I`.** -/
theorem range_fam_subset (S : GenSet A I) : Set.range (fam S) ⊆ (I : Set A) := by
  rw [range_fam_eq]
  rintro a ⟨c, rfl⟩
  exact famFun_mem S c

/-- A prime containing every value of the product family of `S` contains one of the families of
`S` entirely. This is the step with content in `Stacks.GenFamily.zeroLocus_range_fam`: were every
family of `S` to have an element outside the prime, choosing one such element from each family
would give a value of the product family outside the prime, a product being in a prime only if one
of its factors is. -/
theorem exists_forall_elts_mem_of_famFun_mem {S : GenSet A I} {p : Ideal A} (hp : p.IsPrime)
    (h : ∀ c : Idx S, famFun S c ∈ p) :
    ∃ x ∈ S.carrier, ∀ i : Fin x.arity, x.elts i ∈ p := by
  by_contra hcon
  simp only [not_exists, not_and, not_forall] at hcon
  have hchoice : ∀ z : {y // y ∈ S.carrier}, ∃ i : Fin z.1.arity, z.1.elts i ∉ p :=
    fun z => hcon z.1 z.2
  obtain ⟨c, hc⟩ := Classical.axiomOfChoice hchoice
  have hmem : ∏ z : {y // y ∈ S.carrier}, (z : Gen A I).elts (c z) ∈ p := h c
  obtain ⟨z, -, hz⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hp)).1 hmem
  exact hc z hz

/-- **The product family of `S` has the same zero locus as `I`.** Its values lie in `I`, which
gives one inclusion; for the other, a prime containing every value of the product family contains
one of the generating families of `S` entirely, hence contains `I`. -/
theorem zeroLocus_range_fam (S : GenSet A I) :
    PrimeSpectrum.zeroLocus (Set.range (fam S)) = PrimeSpectrum.zeroLocus (I : Set A) := by
  refine le_antisymm ?_ (PrimeSpectrum.zeroLocus_anti_mono (range_fam_subset S))
  intro p hp
  rw [PrimeSpectrum.mem_zeroLocus, range_fam_eq, Set.range_subset_iff] at hp
  obtain ⟨x, -, hx⟩ := exists_forall_elts_mem_of_famFun_mem p.isPrime hp
  rw [PrimeSpectrum.mem_zeroLocus]
  intro a ha
  rw [← x.span_eq] at ha
  exact Ideal.span_le.2 (by rintro b ⟨i, rfl⟩; exact hx i) ha

/-- **The ideal generated by the product family of `S` has the same zero locus as `I`.** -/
theorem zeroLocus_span_range_fam (S : GenSet A I) :
    PrimeSpectrum.zeroLocus ((Ideal.span (Set.range (fam S)) : Ideal A) : Set A) =
      PrimeSpectrum.zeroLocus (I : Set A) := by
  rw [PrimeSpectrum.zeroLocus_span, zeroLocus_range_fam]

/-- **The ideal generated by the product family of `S` is finitely generated**: the product family
is a finite family. -/
theorem fg_span_range_fam (S : GenSet A I) : (Ideal.span (Set.range (fam S))).FG :=
  Submodule.fg_iff_exists_fin_generating_family.2 ⟨famCard S, fam S, rfl⟩

/-! ### Single families -/

/-- **The index given by a single generating family.** -/
def single (x : Gen A I) : GenSet A I := ⟨{x}, Finset.singleton_nonempty x⟩

/-- The underlying finite set of `single x` is `{x}`. -/
@[simp]
theorem single_carrier (x : Gen A I) : (single x).carrier = {x} := rfl

/-- **A single generating family appears in `S` exactly when `S` dominates its singleton.** -/
theorem single_le_iff (x : Gen A I) (S : GenSet A I) : single x ≤ S ↔ x ∈ S.carrier :=
  Finset.singleton_subset_iff

/-- **The transport of a singleton index is the singleton on the transported family.** -/
theorem map_single (φ : A →+* B) (hJ : J = Ideal.map φ I) (x : Gen A I) :
    GenSet.map φ hJ (single x) = single (Gen.map φ hJ x) :=
  GenSet.ext (by rw [GenSet.map_carrier, single_carrier, Finset.image_singleton, single_carrier])

/-- The index set of a singleton index has exactly one element, namely the family itself. -/
instance instUniqueSingleCarrier (x : Gen A I) :
    Unique {y : Gen A I // y ∈ (single x).carrier} where
  default := ⟨x, Finset.mem_singleton_self x⟩
  uniq y := Subtype.ext (Finset.mem_singleton.1 y.2)

/-- **A choice for a singleton index is just an index into the single family.** -/
def idxSingleEquiv (x : Gen A I) : Idx (single x) ≃ Fin x.arity :=
  Equiv.piUnique fun y : {z : Gen A I // z ∈ (single x).carrier} => Fin y.1.arity

/-- The product family of a singleton index is the single family itself, read through
`Stacks.GenFamily.idxSingleEquiv`. -/
theorem famFun_single (x : Gen A I) (c : Idx (single x)) :
    famFun (single x) c = x.elts (idxSingleEquiv x c) := by
  rw [famFun, Fintype.prod_unique]
  rfl

/-- **The reindexing of the product family of a singleton index onto the family itself**: a
bijection `Fin (famCard (single x)) → Fin x.arity` along which the two families agree
(`Stacks.GenFamily.fam_single_apply`). -/
def singleIdx (x : Gen A I) (k : Fin (famCard (single x))) : Fin x.arity :=
  idxSingleEquiv x ((idxEquiv (single x)).symm k)

/-- `singleIdx x k` is the index into `x` of the choice corresponding to `k`. -/
theorem singleIdx_apply (x : Gen A I) (k : Fin (famCard (single x))) :
    singleIdx x k = idxSingleEquiv x ((idxEquiv (single x)).symm k) := rfl

/-- The reindexing `singleIdx x` is a bijection. -/
theorem singleIdx_bijective (x : Gen A I) : Function.Bijective (singleIdx x) :=
  ((idxEquiv (single x)).symm.trans (idxSingleEquiv x)).bijective

/-- **The product family of a singleton index is the single family itself**, reindexed along
`Stacks.GenFamily.singleIdx`. -/
theorem fam_single_apply (x : Gen A I) (k : Fin (famCard (single x))) :
    fam (single x) k = x.elts (singleIdx x k) :=
  (fam_apply (single x) k).trans (famFun_single x _)

/-- Each element `x.elts (singleIdx x k)` divides a power of `fam (single x) k`. -/
theorem exists_dvd_fam_single (x : Gen A I) (k : Fin (famCard (single x))) :
    ∃ n : ℕ, x.elts (singleIdx x k) ∣ fam (single x) k ^ n := by
  refine ⟨1, ?_⟩
  rw [pow_one, fam_single_apply]

/-- **The product family of a singleton index is the single family itself**, up to the bijection of
index sets coming from `Stacks.GenFamily.idxSingleEquiv` and the reindexing by `Fin`. -/
theorem exists_bijective_single (x : Gen A I) :
    ∃ σ : Fin (famCard (single x)) → Fin x.arity,
      Function.Bijective σ ∧ ∀ k, fam (single x) k = x.elts (σ k) :=
  ⟨singleIdx x, singleIdx_bijective x, fam_single_apply x⟩

/-- **The reindexing of a singleton index is compatible with the transport along a ring map.**
Along the equality `GenSet.map φ (single x) = single (Gen.map φ x)` of
`Stacks.GenFamily.map_single`, restricting a choice to the singleton on the image family and
restricting it along the transport are the same operation, so the two reindexings of the two
singleton product families onto `Fin x.arity` agree. -/
theorem singleIdx_idxLe_heq (φ : A →+* B) (hJ : J = Ideal.map φ I) (x : Gen A I) (y : Gen B J)
    (hxy : y = Gen.map φ hJ x) (h₀ : single y ≤ GenSet.map φ hJ (single x))
    (k : Fin (famCard (GenSet.map φ hJ (single x)))) :
    HEq (singleIdx y (idxLe h₀ k)) (singleIdx x (idxMap φ hJ (single x) k)) := by
  subst hxy
  refine heq_of_eq ?_
  rw [singleIdx_apply, singleIdx_apply, idxLe, idxMap, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  rfl

end Stacks.GenFamily

end
