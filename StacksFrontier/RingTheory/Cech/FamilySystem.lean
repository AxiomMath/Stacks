module

public import StacksFrontier.RingTheory.Cech.GeneralReindexBaseChange

/-!
# Systems of distinguished finite families of sections of a presheaf of rings

Let `R` be a presheaf of commutative rings on a category `C`. A **family system** on `R`
(`Stacks.CechFamilySystem.FamilySystem`) singles out, over each object, a class of finite families
of sections, stable under restriction. Out of one the file builds the index system of the Čech
colimit:

* over each object, the **nonempty finite sets of distinguished families**
  (`Stacks.CechFamilySystem.FamilySystem.GenSet`), a directed join-semilattice under inclusion;
* the **product family** of such a finite set (`Stacks.CechFamilySystem.FamilySystem.fam`) — one
  factor chosen out of each family of the set — together with the two divisibility facts that make
  the extended Čech complexes of the product families into a diagram: along an inclusion of index
  sets each value of the smaller product family divides the corresponding value of the larger
  (`Stacks.CechFamilySystem.FamilySystem.fam_dvd_of_le`), and along a restriction map of the
  presheaf the image of a value divides a power of the corresponding value of the restricted index
  (`Stacks.CechFamilySystem.FamilySystem.map_fam_dvd`).

This is the index system of [Stacks, Tag 099D] — `Stacks.GenFamily.GenSet`, the finite sets of
finite generating families of a fixed finitely generated ideal of a fixed ring — with the ring
replaced by a presheaf of rings and the generating condition replaced by an arbitrary
restriction-stable condition. The condition has to be weakened: over a site, the finite families
that generate a sheaf of ideals on the slice at an object do **not** all span one ideal of sections
there, so the condition "spans `I`" of the tag has no sectionwise meaning, while the condition
"generates `ℐ` locally" does.

## Main definitions

* `Stacks.CechFamilySystem.FamilySystem`: the condition, stable under restriction.
* `Stacks.CechFamilySystem.FamilySystem.Gen`: a distinguished family over an object, and
  `Stacks.CechFamilySystem.FamilySystem.Gen.map` its restriction.
* `Stacks.CechFamilySystem.FamilySystem.GenSet`: a nonempty finite set of distinguished families,
  with `Stacks.CechFamilySystem.FamilySystem.GenSet.map` its restriction.
* `Stacks.CechFamilySystem.FamilySystem.fam`: the product family.

## Main results

* `Stacks.CechFamilySystem.FamilySystem.fam_dvd_of_le` and
  `Stacks.CechFamilySystem.FamilySystem.map_fam_dvd`: the two divisibility facts.
* `Stacks.CechFamilySystem.FamilySystem.idxMap_id`,
  `Stacks.CechFamilySystem.FamilySystem.idxMap_comp` and
  `Stacks.CechFamilySystem.FamilySystem.idxLe_idxMap`: the coherence of the index maps.

## Implementation notes

The arity of a distinguished family is a field of the structure and the restriction copies it
verbatim, so `(x.map a).arity` is *definitionally* `x.arity` and the index types of a family and
of its restriction are definitionally equal. That is what keeps casts out of the index maps
below. The restriction along an identity, and the composite of two restrictions, are by contrast
only *propositional* identities — `R.map (𝟙 V)` is the identity only up to `R.map_id` — which is
all a presheaf of modules asks of them.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace Stacks.CechFamilySystem

variable {C : Type u} [Category.{u} C]

/-- **A system of distinguished finite families of sections of a presheaf of commutative rings**:
a condition on the finite families of sections over each object, stable under restriction. -/
structure FamilySystem (R : Cᵒᵖ ⥤ CommRingCat.{u}) where
  /-- The condition on a finite family of sections over an object. -/
  Mem : ∀ {V : Cᵒᵖ} {n : ℕ}, (Fin n → R.obj V) → Prop
  /-- The condition is stable under restriction. -/
  Mem_map : ∀ {V W : Cᵒᵖ} (a : V ⟶ W) {n : ℕ} {f : Fin n → R.obj V},
    Mem f → Mem fun i => (R.map a).hom (f i)

namespace FamilySystem

variable {R : Cᵒᵖ ⥤ CommRingCat.{u}} (F : FamilySystem R)

/-! ### Distinguished families -/

/-- **A distinguished family of sections over an object.** -/
structure Gen (V : Cᵒᵖ) where
  /-- The number of sections in the family. -/
  arity : ℕ
  /-- The sections of the family. -/
  elts : Fin arity → R.obj V
  /-- The family is distinguished. -/
  mem : F.Mem elts

namespace Gen

variable {F}

/-- Equality of distinguished families is decided classically. -/
instance {V : Cᵒᵖ} : DecidableEq (F.Gen V) := Classical.decEq _

/-- Two distinguished families with the same arity and the same sections are equal: the
remaining field is a proposition. -/
theorem ext_elts {V : Cᵒᵖ} {n : ℕ} {f g : Fin n → R.obj V} (hf : F.Mem f) (hg : F.Mem g)
    (h : f = g) : (⟨n, f, hf⟩ : F.Gen V) = ⟨n, g, hg⟩ := by
  subst h
  rfl

/-- **The restriction of a distinguished family** along a restriction map of the presheaf. The
arity is copied verbatim. -/
def map {V W : Cᵒᵖ} (a : V ⟶ W) (x : F.Gen V) : F.Gen W where
  arity := x.arity
  elts i := (R.map a).hom (x.elts i)
  mem := F.Mem_map a x.mem

/-- The restriction of a distinguished family has the same arity. -/
@[simp]
theorem map_arity {V W : Cᵒᵖ} (a : V ⟶ W) (x : F.Gen V) : (map a x).arity = x.arity := rfl

/-- The sections of the restriction are the images of the sections under the restriction map. -/
@[simp]
theorem map_elts {V W : Cᵒᵖ} (a : V ⟶ W) (x : F.Gen V) (i : Fin x.arity) :
    (map a x).elts i = (R.map a).hom (x.elts i) := rfl

/-- **The restriction along an identity is the family itself.** Only propositionally: the
restriction map of the presheaf along an identity is the identity only up to `R.map_id`. -/
theorem map_id {V : Cᵒᵖ} (x : F.Gen V) : map (𝟙 V) x = x := by
  refine ext_elts (F.Mem_map (𝟙 V) x.mem) x.mem (funext fun i => ?_)
  rw [congrArg CommRingCat.Hom.hom (R.map_id V)]
  rfl

/-- **The restrictions along two composable arrows compose.** Only propositionally, for the same
reason as `Stacks.CechFamilySystem.FamilySystem.Gen.map_id`. -/
theorem map_map {V W Y : Cᵒᵖ} (a : V ⟶ W) (b : W ⟶ Y) (x : F.Gen V) :
    map b (map a x) = map (a ≫ b) x := by
  refine ext_elts (F.Mem_map b (F.Mem_map a x.mem)) (F.Mem_map (a ≫ b) x.mem) (funext fun i => ?_)
  rw [congrArg CommRingCat.Hom.hom (R.map_comp a b)]
  rfl

end Gen

/-! ### The directed poset of nonempty finite sets of distinguished families -/

/-- **A nonempty finite set of distinguished families over an object** — an object of the index
system. -/
structure GenSet (V : Cᵒᵖ) where
  /-- The finite set of distinguished families. -/
  carrier : Finset (F.Gen V)
  /-- It is nonempty. -/
  nonempty' : carrier.Nonempty

namespace GenSet

variable {F}

/-- Two indices with the same underlying finite set are equal. -/
@[ext]
theorem ext {V : Cᵒᵖ} : ∀ {S T : F.GenSet V}, S.carrier = T.carrier → S = T
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- **The order on the index system: inclusion of the underlying finite sets.** -/
instance instPartialOrder (V : Cᵒᵖ) : PartialOrder (F.GenSet V) where
  le S T := S.carrier ⊆ T.carrier
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ h₁ h₂ := Finset.Subset.trans h₁ h₂
  le_antisymm _ _ h₁ h₂ := ext (Finset.Subset.antisymm h₁ h₂)

/-- `S ≤ T` exactly when the finite set of `S` is contained in that of `T`. -/
@[simp]
theorem le_iff {V : Cᵒᵖ} {S T : F.GenSet V} : S ≤ T ↔ S.carrier ⊆ T.carrier := Iff.rfl

/-- **The index system is a join-semilattice**, the join being the union. -/
instance instSemilatticeSup (V : Cᵒᵖ) : SemilatticeSup (F.GenSet V) where
  sup S T := ⟨S.carrier ∪ T.carrier, S.nonempty'.mono Finset.subset_union_left⟩
  le_sup_left _ _ := Finset.subset_union_left
  le_sup_right _ _ := Finset.subset_union_right
  sup_le _ _ _ h₁ h₂ := Finset.union_subset h₁ h₂

/-- The underlying finite set of `S ⊔ T` is the union of those of `S` and `T`. -/
@[simp]
theorem sup_carrier {V : Cᵒᵖ} (S T : F.GenSet V) :
    (S ⊔ T).carrier = S.carrier ∪ T.carrier := rfl

/-- The index system is directed: `S ⊔ T` is an upper bound of `S` and `T`. -/
instance instIsDirected (V : Cᵒᵖ) : IsDirected (F.GenSet V) (· ≤ ·) :=
  ⟨fun S T => ⟨S ⊔ T, le_sup_left, le_sup_right⟩⟩

/-- **The restriction of an index**: restrict every family of `S`. -/
def map {V W : Cᵒᵖ} (a : V ⟶ W) (S : F.GenSet V) : F.GenSet W where
  carrier := S.carrier.image (Gen.map a)
  nonempty' := S.nonempty'.image _

/-- The underlying finite set of the restriction of `S` is the image of that of `S` under
`Stacks.CechFamilySystem.FamilySystem.Gen.map`. -/
@[simp]
theorem map_carrier {V W : Cᵒᵖ} (a : V ⟶ W) (S : F.GenSet V) :
    (map a S).carrier = S.carrier.image (Gen.map a) := rfl

/-- **Restriction of indices is monotone.** -/
theorem map_monotone {V W : Cᵒᵖ} (a : V ⟶ W) : Monotone (map a : F.GenSet V → F.GenSet W) :=
  fun _ _ h => Finset.image_subset_image h

/-- **The restriction along an identity is the identity.** Only propositionally:
`Finset.image` of the identity is not the identity on the nose. -/
theorem map_id {V : Cᵒᵖ} (S : F.GenSet V) : map (𝟙 V) S = S := by
  refine ext ?_
  rw [map_carrier, show (Gen.map (𝟙 V) : F.Gen V → F.Gen V) = id from
    funext fun x => Gen.map_id x, Finset.image_id]

/-- **The restrictions of indices compose.** Only propositionally, for the same reason as
`Stacks.CechFamilySystem.FamilySystem.GenSet.map_id`. -/
theorem map_map {V W Y : Cᵒᵖ} (a : V ⟶ W) (b : W ⟶ Y) (S : F.GenSet V) :
    map b (map a S) = map (a ≫ b) S := by
  refine ext ?_
  rw [map_carrier, map_carrier, map_carrier, Finset.image_image]
  exact Finset.image_congr fun x _ => Gen.map_map a b x

end GenSet

/-! ### The product family -/

variable {F}

/-- **The index type of the product family of `S`**: one index into each family of `S`.

This type can be **empty** — precisely when some family of `S` has arity `0`. No `Nonempty`
instance is provided. -/
def Idx {V : Cᵒᵖ} (S : F.GenSet V) : Type u := (x : {y // y ∈ S.carrier}) → Fin x.1.arity

/-- The index type of the product family of `S` is finite. -/
instance instFintypeIdx {V : Cᵒᵖ} (S : F.GenSet V) : Fintype (Idx S) :=
  inferInstanceAs (Fintype ((x : {y // y ∈ S.carrier}) → Fin x.1.arity))

/-- **The product family of `S`**: the product, over the families in `S`, of the chosen section of
each. -/
def famFun {V : Cᵒᵖ} (S : F.GenSet V) (c : Idx S) : R.obj V :=
  ∏ x : {y // y ∈ S.carrier}, x.1.elts (c x)

/-- The number of members of the product family of `S`. -/
def famCard {V : Cᵒᵖ} (S : F.GenSet V) : ℕ := Fintype.card (Idx S)

/-- The reindexing of `Stacks.CechFamilySystem.FamilySystem.Idx` by `Fin (famCard S)`. -/
def idxEquiv {V : Cᵒᵖ} (S : F.GenSet V) : Idx S ≃ Fin (famCard S) := Fintype.equivFin (Idx S)

/-- **The product family of `S`, indexed by `Fin (famCard S)`.** -/
def fam {V : Cᵒᵖ} (S : F.GenSet V) : Fin (famCard S) → R.obj V :=
  fun k => famFun S ((idxEquiv S).symm k)

/-- The value of `fam S` at `k` is the value of `famFun S` at the corresponding choice. -/
theorem fam_apply {V : Cᵒᵖ} (S : F.GenSet V) (k : Fin (famCard S)) :
    fam S k = famFun S ((idxEquiv S).symm k) := rfl

/-- The value of `fam S` at the reindexing of a choice `c` is `famFun S c`. -/
@[simp]
theorem fam_idxEquiv {V : Cᵒᵖ} (S : F.GenSet V) (c : Idx S) : fam S (idxEquiv S c) = famFun S c :=
  by rw [fam_apply, Equiv.symm_apply_apply]

/-- The product family and its reindexing have the same values. -/
theorem range_fam_eq {V : Cᵒᵖ} (S : F.GenSet V) : Set.range (fam S) = Set.range (famFun S) :=
  (idxEquiv S).symm.surjective.range_comp (famFun S)

/-! ### The index maps of an inclusion -/

/-- The inclusion of the index sets underlying an inclusion `S ≤ T` of indices. -/
def inclSub {V : Cᵒᵖ} {S T : F.GenSet V} (h : S ≤ T) (x : {y // y ∈ S.carrier}) :
    {y // y ∈ T.carrier} := ⟨x.1, h x.2⟩

/-- The inclusion of index sets underlying `S ≤ T` is injective. -/
theorem inclSub_injective {V : Cᵒᵖ} {S T : F.GenSet V} (h : S ≤ T) :
    Function.Injective (inclSub h) := by
  intro a b hab
  have h1 : (inclSub h a).1 = (inclSub h b).1 := congrArg Subtype.val hab
  exact Subtype.ext h1

/-- **For `S ≤ T`, the restriction of a choice for `T` to a choice for `S`.** -/
def idxLeFun {V : Cᵒᵖ} {S T : F.GenSet V} (h : S ≤ T) (c : Idx T) : Idx S :=
  fun x => c (inclSub h x)

/-- **For `S ≤ T`, the restriction of a choice for `T` to a choice for `S`**, through the
reindexings by `Fin`. -/
def idxLe {V : Cᵒᵖ} {S T : F.GenSet V} (h : S ≤ T) : Fin (famCard T) → Fin (famCard S) :=
  fun k => idxEquiv S (idxLeFun h ((idxEquiv T).symm k))

/-- The restriction of a choice along `S ≤ S` is the choice itself. -/
theorem idxLeFun_refl {V : Cᵒᵖ} (S : F.GenSet V) (c : Idx S) : idxLeFun (le_refl S) c = c := rfl

/-- The restrictions of choices along `S ≤ T` and `T ≤ U` compose to the restriction along
`S ≤ U`. -/
theorem idxLeFun_trans {V : Cᵒᵖ} {S T U : F.GenSet V} (h₁ : S ≤ T) (h₂ : T ≤ U) (c : Idx U) :
    idxLeFun h₁ (idxLeFun h₂ c) = idxLeFun (h₁.trans h₂) c := rfl

/-- **The comparison divisibility.** Along `S ≤ T` each value of the product family of `S` divides
the corresponding value of the product family of `T`: the latter is the former times the factors
contributed by the families of `T` outside `S`. -/
theorem famFun_dvd_of_le {V : Cᵒᵖ} {S T : F.GenSet V} (h : S ≤ T) (c : Idx T) :
    famFun S (idxLeFun h c) ∣ famFun T c := by
  have e : famFun S (idxLeFun h c)
      = ∏ z ∈ Finset.univ.image (inclSub h), z.1.elts (c z) := by
    rw [Finset.prod_image fun a _ b _ hab => inclSub_injective h hab]
    rfl
  rw [e, famFun]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)

/-- **The comparison divisibility**, through the reindexings by `Fin`. -/
theorem fam_dvd_of_le {V : Cᵒᵖ} {S T : F.GenSet V} (h : S ≤ T) (k : Fin (famCard T)) :
    fam S (idxLe h k) ∣ fam T k := by
  rw [fam_apply, idxLe, Equiv.symm_apply_apply, fam_apply]
  exact famFun_dvd_of_le h _

/-- Each value of the product family of `S` divides a power of the corresponding value of the
product family of `T`. -/
theorem exists_dvd_fam_of_le {V : Cᵒᵖ} {S T : F.GenSet V} (h : S ≤ T) (k : Fin (famCard T)) :
    ∃ n : ℕ, fam S (idxLe h k) ∣ fam T k ^ n :=
  ⟨1, by rw [pow_one]; exact fam_dvd_of_le h k⟩

/-- The restriction of choices along `S ≤ S`, through the reindexings by `Fin`, is the
identity. -/
@[simp]
theorem idxLe_refl {V : Cᵒᵖ} (S : F.GenSet V) : idxLe (le_refl S) = id := by
  funext k
  exact Equiv.apply_symm_apply _ _

/-- The restrictions of choices along `S ≤ T` and `T ≤ U`, through the reindexings by `Fin`,
compose to the restriction along `S ≤ U`. -/
theorem idxLe_trans {V : Cᵒᵖ} {S T U : F.GenSet V} (h₁ : S ≤ T) (h₂ : T ≤ U) :
    idxLe (h₁.trans h₂) = idxLe h₁ ∘ idxLe h₂ := by
  funext k
  rw [Function.comp_apply, idxLe, idxLe, idxLe, Equiv.symm_apply_apply, idxLeFun_trans]

/-! ### The index maps of a restriction -/

/-- The map on index sets underlying the restriction along an arrow of the presheaf. -/
def inclMap {V W : Cᵒᵖ} (a : V ⟶ W) (S : F.GenSet V) (x : {y // y ∈ S.carrier}) :
    {y // y ∈ (GenSet.map a S).carrier} :=
  ⟨Gen.map a x.1, Finset.mem_image_of_mem _ x.2⟩

/-- **The restriction of a choice for `GenSet.map a S` to a choice for `S`.**

No cast appears: `(Gen.map a x.1).arity` is *definitionally* `x.1.arity`, the arity being copied
verbatim by `Stacks.CechFamilySystem.FamilySystem.Gen.map`. -/
def idxMapFun {V W : Cᵒᵖ} (a : V ⟶ W) (S : F.GenSet V) (c : Idx (GenSet.map a S)) : Idx S :=
  fun x => c (inclMap a S x)

/-- **The restriction of a choice along an arrow of the presheaf**, through the reindexings by
`Fin`. -/
def idxMap {V W : Cᵒᵖ} (a : V ⟶ W) (S : F.GenSet V) :
    Fin (famCard (GenSet.map a S)) → Fin (famCard S) :=
  fun k => idxEquiv S (idxMapFun a S ((idxEquiv (GenSet.map a S)).symm k))

/-- **The divisibility for a restriction.** The image of a value of the product family of `S`
divides the `S.carrier.card`-th power of the corresponding value of the product family of the
restricted index.

The power is needed: `Gen.map a` need not be injective on `S.carrier`, so the image is a product
of `S.carrier.card` factors of `famFun (GenSet.map a S) c`, possibly repeated. -/
theorem map_famFun_dvd {V W : Cᵒᵖ} (a : V ⟶ W) (S : F.GenSet V) (c : Idx (GenSet.map a S)) :
    (R.map a).hom (famFun S (idxMapFun a S c)) ∣
      famFun (GenSet.map a S) c ^ S.carrier.card := by
  have e : (R.map a).hom (famFun S (idxMapFun a S c))
      = ∏ x : {y // y ∈ S.carrier}, (inclMap a S x).1.elts (c (inclMap a S x)) := by
    rw [famFun, map_prod]
    rfl
  have hcard : (Finset.univ : Finset {y // y ∈ S.carrier}).card = S.carrier.card := by
    simp
  rw [e, ← hcard, ← Finset.prod_const]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun x _ => ?_
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ (inclMap a S x))

/-- **The divisibility for a restriction**, through the reindexings by `Fin`. -/
theorem map_fam_dvd {V W : Cᵒᵖ} (a : V ⟶ W) (S : F.GenSet V)
    (k : Fin (famCard (GenSet.map a S))) :
    (R.map a).hom (fam S (idxMap a S k)) ∣ fam (GenSet.map a S) k ^ S.carrier.card := by
  rw [fam_apply, idxMap, Equiv.symm_apply_apply, fam_apply]
  exact map_famFun_dvd a S _

/-- The image of a value of the product family of `S` divides a power of the corresponding value
of the product family of the restricted index. -/
theorem exists_dvd_map_fam {V W : Cᵒᵖ} (a : V ⟶ W) (S : F.GenSet V)
    (k : Fin (famCard (GenSet.map a S))) :
    ∃ n : ℕ, (R.map a).hom (fam S (idxMap a S k)) ∣ fam (GenSet.map a S) k ^ n :=
  ⟨S.carrier.card, map_fam_dvd a S k⟩

/-! ### Coherence of the index maps -/

/-- A choice takes the same value at two members of the index set with equal underlying
families. -/
private theorem idx_val_congr {V : Cᵒᵖ} {S : F.GenSet V} (c : Idx S)
    {x y : {z // z ∈ S.carrier}} (h : x.1 = y.1) : (c x).val = (c y).val :=
  congrArg (fun z : {z // z ∈ S.carrier} => (c z).val) (Subtype.ext h)

/-- **The index map of an identity is the transport along `GenSet.map_id`.** -/
theorem idxMapFun_id {V : Cᵒᵖ} (S : F.GenSet V) (c : Idx (GenSet.map (𝟙 V) S)) :
    idxMapFun (𝟙 V) S c = idxLeFun (GenSet.map_id S).ge c := by
  exact funext fun x => Fin.val_injective (idx_val_congr c (Gen.map_id x.1))

/-- **The index map of an identity is the transport along `GenSet.map_id`**, through the
reindexings by `Fin`. -/
theorem idxMap_id {V : Cᵒᵖ} (S : F.GenSet V) : idxMap (𝟙 V) S = idxLe (GenSet.map_id S).ge := by
  funext k
  rw [idxMap, idxLe, idxMapFun_id]

/-- **The index maps of two composable arrows compose**, modulo the transport along
`GenSet.map_map`. -/
theorem idxMapFun_comp {V W Y : Cᵒᵖ} (a : V ⟶ W) (b : W ⟶ Y) (S : F.GenSet V)
    (c : Idx (GenSet.map b (GenSet.map a S))) :
    idxMapFun a S (idxMapFun b (GenSet.map a S) c)
      = idxMapFun (a ≫ b) S (idxLeFun (GenSet.map_map a b S).ge c) := by
  exact funext fun x => Fin.val_injective (idx_val_congr c (Gen.map_map a b x.1))

/-- **The index maps of two composable arrows compose**, modulo the transport along
`GenSet.map_map`, through the reindexings by `Fin`. -/
theorem idxMap_comp {V W Y : Cᵒᵖ} (a : V ⟶ W) (b : W ⟶ Y) (S : F.GenSet V) :
    idxMap a S ∘ idxMap b (GenSet.map a S)
      = idxMap (a ≫ b) S ∘ idxLe (GenSet.map_map a b S).ge := by
  funext k
  rw [Function.comp_apply, Function.comp_apply, idxMap, idxMap, idxMap, idxLe,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, idxMapFun_comp]

/-- **The index map of a restriction commutes with the comparison maps of the system.** -/
theorem idxLeFun_idxMapFun {V W : Cᵒᵖ} {S T : F.GenSet V} (h : S ≤ T) (a : V ⟶ W) :
    idxMapFun a S ∘ idxLeFun (GenSet.map_monotone a h) = idxLeFun h ∘ idxMapFun a T := rfl

/-- **The index map of a restriction commutes with the comparison maps of the system**, through
the reindexings by `Fin`. -/
theorem idxLe_idxMap {V W : Cᵒᵖ} {S T : F.GenSet V} (h : S ≤ T) (a : V ⟶ W) :
    idxMap a S ∘ idxLe (GenSet.map_monotone a h) = idxLe h ∘ idxMap a T := by
  funext k
  rw [Function.comp_apply, Function.comp_apply, idxMap, idxLe, idxLe, idxMap,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

/-! ### Single families -/

/-- **The index given by a single distinguished family.** -/
def single {V : Cᵒᵖ} (x : F.Gen V) : F.GenSet V := ⟨{x}, Finset.singleton_nonempty x⟩

/-- The underlying finite set of the singleton index on `x` is the singleton `{x}`. -/
@[simp]
theorem single_carrier {V : Cᵒᵖ} (x : F.Gen V) : (single x).carrier = {x} := rfl

/-- **A single family appears in `S` exactly when `S` dominates its singleton.** -/
theorem single_le_iff {V : Cᵒᵖ} (x : F.Gen V) (S : F.GenSet V) :
    single x ≤ S ↔ x ∈ S.carrier := Finset.singleton_subset_iff

/-- **The restriction of a singleton index is the singleton on the restricted family.** -/
theorem map_single {V W : Cᵒᵖ} (a : V ⟶ W) (x : F.Gen V) :
    GenSet.map a (single x) = single (Gen.map a x) :=
  GenSet.ext (by rw [GenSet.map_carrier, single_carrier, Finset.image_singleton, single_carrier])

/-- The index set of a singleton index has exactly one element, namely the family itself. -/
instance instUniqueSingleCarrier {V : Cᵒᵖ} (x : F.Gen V) :
    Unique {y : F.Gen V // y ∈ (single x).carrier} where
  default := ⟨x, Finset.mem_singleton_self x⟩
  uniq y := Subtype.ext (Finset.mem_singleton.1 y.2)

/-- **A choice for a singleton index is just an index into the single family.** -/
def idxSingleEquiv {V : Cᵒᵖ} (x : F.Gen V) : Idx (single x) ≃ Fin x.arity :=
  Equiv.piUnique fun y : {z : F.Gen V // z ∈ (single x).carrier} => Fin y.1.arity

/-- The product family of a singleton index is the single family itself, read through
`Stacks.CechFamilySystem.FamilySystem.idxSingleEquiv`. -/
theorem famFun_single {V : Cᵒᵖ} (x : F.Gen V) (c : Idx (single x)) :
    famFun (single x) c = x.elts (idxSingleEquiv x c) := by
  rw [famFun, Fintype.prod_unique]
  rfl

/-- **The index of the chosen factor out of a family belonging to `S`.** -/
def famIdx {V : Cᵒᵖ} {S : F.GenSet V} {x : F.Gen V} (hx : x ∈ S.carrier)
    (k : Fin (famCard S)) : Fin x.arity :=
  (idxEquiv S).symm k ⟨x, hx⟩

/-- **Each value of the product family of `S` is divisible by the chosen factor out of any family
belonging to `S`.** -/
theorem elts_famIdx_dvd_fam {V : Cᵒᵖ} {S : F.GenSet V} {x : F.Gen V} (hx : x ∈ S.carrier)
    (k : Fin (famCard S)) : x.elts (famIdx hx k) ∣ fam S k := by
  rw [fam_apply, famFun]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨x, hx⟩ : {y // y ∈ S.carrier}))

/-- **Some power of each value of the product family of `S` is divisible by the chosen factor out
of any family belonging to `S`.** -/
theorem exists_elts_famIdx_dvd_fam {V : Cᵒᵖ} {S : F.GenSet V} {x : F.Gen V} (hx : x ∈ S.carrier)
    (k : Fin (famCard S)) : ∃ n : ℕ, x.elts (famIdx hx k) ∣ fam S k ^ n :=
  ⟨1, by rw [pow_one]; exact elts_famIdx_dvd_fam hx k⟩

end FamilySystem

end Stacks.CechFamilySystem

end
