module

public import StacksFrontier.AlgebraicGeometry.OrderedOpenCover

/-!
# Extending a functor from the quasi-compact schemes to all schemes

The Stacks Project repeatedly defines a functor `F : Sch^{opp} ⟶ Sets` by giving it on
quasi-compact test schemes and extending it to a general test scheme `T` by

`F(T) = lim_{V ⊆ T quasi-compact open} F(V)`,

and then represents the extension by a scheme. Tag 01NC does this for the functor of triples of
Section 01N4 and Tag 01NY for the functor of quadruples of the display 01NX. This file carries out
that extension, and the representability of the extension, **for an arbitrary functor**
`Φ : Sch^{opp} ⟶ Sets`.

## Main definitions

* `AlgebraicGeometry.Scheme.QcExtension`: **the extension `Φ^{qc}(T)`** — a family of elements of
  `Φ(W)`, one for each morphism `g : W ⟶ T` out of a quasi-compact scheme, compatible with
  precomposition.
* `AlgebraicGeometry.Scheme.QcOpenExtension`: **the source's own form of the extension** — a
  family indexed by the quasi-compact *opens* of `T`, compatible with the inclusions between them.
* `AlgebraicGeometry.Scheme.QcExtension.functor`: the extension as a functor
  `Sch^{opp} ⟶ Sets`, with both functor laws.
* `AlgebraicGeometry.Scheme.QcClassifying`: the datum of a bijection
  `Φ(W) ≃ Mor(W, X)` for every quasi-compact `W`, natural in `W`. This is what a representability
  statement on quasi-compact test schemes supplies.

## Main results

* `AlgebraicGeometry.Scheme.exists_compactOpen_factorization`: **a morphism out of a
  quasi-compact scheme factors through a quasi-compact open of its target.** The image is
  quasi-compact, hence covered by finitely many affine opens, and their union is a quasi-compact
  open containing it.
* `AlgebraicGeometry.Scheme.QcExtension.equivQcOpen`: **the two forms of the extension agree** —
  restricting a family indexed by all quasi-compact test objects to the inclusions of the
  quasi-compact opens is a bijection. So the construction here *is* the source's inverse limit;
  the index is enlarged only to make the functoriality in `T` a reindexing.
* `AlgebraicGeometry.Scheme.QcExtension.equivObj`: for a quasi-compact `T` the extension is `Φ(T)`
  itself, the identity of `T` being a terminal object of the index.
* `AlgebraicGeometry.Scheme.QcClassifying.representableBy`: **if `X` represents `Φ` on
  quasi-compact test schemes, then `X` represents the extension of `Φ` on all test schemes.**

## Implementation notes

**Why the index is enlarged.** Taken literally, `lim_{V ⊆ T quasi-compact open} Φ(V)` does not
visibly carry a functoriality in `T`: for `f : T' ⟶ T` and a quasi-compact open `V' ⊆ T'` the
image `f(V')` is quasi-compact but not open, so there is no map between the two families without
first producing a quasi-compact open of `T` containing `f(V')`. Indexing instead by *all*
morphisms `g : W ⟶ T` out of a quasi-compact scheme makes the functoriality the reindexing
`g ↦ g ≫ f`, which needs nothing. That no information is gained or lost is `equivQcOpen`, whose
two halves are exactly `exists_compactOpen_factorization` (every index of the large family is
dominated by one of the small family) and the fact that an open immersion is a monomorphism (the
domination is unique, so there is nothing to choose).

**Where the quasi-compact opens are still used.** In the proof of the representability: the
morphism a family glues to is produced by
`AlgebraicGeometry.Scheme.existsUnique_hom_of_compatible_compactOpens`, i.e. from the subfamily
indexed by the quasi-compact opens, which is the form the gluing statement takes.

**Universes.** `Φ` takes values in `Type v` for a `v` unrelated to the universe of `Scheme.{u}`,
and `QcExtension Φ T` lands in `Type (max (u + 1) v)` — the index of the limit is `Scheme.{u}`,
which is `Type (u + 1)`. No `ULift` of anything is needed for the representability:
`CategoryTheory.Functor.RepresentableBy` is stated for `F : Cᵒᵖ ⥤ Type v` with `v` independent of
the universe of the `Hom` sets of `C`, and its field `homEquiv` is an `Equiv` between types that
may live in two different universes.

## References

* [Stacks Project, Tag 01NC](https://stacks.math.columbia.edu/tag/01NC)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u v

namespace AlgebraicGeometry.Scheme

variable {T T' T'' W W' : Scheme.{u}}

/-! ### Factoring a morphism out of a quasi-compact scheme -/

/-- **A morphism out of a quasi-compact scheme factors through a member of a directed open cover
of its target.** The set-theoretic image is quasi-compact, so finitely many members cover it, and
by directedness one member contains all of those; the morphism factors through it by the universal
property of an open immersion.

The factorization is unique for a given member, the inclusion of an open subscheme being a
monomorphism; see `AlgebraicGeometry.IsOpenImmersion.lift_uniq`. -/
theorem exists_factorization_of_directed {ι : Type*} [Nonempty ι] {U : ι → T.Opens}
    (hU : IsOpenCover U) (hdir : Directed (· ≤ ·) U) [CompactSpace W] (g : W ⟶ T) :
    ∃ (i : ι) (h : W ⟶ (U i).toScheme), h ≫ (U i).ι = g := by
  classical
  have hcov : Set.range g ⊆ ⋃ i, ((U i : T.Opens) : Set T) := by
    rw [hU.iSup_set_eq_univ]
    exact Set.subset_univ _
  obtain ⟨t, ht⟩ := (isCompact_range (Scheme.Hom.continuous g)).elim_finite_subcover
    (fun i => ((U i : T.Opens) : Set T)) (fun i => (U i).2) hcov
  obtain ⟨i, hi⟩ := hdir.finset_le t
  have hsub : Set.range g ⊆ Set.range (U i).ι := by
    rw [Scheme.Opens.range_ι]
    exact ht.trans (Set.iUnion₂_subset fun j hj => hi j hj)
  exact ⟨i, IsOpenImmersion.lift _ g hsub, IsOpenImmersion.lift_fac _ _ _⟩

/-- The empty open is quasi-compact, so a scheme has at least one quasi-compact open. -/
instance nonempty_compactOpens : Nonempty T.CompactOpens :=
  ⟨⟨⊥, by rw [Opens.coe_bot]; exact isCompact_empty⟩⟩

/-- **A morphism out of a quasi-compact scheme factors through a quasi-compact open of its
target.** The quasi-compact opens are a directed cover of a scheme: they cover it because the
affine opens do, and the union of two of them is again one.

The factorization is unique for a given open, `V.ι` being a monomorphism; see
`AlgebraicGeometry.IsOpenImmersion.lift_uniq`. -/
theorem exists_compactOpen_factorization [CompactSpace W] (g : W ⟶ T) :
    ∃ (V : T.Opens) (_ : IsCompact (V : Set T)) (h : W ⟶ V.toScheme), h ≫ V.ι = g := by
  obtain ⟨V, h, hfac⟩ := exists_factorization_of_directed
    (U := fun V : T.CompactOpens => (V : T.Opens)) (isOpenCover_compactOpens T)
    (fun V V' => ⟨⟨V ⊔ V', by rw [Opens.coe_sup]; exact V.2.union V'.2⟩,
      le_sup_left, le_sup_right⟩) g
  exact ⟨V.1, V.2, h, hfac⟩

/-- A factorization of a morphism of schemes through a quasi-compact open of its target. -/
structure CompactOpenFactorization (g : W ⟶ T) where
  /-- The quasi-compact open of the target. -/
  opens : T.Opens
  /-- It is quasi-compact. -/
  isCompact_opens : IsCompact (opens : Set T)
  /-- The morphism into it. -/
  hom : W ⟶ opens.toScheme
  /-- Followed by the inclusion it is the given morphism. -/
  fac : hom ≫ opens.ι = g

/-- **A morphism out of a quasi-compact scheme has a factorization through a quasi-compact open**,
`exists_compactOpen_factorization` read as the nonemptiness of the type of factorizations. -/
theorem nonempty_compactOpenFactorization [CompactSpace W] (g : W ⟶ T) :
    Nonempty (CompactOpenFactorization g) := by
  obtain ⟨V, hV, h, hfac⟩ := exists_compactOpen_factorization g
  exact ⟨⟨V, hV, h, hfac⟩⟩

/-- A chosen factorization of a morphism out of a quasi-compact scheme through a quasi-compact
open of its target. Which one is chosen never matters: `QcOpenExtension.map_val_eq` shows that any
two give the same answer, because the inclusion of the common upper bound of the two opens is a
monomorphism. -/
def compactOpenFactorization (hW : CompactSpace W) (g : W ⟶ T) : CompactOpenFactorization g :=
  haveI := hW; (nonempty_compactOpenFactorization g).some

/-! ### The two forms of the extension -/

variable (Φ : Scheme.{u}ᵒᵖ ⥤ Type v)

/-- **The extension of a functor `Φ : Sch^{opp} ⟶ Sets` to an arbitrary test scheme `T`**: the
limit of the sets `Φ(W)` over the morphisms `g : W ⟶ T` out of a quasi-compact scheme `W`.

An element is a rule assigning to each such `g` an element of `Φ(W)`, compatibly with
precomposition. Restricted to the inclusions of the quasi-compact opens of `T` this is the limit
`lim_{V ⊆ T quasi-compact open} Φ(V)` the Stacks Project writes, by `QcExtension.equivQcOpen`;
indexing by all quasi-compact test objects instead makes the functoriality in `T` a reindexing. -/
structure QcExtension (T : Scheme.{u}) : Type (max (u + 1) v) where
  /-- The element of `Φ(W)` recorded at a morphism `g : W ⟶ T` out of a quasi-compact `W`. -/
  val : ∀ W : Scheme.{u}, CompactSpace W → (W ⟶ T) → Φ.obj (op W)
  /-- The recorded elements are compatible with precomposition. -/
  compat : ∀ (W W' : Scheme.{u}) (hW : CompactSpace W) (hW' : CompactSpace W') (h : W' ⟶ W)
    (g : W ⟶ T), Φ.map h.op (val W hW g) = val W' hW' (h ≫ g)

attribute [ext] QcExtension

/-- **The Stacks Project's own form of the extension**: the limit of the sets `Φ(V)` over the
quasi-compact *opens* `V` of `T`, a family compatible with the inclusions between them. -/
structure QcOpenExtension (T : Scheme.{u}) : Type (max u v) where
  /-- The element of `Φ(V)` recorded at a quasi-compact open `V ⊆ T`. -/
  val : ∀ V : T.Opens, IsCompact (V : Set T) → Φ.obj (op V.toScheme)
  /-- The recorded elements are compatible with the inclusions. -/
  compat : ∀ (V V' : T.Opens) (hV : IsCompact (V : Set T)) (hV' : IsCompact (V' : Set T))
    (h : V' ≤ V), Φ.map (T.homOfLE h).op (val V hV) = val V' hV'

attribute [ext] QcOpenExtension

/-! ### Functoriality of the extension -/

/-- **The map `Φ^{qc}(T) → Φ^{qc}(T')` attached to a morphism of schemes `f : T' ⟶ T`**:
reindexing a compatible family along `g ↦ g ≫ f`. -/
def QcExtension.pullback (f : T' ⟶ T) (s : QcExtension Φ T) : QcExtension Φ T' where
  val W hW g := s.val W hW (g ≫ f)
  compat W W' hW hW' h g := s.compat W W' hW hW' h (g ≫ f)

/-- The value of the reindexed family `QcExtension.pullback Φ f s` at `g` is the value of `s` at
`g ≫ f`. -/
@[simp] theorem QcExtension.pullback_val (f : T' ⟶ T) (s : QcExtension Φ T)
    (hW : CompactSpace W) (g : W ⟶ T') :
    (QcExtension.pullback Φ f s).val W hW g = s.val W hW (g ≫ f) := rfl

/-- **The identity law for the extension.** -/
theorem QcExtension.pullback_id (s : QcExtension Φ T) : QcExtension.pullback Φ (𝟙 T) s = s := by
  ext W hW g
  rw [QcExtension.pullback_val, Category.comp_id]

/-- **The composition law for the extension.** -/
theorem QcExtension.pullback_comp (f : T' ⟶ T) (f' : T'' ⟶ T') (s : QcExtension Φ T) :
    QcExtension.pullback Φ (f' ≫ f) s
      = QcExtension.pullback Φ f' (QcExtension.pullback Φ f s) := by
  ext W hW g
  rw [QcExtension.pullback_val, QcExtension.pullback_val, QcExtension.pullback_val,
    Category.assoc]

/-- **The extension as a functor `Sch^{opp} ⟶ Sets`.** The two functor laws are
`QcExtension.pullback_id` and `QcExtension.pullback_comp`. -/
def QcExtension.functor : Scheme.{u}ᵒᵖ ⥤ Type (max (u + 1) v) where
  obj T := QcExtension Φ T.unop
  map φ := TypeCat.ofHom (QcExtension.pullback Φ φ.unop)
  map_id _ := TypeCat.homEquiv.injective (funext fun s => QcExtension.pullback_id Φ s)
  map_comp φ χ :=
    TypeCat.homEquiv.injective (funext fun s => QcExtension.pullback_comp Φ φ.unop χ.unop s)

/-- The extension functor sends `T` to `QcExtension Φ T.unop`. -/
@[simp] theorem QcExtension.functor_obj (T : Scheme.{u}ᵒᵖ) :
    (QcExtension.functor Φ).obj T = QcExtension Φ T.unop := rfl

/-- The extension functor acts on a morphism `φ` by `QcExtension.pullback Φ φ.unop`. -/
@[simp] theorem QcExtension.functor_map {S T : Scheme.{u}ᵒᵖ} (φ : S ⟶ T)
    (s : QcExtension Φ S.unop) :
    (QcExtension.functor Φ).map φ s = QcExtension.pullback Φ φ.unop s := rfl

/-- **On a quasi-compact test scheme the extension is `Φ` itself.** The identity of `T` is a
terminal object of the index of the limit, so a compatible family is its value there. -/
def QcExtension.equivObj (T : Scheme.{u}) (hT : CompactSpace T) :
    QcExtension Φ T ≃ Φ.obj (op T) where
  toFun s := s.val T hT (𝟙 T)
  invFun x :=
    { val := fun W _ g => Φ.map g.op x
      compat := fun _ _ _ _ h g => by rw [op_comp, Functor.map_comp_apply] }
  left_inv s := by
    ext W hW g
    exact (s.compat T W hT hW g (𝟙 T)).trans (by rw [Category.comp_id])
  right_inv x := by
    change Φ.map (𝟙 T).op x = x
    rw [op_id, Functor.map_id_apply]

/-! ### The two forms of the extension agree -/

/-- **The element a family indexed by the quasi-compact opens assigns to a morphism
`g : W ⟶ T` does not depend on the factorization of `g` chosen.** Two factorizations are both
dominated by the one through the union of their two opens, and the two comparison morphisms into
that union agree because the inclusion of an open subscheme is a monomorphism. -/
theorem QcOpenExtension.map_val_eq (r : QcOpenExtension Φ T) {g : W ⟶ T}
    (c c' : CompactOpenFactorization g) :
    Φ.map c.hom.op (r.val c.opens c.isCompact_opens)
      = Φ.map c'.hom.op (r.val c'.opens c'.isCompact_opens) := by
  have hsup : IsCompact ((c.opens ⊔ c'.opens : T.Opens) : Set T) := by
    rw [Opens.coe_sup]
    exact c.isCompact_opens.union c'.isCompact_opens
  have key : ∀ (d : CompactOpenFactorization g) (hle : d.opens ≤ c.opens ⊔ c'.opens),
      Φ.map (d.hom ≫ T.homOfLE hle).op (r.val _ hsup)
        = Φ.map d.hom.op (r.val d.opens d.isCompact_opens) := by
    intro d hle
    rw [op_comp, Functor.map_comp_apply, r.compat _ _ hsup d.isCompact_opens hle]
  have hhom : c.hom ≫ T.homOfLE (le_sup_left : c.opens ≤ c.opens ⊔ c'.opens)
      = c'.hom ≫ T.homOfLE (le_sup_right : c'.opens ≤ c.opens ⊔ c'.opens) := by
    rw [← cancel_mono (f := (c.opens ⊔ c'.opens : T.Opens).ι), Category.assoc, Category.assoc,
      Scheme.homOfLE_ι, Scheme.homOfLE_ι, c.fac, c'.fac]
  rw [← key c le_sup_left, ← key c' le_sup_right, hhom]

/-- **The element of `Φ(W)` that a family indexed by the quasi-compact opens assigns to a
morphism `g : W ⟶ T` out of a quasi-compact `W`**: transport the value at a quasi-compact open
through which `g` factors along the factorization. -/
def QcOpenExtension.value (r : QcOpenExtension Φ T) (hW : CompactSpace W) (g : W ⟶ T) :
    Φ.obj (op W) :=
  Φ.map (compactOpenFactorization hW g).hom.op
    (r.val _ (compactOpenFactorization hW g).isCompact_opens)

/-- The value of a family indexed by the quasi-compact opens at `g` may be computed from any
factorization `c` of `g` through a quasi-compact open. -/
theorem QcOpenExtension.value_eq (r : QcOpenExtension Φ T) (hW : CompactSpace W) (g : W ⟶ T)
    (c : CompactOpenFactorization g) :
    QcOpenExtension.value Φ r hW g = Φ.map c.hom.op (r.val c.opens c.isCompact_opens) :=
  QcOpenExtension.map_val_eq Φ r _ c

/-- Restricting a family indexed by all quasi-compact test objects to the inclusions of the
quasi-compact opens. -/
def QcExtension.toQcOpen (s : QcExtension Φ T) : QcOpenExtension Φ T where
  val V hV := s.val V.toScheme (isCompact_iff_compactSpace.mp hV) V.ι
  compat V V' hV hV' h := by
    rw [s.compat V.toScheme V'.toScheme (isCompact_iff_compactSpace.mp hV)
      (isCompact_iff_compactSpace.mp hV') (T.homOfLE h) V.ι, Scheme.homOfLE_ι]

/-- Extending a family indexed by the quasi-compact opens to all quasi-compact test objects. -/
def QcOpenExtension.toQcExtension (r : QcOpenExtension Φ T) : QcExtension Φ T where
  val W hW g := QcOpenExtension.value Φ r hW g
  compat W W' hW hW' h g := by
    rw [QcOpenExtension.value_eq Φ r hW g (compactOpenFactorization hW g),
      QcOpenExtension.value_eq Φ r hW' (h ≫ g)
        ⟨(compactOpenFactorization hW g).opens, (compactOpenFactorization hW g).isCompact_opens,
          h ≫ (compactOpenFactorization hW g).hom,
          by rw [Category.assoc, (compactOpenFactorization hW g).fac]⟩,
      op_comp, Functor.map_comp_apply]

/-- **The two forms of the extension agree.** Restricting a compatible family indexed by all
morphisms out of quasi-compact schemes to the inclusions of the quasi-compact opens of `T` loses
nothing: every index of the large family factors through a quasi-compact open
(`exists_compactOpen_factorization`) and does so uniquely for a given open, the inclusion being a
monomorphism.

So the extension constructed here *is* the inverse limit
`lim_{V ⊆ T quasi-compact open} Φ(V)` of the Stacks Project; the index is enlarged only to make
the functoriality in `T` a reindexing. -/
def QcExtension.equivQcOpen (T : Scheme.{u}) : QcExtension Φ T ≃ QcOpenExtension Φ T where
  toFun := QcExtension.toQcOpen Φ
  invFun := QcOpenExtension.toQcExtension Φ
  left_inv s := by
    ext W hW g
    change QcOpenExtension.value Φ (QcExtension.toQcOpen Φ s) hW g = s.val W hW g
    rw [QcOpenExtension.value_eq Φ _ hW g (compactOpenFactorization hW g)]
    exact (s.compat (compactOpenFactorization hW g).opens.toScheme W
      (isCompact_iff_compactSpace.mp (compactOpenFactorization hW g).isCompact_opens) hW
      (compactOpenFactorization hW g).hom
      (compactOpenFactorization hW g).opens.ι).trans
        (by rw [(compactOpenFactorization hW g).fac])
  right_inv r := by
    ext V hV
    change QcOpenExtension.value Φ r (isCompact_iff_compactSpace.mp hV) V.ι = r.val V hV
    rw [QcOpenExtension.value_eq Φ r (isCompact_iff_compactSpace.mp hV) V.ι
      ⟨V, hV, 𝟙 V.toScheme, Category.id_comp _⟩, op_id, Functor.map_id_apply]

/-! ### Representability of the extension -/

/-- **The datum of a representation of `Φ` on the quasi-compact test schemes**: a map
`Φ(W) → Mor(W, X)` for every quasi-compact `W`, natural in `W` and bijective.

This is exactly what a representability statement for `Φ` restricted to quasi-compact test
schemes supplies, and `QcClassifying.representableBy` turns it into a representation of the
extension of `Φ` by `X` on *all* test schemes. -/
structure QcClassifying (X : Scheme.{u}) where
  /-- The morphism `W ⟶ X` classifying an element of `Φ(W)`, for `W` quasi-compact. -/
  hom : ∀ W : Scheme.{u}, CompactSpace W → Φ.obj (op W) → (W ⟶ X)
  /-- Naturality: the morphism classifying a restricted element is the restricted morphism. -/
  hom_map : ∀ (W W' : Scheme.{u}) (hW : CompactSpace W) (hW' : CompactSpace W') (h : W' ⟶ W)
    (x : Φ.obj (op W)), hom W' hW' (Φ.map h.op x) = h ≫ hom W hW x
  /-- Every morphism out of a quasi-compact scheme is classified by exactly one element. -/
  bijective : ∀ (W : Scheme.{u}) (hW : CompactSpace W), Function.Bijective (hom W hW)

section Representability

variable {Φ} {X : Scheme.{u}} (c : QcClassifying Φ X)

/-- The bijection `Φ(W) ≃ Mor(W, X)` of a classifying datum, at a quasi-compact `W`. -/
def QcClassifying.equiv (hW : CompactSpace W) : Φ.obj (op W) ≃ (W ⟶ X) :=
  Equiv.ofBijective _ (c.bijective W hW)

/-- The bijection `QcClassifying.equiv` is the classifying map `c.hom W hW`. -/
@[simp] theorem QcClassifying.equiv_apply (hW : CompactSpace W) (x : Φ.obj (op W)) :
    c.equiv hW x = c.hom W hW x := rfl

/-- The inverse bijection is natural too. -/
theorem QcClassifying.map_equiv_symm (hW : CompactSpace W) (hW' : CompactSpace W')
    (h : W' ⟶ W) (φ : W ⟶ X) :
    Φ.map h.op ((c.equiv hW).symm φ) = (c.equiv hW').symm (h ≫ φ) := by
  refine (c.equiv hW').injective ?_
  rw [Equiv.apply_symm_apply]
  show c.hom W' hW' (Φ.map h.op ((c.equiv hW).symm φ)) = _
  rw [c.hom_map]
  show h ≫ c.equiv hW ((c.equiv hW).symm φ) = _
  rw [Equiv.apply_symm_apply]

/-! #### From a compatible family to a morphism -/

/-- **The morphisms classified by a compatible family are compatible**: the morphism classified at
`h ≫ g` is `h` followed by the one classified at `g`. This is the naturality of the classifying
datum read through the compatibility of the family, and it is all the gluing below uses. -/
theorem QcClassifying.hom_val_comp (s : QcExtension Φ T) (hW : CompactSpace W)
    (hW' : CompactSpace W') (h : W' ⟶ W) (g : W ⟶ T) :
    h ≫ c.hom W hW (s.val W hW g) = c.hom W' hW' (s.val W' hW' (h ≫ g)) := by
  rw [← s.compat W W' hW hW' h g, c.hom_map]

/-- **A compatible family glues to a unique morphism `T ⟶ X`.** The morphisms classified at the
inclusions of the quasi-compact opens of `T` are compatible with those inclusions, so
`AlgebraicGeometry.Scheme.existsUnique_hom_of_compatible_compactOpens` glues them. -/
theorem QcClassifying.existsUnique_hom (s : QcExtension Φ T) :
    ∃! φ : T ⟶ X, ∀ (V : T.Opens) (hV : IsCompact (V : Set T)),
      V.ι ≫ φ = c.hom V.toScheme (isCompact_iff_compactSpace.mp hV)
        (s.val V.toScheme (isCompact_iff_compactSpace.mp hV) V.ι) := by
  refine existsUnique_hom_of_compatible_compactOpens T _ ?_
  intro V V' hV hV' hVV'
  rw [c.hom_val_comp s (isCompact_iff_compactSpace.mp hV')
    (isCompact_iff_compactSpace.mp hV) (T.homOfLE hVV') V'.ι, Scheme.homOfLE_ι]

/-- **The morphism `T ⟶ X` that a compatible family glues to.** -/
def QcClassifying.toHom (s : QcExtension Φ T) : T ⟶ X := (c.existsUnique_hom s).choose

/-- The glued morphism `c.toHom s`, restricted to a quasi-compact open `V` of `T`, is the morphism
classified by the value of `s` at the inclusion of `V`. -/
theorem QcClassifying.ι_comp_toHom (s : QcExtension Φ T) (V : T.Opens)
    (hV : IsCompact (V : Set T)) :
    V.ι ≫ c.toHom s = c.hom V.toScheme (isCompact_iff_compactSpace.mp hV)
      (s.val V.toScheme (isCompact_iff_compactSpace.mp hV) V.ι) :=
  (c.existsUnique_hom s).choose_spec.1 V hV

/-- A morphism `φ : T ⟶ X` whose restriction to every quasi-compact open `V` of `T` is the
morphism classified by the value of `s` at the inclusion of `V` is `c.toHom s`. -/
theorem QcClassifying.eq_toHom (s : QcExtension Φ T) (φ : T ⟶ X)
    (hφ : ∀ (V : T.Opens) (hV : IsCompact (V : Set T)), V.ι ≫ φ
      = c.hom V.toScheme (isCompact_iff_compactSpace.mp hV)
        (s.val V.toScheme (isCompact_iff_compactSpace.mp hV) V.ι)) :
    φ = c.toHom s :=
  (c.existsUnique_hom s).unique hφ (c.existsUnique_hom s).choose_spec.1

/-- **The morphism classified by a compatible family at an arbitrary quasi-compact test object is
the expected one**: for every `g : W ⟶ T` with `W` quasi-compact, the family `s` records at `g` an
element classifying `g` followed by the morphism `s` glues to.

The gluing only sees the quasi-compact *opens* of `T`, so this is the step that has to reach an
arbitrary quasi-compact test object. It costs nothing, because `g` itself factors through a
quasi-compact open of `T` (`exists_compactOpen_factorization`), after which the statement is the
compatibility of `s` and the naturality of the classifying datum. -/
theorem QcClassifying.hom_val (s : QcExtension Φ T) (hW : CompactSpace W) (g : W ⟶ T) :
    c.hom W hW (s.val W hW g) = g ≫ c.toHom s := by
  have := hW
  obtain ⟨V, hV, h, rfl⟩ := exists_compactOpen_factorization (T := T) (W := W) g
  rw [← c.hom_val_comp s (isCompact_iff_compactSpace.mp hV) hW h V.ι, ← c.ι_comp_toHom s V hV,
    Category.assoc]

/-! #### From a morphism to a compatible family -/

/-- **The element of the extension attached to a morphism `φ : T ⟶ X`**: at `g : W ⟶ T` it records
the element of `Φ(W)` classifying `g ≫ φ`. -/
def QcClassifying.ofHom (φ : T ⟶ X) : QcExtension Φ T where
  val W hW g := (c.equiv hW).symm (g ≫ φ)
  compat W W' hW hW' h g := by
    rw [c.map_equiv_symm hW hW' h (g ≫ φ), Category.assoc]

/-- The value of `c.ofHom φ` at `g` is the element classifying `g ≫ φ`. -/
@[simp] theorem QcClassifying.ofHom_val (φ : T ⟶ X) (hW : CompactSpace W) (g : W ⟶ T) :
    (c.ofHom φ).val W hW g = (c.equiv hW).symm (g ≫ φ) := rfl

/-- **The comparison is natural in `T`**, in the direction from morphisms to families. This is the
`homEquiv_comp` field of the representing datum. -/
theorem QcClassifying.ofHom_comp (f : T' ⟶ T) (φ : T ⟶ X) :
    c.ofHom (f ≫ φ) = QcExtension.pullback Φ f (c.ofHom φ) := by
  ext W hW g
  rw [QcClassifying.ofHom_val, QcExtension.pullback_val, QcClassifying.ofHom_val, Category.assoc]

/-! #### The bijection and the representing datum -/

/-- The family attached to a morphism `φ` glues back to `φ`. -/
theorem QcClassifying.toHom_ofHom (φ : T ⟶ X) : c.toHom (c.ofHom φ) = φ :=
  (c.eq_toHom (c.ofHom φ) φ fun V hV =>
    ((c.equiv (isCompact_iff_compactSpace.mp hV)).apply_symm_apply (V.ι ≫ φ)).symm).symm

/-- The family attached to the morphism a family `s` glues to is `s`. -/
theorem QcClassifying.ofHom_toHom (s : QcExtension Φ T) : c.ofHom (c.toHom s) = s := by
  ext W hW g
  rw [QcClassifying.ofHom_val, ← c.hom_val s hW g]
  exact (c.equiv hW).symm_apply_apply _

/-- **The bijection `Φ^{qc}(T) ≃ Mor(T, X)`** for an arbitrary scheme `T`, attached to a
representation of `Φ` on the quasi-compact test schemes. -/
def QcClassifying.classifyingEquiv (T : Scheme.{u}) : QcExtension Φ T ≃ (T ⟶ X) where
  toFun := c.toHom
  invFun := c.ofHom
  left_inv := c.ofHom_toHom
  right_inv := c.toHom_ofHom

/-- **If `X` represents `Φ` on the quasi-compact test schemes, then `X` represents the extension of
`Φ` to all test schemes.**

The bijection is `QcClassifying.classifyingEquiv`: a morphism `T ⟶ X` gives the family of the
elements classifying its restrictions, and a family glues to a morphism by
`AlgebraicGeometry.Scheme.existsUnique_hom_of_compatible_compactOpens`. Its naturality in `T` is
`QcClassifying.ofHom_comp`. -/
def QcClassifying.representableBy : (QcExtension.functor Φ).RepresentableBy X where
  homEquiv {T} := (c.classifyingEquiv T).symm
  homEquiv_comp f g :=
    (c.ofHom_comp f g).trans (QcExtension.functor_map Φ f.op (c.ofHom g)).symm

/-- The bijection of `QcClassifying.representableBy` sends a morphism `φ` to `c.ofHom φ`. -/
@[simp] theorem QcClassifying.representableBy_homEquiv (φ : T ⟶ X) :
    c.representableBy.homEquiv φ = c.ofHom φ := rfl

include c in
/-- The extension of `Φ` is representable as soon as `Φ` is represented on the quasi-compact test
schemes. -/
theorem QcClassifying.isRepresentable : (QcExtension.functor Φ).IsRepresentable :=
  (QcClassifying.representableBy c).isRepresentable

end Representability

end AlgebraicGeometry.Scheme

end
