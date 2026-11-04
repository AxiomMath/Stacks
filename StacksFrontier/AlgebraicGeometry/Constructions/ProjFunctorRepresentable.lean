module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjFunctorColimit
public import StacksFrontier.AlgebraicGeometry.QuasiCompactExtension

/-!
# Stacks Tag 01NC: `Proj(A)` represents the functor `F` of Section 01N4

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring and `X = Proj(A)`. For a **quasi-compact** scheme `Y`,
Section 27.12 forms `F(Y) = ⋃_{d ≥ 1} F_d(Y)`, the colimit of the sets of strict equivalence
classes of triples along the weight transitions; that colimit is `Fcolim`, and the bijection
`F(Y) ≃ Mor(Y, X)` for quasi-compact `Y` is `Fcolim.classifyingEquiv`. For a **general** scheme `T`
the source extends `F` by the limit over the quasi-compact opens of `T`.

This file forms that extension: a functor `F : Sch^{opp} ⟶ Sets` defined on every scheme, a
bijection `F(T) ≃ Mor(T, X)` for every scheme `T`, and a `CategoryTheory.Functor.RepresentableBy`
datum exhibiting `X` as a representing object for it. That is the statement of [Stacks, Tag 01NC].

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.F`: **the set `F(T)` for an arbitrary scheme
  `T`** — a family of elements of `Fcolim(W)`, one for each morphism `g : W ⟶ T` out of a
  quasi-compact scheme, compatible with composition.
* `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.F.functor`: **the functor
  `F : Sch^{opp} ⟶ Sets`**, with both functor laws.
* `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.F.fcolimEquiv`: **`F(T) ≃ Fcolim(T)` for a
  quasi-compact `T`** — the extension really does extend the colimit of Section 27.12.
* `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.F.classifyingEquiv`: **the bijection
  `F(T) ≃ Mor(T, Proj(A))`**, for every scheme `T`.
* `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.F.representableBy`: **`Proj(A)` represents
  `F`.**

## Main results

* `...F.classifyingMorphism_val`: the morphism `W ⟶ Proj(A)` recorded by `s : F(T)` at
  `g : W ⟶ T` is `g` followed by the morphism `T ⟶ Proj(A)` that `s` glues to; it is the content
  of the round trip `F.ofHom_toHom`.
* `...F.ofHom_comp`: the bijection is natural in `T`, which is the `homEquiv_comp` field of the
  representing datum.

## Implementation notes

**The shape of the limit.** The source writes the extension as
`F(T) = lim_{V ⊆ T quasi-compact open} F(V)`. Taken literally that formula does not visibly carry a
functoriality in `T`: for `f : T' ⟶ T` and a quasi-compact open `V' ⊆ T'`, the image `f(V')` is
quasi-compact but is not open, so there is no map from the family indexed by the quasi-compact
opens of `T` to the one indexed by those of `T'` without first producing a quasi-compact open of
`T` containing `f(V')`. The limit is therefore taken here over **all** morphisms `g : W ⟶ T` out of
a quasi-compact scheme — the same limit, since the inclusions of the quasi-compact opens are an
initial subfamily — for which functoriality is the reindexing `g ↦ g ≫ f` and needs nothing. The
quasi-compact opens reappear exactly where the source uses them, in the proof: the glueing
`F.existsUnique_hom` is `AlgebraicGeometry.Scheme.existsUnique_hom_of_compatible_compactOpens`
applied to the subfamily of inclusions.

That this is an *extension* and not some other functor agreeing with nothing is
`F.fcolimEquiv`: for a quasi-compact `T` the identity `𝟙 T` is a terminal object of the index, so
`F(T) ≃ Fcolim(T)`.

**The comparison at a general quasi-compact test object.** `F.ofHom` and `F.toHom` are the two
directions of the bijection, and `F.toHom_ofHom` is immediate from the uniqueness in
`existsUnique_hom_of_compatible_compactOpens`. The other round trip is
`F.classifyingMorphism_val`: a family `s : F(T)` records at a general `g : W ⟶ T` out of a
quasi-compact `W` the same morphism as `g` composed with the glueing of its values at the
quasi-compact *opens* of `T`. Since `W` is quasi-compact, `g` itself factors as `h ≫ V.ι` through a
quasi-compact open `V` of `T` — the quasi-compact opens are a directed cover, which is
`AlgebraicGeometry.Scheme.exists_compactOpen_factorization` — so no basis argument is needed: the
compatibility of the family moves the value at `g` to the value at `V.ι`, where the glueing's
defining property applies.

**Universes.** `F(T)` is `Type (u + 1)` for `T : Scheme.{u}`, because a triple carries an
`𝒪`-module; the index of the limit is `Scheme.{u}`, which is `Type (u + 1)` as well, so the
compatible families stay in `Type (u + 1)`. **No `ULift` is needed anywhere**:
`CategoryTheory.Functor.RepresentableBy` is stated for `F : Cᵒᵖ ⥤ Type v` with `v` a universe
independent of the universe of the `Hom` sets of `C`, and its field `homEquiv` is an `Equiv`
between types that may live in two different universes.

**The universe restriction on the grading.** The bijection runs on the surjectivity of
`Fcolim.classifyingMorphism`, which runs on [Stacks, Tag 01N9]'s universal family, available here
only for a grading `𝒮 : ℕ → ς` whose index type `ς` lies in the *same* universe as the graded ring.
`F`, its functoriality and `F.fcolimEquiv` are stated for `σ : Type w` arbitrary; the bijection and
the representing datum inherit the restriction.

## References

* [Stacks Project, Tag 01NC](https://stacks.math.columbia.edu/tag/01NC)
* [Stacks Project, Tag 01NB](https://stacks.math.columbia.edu/tag/01NB)
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u w

namespace Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {T T' T'' W W' : Scheme.{u}}

/-! ### `F(T)` for an arbitrary scheme `T` -/

/-- **The set `F(T)` of Section 27.12 for an arbitrary scheme `T`**: the limit of the sets
`F(W) = Fcolim(W)` over the morphisms `g : W ⟶ T` out of a quasi-compact scheme `W`.

An element is a rule assigning to each such `g` an element of `Fcolim(W)`, compatibly with
precomposition. Restricted to the inclusions of the quasi-compact opens of `T` this is the limit
`lim_{V ⊆ T quasi-compact open} F(V)` the source writes; indexing by all quasi-compact test objects
instead makes the functoriality in `T` a reindexing. -/
structure F (T : Scheme.{u}) : Type (u + 1) where
  /-- The element of `F(W)` recorded at a morphism `g : W ⟶ T` out of a quasi-compact `W`. -/
  val : ∀ W : Scheme.{u}, CompactSpace W → (W ⟶ T) → Fcolim 𝒜 W
  /-- The recorded elements are compatible with precomposition. -/
  compat : ∀ (W W' : Scheme.{u}) (hW : CompactSpace W) (hW' : CompactSpace W') (h : W' ⟶ W)
    (g : W ⟶ T), Fcolim.pullback 𝒜 h (val W hW g) = val W' hW' (h ≫ g)

attribute [ext] F

/-! ### Functoriality -/

/-- **The map `F(T) → F(T')` attached to a morphism of schemes `f : T' ⟶ T`**: reindexing a
compatible family along `g ↦ g ≫ f`. -/
def F.pullback (f : T' ⟶ T) (s : F 𝒜 T) : F 𝒜 T' where
  val W hW g := s.val W hW (g ≫ f)
  compat W W' hW hW' h g := s.compat W W' hW hW' h (g ≫ f)

/-- The value of `F.pullback 𝒜 f s` at a morphism `g` is the value of `s` at `g ≫ f`. -/
@[simp] theorem F.pullback_val (f : T' ⟶ T) (s : F 𝒜 T) (hW : CompactSpace W) (g : W ⟶ T') :
    (F.pullback 𝒜 f s).val W hW g = s.val W hW (g ≫ f) := rfl

/-- **The identity law for `F`.** -/
theorem F.pullback_id (s : F 𝒜 T) : F.pullback 𝒜 (𝟙 T) s = s := by
  ext W hW g
  simp

/-- **The composition law for `F`.** -/
theorem F.pullback_comp (f : T' ⟶ T) (f' : T'' ⟶ T') (s : F 𝒜 T) :
    F.pullback 𝒜 (f' ≫ f) s = F.pullback 𝒜 f' (F.pullback 𝒜 f s) := by
  ext W hW g
  simp

/-- **The functor `F : Sch^{opp} ⟶ Sets` of Section 27.12**, on all of `Sch`: on a quasi-compact
scheme it is the union `⋃_{d ≥ 1} F_d` (`F.fcolimEquiv`), and on a general scheme the limit of its
values at the quasi-compact test objects. The two functor laws are `F.pullback_id` and
`F.pullback_comp`. -/
def F.functor : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj T := F 𝒜 T.unop
  map φ := TypeCat.ofHom (F.pullback 𝒜 φ.unop)
  map_id _ := TypeCat.homEquiv.injective (funext fun s => F.pullback_id 𝒜 s)
  map_comp φ χ :=
    TypeCat.homEquiv.injective (funext fun s => F.pullback_comp 𝒜 φ.unop χ.unop s)

/-- The functor `F.functor 𝒜` sends `T` to `F 𝒜 T.unop`. -/
@[simp] theorem F.functor_obj (T : Scheme.{u}ᵒᵖ) : (F.functor 𝒜).obj T = F 𝒜 T.unop := rfl

/-- The functor `F.functor 𝒜` acts on a morphism `φ` by `F.pullback 𝒜 φ.unop`. -/
@[simp] theorem F.functor_map {S T : Scheme.{u}ᵒᵖ} (φ : S ⟶ T) (s : F 𝒜 S.unop) :
    (F.functor 𝒜).map φ s = F.pullback 𝒜 φ.unop s := rfl

/-! ### `F` extends the colimit of the `F_d` -/

/-- **For a quasi-compact `T` the extension `F(T)` is the colimit `Fcolim(T)` of Section 27.12.**
The identity of `T` is a terminal object of the index of the limit, so a compatible family is its
value there. -/
def F.fcolimEquiv (T : Scheme.{u}) (hT : CompactSpace T) : F 𝒜 T ≃ Fcolim 𝒜 T where
  toFun s := s.val T hT (𝟙 T)
  invFun x := { val := fun W _ g => Fcolim.pullback 𝒜 g x
                compat := fun _ _ _ _ h g => (Fcolim.pullback_comp 𝒜 g h x).symm }
  left_inv s := by
    ext W hW g
    exact (s.compat T W hT hW g (𝟙 T)).trans (by rw [Category.comp_id])
  right_inv x := Fcolim.pullback_id 𝒜 x

section Universal

variable {S : Type u} {ς : Type u} [CommRing S] [SetLike ς S] [AddSubgroupClass ς S]
  (𝒮 : ℕ → ς) [GradedRing 𝒮]

/-! ### The inverse of the comparison at a quasi-compact scheme -/

/-- **The class of triples on a quasi-compact `W` classifying a given morphism `W ⟶ Proj(A)`**:
the inverse of `Fcolim.classifyingEquiv`, with the quasi-compactness as an ordinary hypothesis
rather than an instance. -/
def Fcolim.classifyingInv (hW : CompactSpace W) (φ : W ⟶ AlgebraicGeometry.Proj 𝒮) :
    Fcolim 𝒮 W :=
  haveI := hW; (Fcolim.classifyingEquiv 𝒮 W).symm φ

/-- The class `Fcolim.classifyingInv 𝒮 hW φ` classifies the morphism `φ`. -/
@[simp] theorem Fcolim.classifyingMorphism_classifyingInv (hW : CompactSpace W)
    (φ : W ⟶ AlgebraicGeometry.Proj 𝒮) :
    Fcolim.classifyingMorphism 𝒮 (Fcolim.classifyingInv 𝒮 hW φ) = φ :=
  have := hW; (Fcolim.classifyingEquiv 𝒮 W).apply_symm_apply φ

/-- A class of triples on a quasi-compact `W` classifying `φ` is
`Fcolim.classifyingInv 𝒮 hW φ`. -/
theorem Fcolim.classifyingInv_eq (hW : CompactSpace W) (φ : W ⟶ AlgebraicGeometry.Proj 𝒮)
    (x : Fcolim 𝒮 W) (hx : Fcolim.classifyingMorphism 𝒮 x = φ) :
    x = Fcolim.classifyingInv 𝒮 hW φ :=
  Fcolim.classifyingMorphism_injective 𝒮
    (hx.trans (Fcolim.classifyingMorphism_classifyingInv 𝒮 hW φ).symm)

/-! ### From a morphism to a compatible family -/

/-- **The element of `F(T)` attached to a morphism `φ : T ⟶ Proj(A)`**: at `g : W ⟶ T` it records
the class of triples on the quasi-compact `W` classifying `g ≫ φ`. -/
def F.ofHom (φ : T ⟶ AlgebraicGeometry.Proj 𝒮) : F 𝒮 T where
  val W hW g := Fcolim.classifyingInv 𝒮 hW (g ≫ φ)
  compat W W' hW hW' h g := by
    refine Fcolim.classifyingMorphism_injective 𝒮 ?_
    rw [Fcolim.classifyingMorphism_pullback, Fcolim.classifyingMorphism_classifyingInv,
      Fcolim.classifyingMorphism_classifyingInv, Category.assoc]

/-- The value of `F.ofHom 𝒮 φ` at `g` is the class classifying `g ≫ φ`. -/
@[simp] theorem F.ofHom_val (φ : T ⟶ AlgebraicGeometry.Proj 𝒮) (hW : CompactSpace W)
    (g : W ⟶ T) :
    (F.ofHom 𝒮 φ).val W hW g = Fcolim.classifyingInv 𝒮 hW (g ≫ φ) := rfl

/-- **The comparison is natural in `T`**, in the direction from morphisms to families: reindexing
the family of `φ` along `f` is the family of `f ≫ φ`. -/
theorem F.ofHom_comp (f : T' ⟶ T) (φ : T ⟶ AlgebraicGeometry.Proj 𝒮) :
    F.ofHom 𝒮 (f ≫ φ) = F.pullback 𝒮 f (F.ofHom 𝒮 φ) := by
  ext W hW g
  simp

/-! ### From a compatible family to a morphism -/

/-- **The morphisms recorded by a compatible family are compatible**: the morphism recorded at
`h ≫ g` is `h` followed by the one recorded at `g`. -/
theorem F.classifyingMorphism_val_comp (s : F 𝒮 T) (hW : CompactSpace W) (hW' : CompactSpace W')
    (h : W' ⟶ W) (g : W ⟶ T) :
    h ≫ Fcolim.classifyingMorphism 𝒮 (s.val W hW g)
      = Fcolim.classifyingMorphism 𝒮 (s.val W' hW' (h ≫ g)) := by
  rw [← s.compat W W' hW hW' h g, Fcolim.classifyingMorphism_pullback]

/-- **A compatible family glues to a unique morphism `T ⟶ Proj(A)`.** The morphisms recorded at the
inclusions of the quasi-compact opens of `T` are compatible with those inclusions, so
`AlgebraicGeometry.Scheme.existsUnique_hom_of_compatible_compactOpens` glues them. -/
theorem F.existsUnique_hom (s : F 𝒮 T) :
    ∃! φ : T ⟶ AlgebraicGeometry.Proj 𝒮, ∀ (V : T.Opens) (hV : IsCompact (V : Set T)),
      V.ι ≫ φ = Fcolim.classifyingMorphism 𝒮
        (s.val V.toScheme (isCompact_iff_compactSpace.mp hV) V.ι) := by
  refine AlgebraicGeometry.Scheme.existsUnique_hom_of_compatible_compactOpens T _ ?_
  intro V V' hV hV' hVV'
  rw [F.classifyingMorphism_val_comp 𝒮 s (isCompact_iff_compactSpace.mp hV')
    (isCompact_iff_compactSpace.mp hV) (T.homOfLE hVV') V'.ι, Scheme.homOfLE_ι]

/-- **The morphism `T ⟶ Proj(A)` that a compatible family glues to.** -/
def F.toHom (s : F 𝒮 T) : T ⟶ AlgebraicGeometry.Proj 𝒮 := (F.existsUnique_hom 𝒮 s).choose

/-- The restriction of `F.toHom 𝒮 s` to a quasi-compact open `V` of `T` is the morphism
classified by the value of `s` at the inclusion `V.ι`. -/
theorem F.ι_comp_toHom (s : F 𝒮 T) (V : T.Opens) (hV : IsCompact (V : Set T)) :
    V.ι ≫ F.toHom 𝒮 s = Fcolim.classifyingMorphism 𝒮
      (s.val V.toScheme (isCompact_iff_compactSpace.mp hV) V.ι) :=
  (F.existsUnique_hom 𝒮 s).choose_spec.1 V hV

/-- A morphism `φ : T ⟶ Proj(A)` whose restriction to every quasi-compact open `V` is the morphism
classified by the value of `s` at `V.ι` is `F.toHom 𝒮 s`. -/
theorem F.eq_toHom (s : F 𝒮 T) (φ : T ⟶ AlgebraicGeometry.Proj 𝒮)
    (hφ : ∀ (V : T.Opens) (hV : IsCompact (V : Set T)), V.ι ≫ φ
      = Fcolim.classifyingMorphism 𝒮 (s.val V.toScheme (isCompact_iff_compactSpace.mp hV) V.ι)) :
    φ = F.toHom 𝒮 s :=
  (F.existsUnique_hom 𝒮 s).unique hφ (F.ι_comp_toHom 𝒮 s)

/-! ### The family is determined by its values at the quasi-compact opens -/

/-- **The morphism recorded by a compatible family at an arbitrary quasi-compact test object is
the expected one**: for every `g : W ⟶ T` with `W` quasi-compact, the family `s` records at `g`
the class classifying `g` followed by the morphism `s` glues to. -/
theorem F.classifyingMorphism_val (s : F 𝒮 T) (hW : CompactSpace W) (g : W ⟶ T) :
    Fcolim.classifyingMorphism 𝒮 (s.val W hW g) = g ≫ F.toHom 𝒮 s := by
  have := hW
  obtain ⟨V, hV, h, rfl⟩ :=
    AlgebraicGeometry.Scheme.exists_compactOpen_factorization (T := T) (W := W) g
  rw [← F.classifyingMorphism_val_comp 𝒮 s (isCompact_iff_compactSpace.mp hV) hW h V.ι,
    ← F.ι_comp_toHom 𝒮 s V hV, Category.assoc]

/-! ### The bijection and the representing datum -/

/-- The morphism glued from the family `F.ofHom 𝒮 φ` is `φ`. -/
theorem F.toHom_ofHom (φ : T ⟶ AlgebraicGeometry.Proj 𝒮) :
    F.toHom 𝒮 (F.ofHom 𝒮 φ) = φ :=
  (F.eq_toHom 𝒮 (F.ofHom 𝒮 φ) φ fun V hV =>
    (Fcolim.classifyingMorphism_classifyingInv 𝒮 (isCompact_iff_compactSpace.mp hV)
      (V.ι ≫ φ)).symm).symm

/-- The family attached to the morphism `F.toHom 𝒮 s` is `s`. -/
theorem F.ofHom_toHom (s : F 𝒮 T) : F.ofHom 𝒮 (F.toHom 𝒮 s) = s := by
  ext W hW g
  exact (Fcolim.classifyingInv_eq 𝒮 hW _ _ (F.classifyingMorphism_val 𝒮 s hW g)).symm

/-- **Stacks Tag 01NC: the bijection `F(T) ≃ Mor(T, Proj(A))`**, for an arbitrary scheme `T`. Let
`A` be a graded ring and `X = Proj(A)`. The map sending a class of triples to the morphism it
classifies by [Stacks, Tag 01N8] is a bijection from the set `F(T)` of Section 27.12 — the union
`⋃_{d ≥ 1} F_d(T)` for quasi-compact `T`, and the limit of those unions over the quasi-compact
opens in general — onto `Mor(T, X)`.

Both directions are explicit: `F.ofHom` sends a morphism to the family of the classes classifying
its restrictions, and `F.toHom` glues the morphisms a family records. -/
def F.classifyingEquiv (T : Scheme.{u}) : F 𝒮 T ≃ (T ⟶ AlgebraicGeometry.Proj 𝒮) where
  toFun := F.toHom 𝒮
  invFun := F.ofHom 𝒮
  left_inv := F.ofHom_toHom 𝒮
  right_inv := F.toHom_ofHom 𝒮

/-- **`Proj(A)` represents the functor `F` of Section 01N4.** Let `A` be a graded ring and
`X = Proj(A)`. The functor `F : Sch^{opp} ⟶ Sets` which sends a quasi-compact scheme `T` to
`⋃_{d ≥ 1} F_d(T)`, the colimit of the sets of strict equivalence classes of triples of positive
weight along the weight transitions, and a general scheme to the limit of those over its
quasi-compact opens, is represented by `X`: there is a bijection `Mor(T, X) ≃ F(T)` natural in `T`.

The bijection is `F.classifyingEquiv`, whose two halves are the injectivity of [Stacks, Tag 01NB]
and the surjectivity coming from [Stacks, Tag 01N9]'s universal family; its naturality is
`F.ofHom_comp`. -/
@[stacks 01NC "the FULL statement of this tag: Proj(A) represents the functor F of Section 01N4. \
F.functor is F as a functor Sch^opp ⟶ Type (u+1) on ALL schemes (the colimit Fcolim of the F_d \
along divisibility on a quasi-compact T, by F.fcolimEquiv, and the limit over the quasi-compact \
test objects in general, which is the limit over the quasi-compact opens the source writes — see \
the module docstring for why the index is the morphisms out of quasi-compact schemes), \
F.classifyingEquiv is the bijection F(T) ≃ Mor(T, Proj(A)) for every scheme T, and this is the \
RepresentableBy datum. The two halves of the bijection remain available separately as \
Fd.veronese_eq_weightCongr_veronese_of_classifyingMorphism_eq (injectivity) and \
Fd.exists_pos_classifyingMorphism_eq (surjectivity for a quasi-compact Y). The grading is taken \
with its index type in the same universe as the graded ring, which is the generality of Tag \
01N9's universal family here; the functor F itself and F.fcolimEquiv are unrestricted."]
def F.representableBy : (F.functor 𝒮).RepresentableBy (AlgebraicGeometry.Proj 𝒮) where
  homEquiv {T} := (F.classifyingEquiv 𝒮 T).symm
  homEquiv_comp f g :=
    (F.ofHom_comp 𝒮 f g).trans (F.functor_map 𝒮 f.op (F.ofHom 𝒮 g)).symm

/-- The bijection of `F.representableBy 𝒮` sends a morphism `φ` to `F.ofHom 𝒮 φ`. -/
@[simp] theorem F.representableBy_homEquiv (φ : T ⟶ AlgebraicGeometry.Proj 𝒮) :
    (F.representableBy 𝒮).homEquiv φ = F.ofHom 𝒮 φ := rfl

/-- `F` is representable, as a predicate. -/
theorem F.isRepresentable : (F.functor 𝒮).IsRepresentable :=
  (F.representableBy 𝒮).isRepresentable

end Universal

end Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor

end
