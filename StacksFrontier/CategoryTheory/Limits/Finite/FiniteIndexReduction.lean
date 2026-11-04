module

public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Fintype.Sum
public import StacksCore.Tactic.StacksAttribute

/-!
# Reduction to a finite index category (Stacks 05XU)

Let `I` be a small category whose objects form a finite type and whose morphisms are all
finite composites of arrows drawn from one fixed finite list.  This is the hypothesis
`FinitelyGeneratedShape I`, and it is strictly weaker than `FinCategory I`, since the
hom-sets of `I` themselves may well be infinite.

The finite category produced from it is `JObj gens`: two disjoint copies `y_i = ⟨.inl i⟩`
and `z_i = ⟨.inr i⟩` of the objects of `I`, one arrow `g_k : y_{s k} ⟶ z_{t k}` for each
generator `f_k : s k ⟶ t k` in the list, one diagonal arrow `h_i : y_i ⟶ z_i` for each
object of `I`, and no non-identity arrows besides these.  Every non-identity arrow goes
from a `y`-copy to a `z`-copy, so in any composable pair one factor is an identity and
composition is forced; each hom-set is a proposition together with a subtype of
`Fin gens.length`, so `JObj gens` is a finite category.  The functor `jFunctor gens`
collapses the two copies, sending `h_i` to `𝟙 i` and `g_k` to `f_k`.

The mathematical heart of the tag is that this functor is both initial and final
(`FinitelyGeneratedShape.jFunctor_initial`, `FinitelyGeneratedShape.jFunctor_final`):
every comma category `CostructuredArrow F d`, resp. `StructuredArrow d F`, is connected.
That is exactly the cone, resp. cocone, bijection of the source, and it is proved by
inducting on the decomposition of an arbitrary arrow of `I` into generators, using the
diagonal arrows `h_i` to move between the two copies.

Part (b) of the source asks that the (co)limits of `M : I ⥤ C` and of `F ⋙ M` exist
together and are canonically isomorphic *via the comparison induced by `F`*.  That
comparison is `limit.pre M F : limit M ⟶ limit (F ⋙ M)`, uniquely characterised by its
compatibility with the projections, `limit.pre_π`, and dually `colimit.pre M F` by
`colimit.ι_pre`.  Since the comparison commutes with the legs by construction, asserting
`IsIso (limit.pre M F)` says precisely that the two limits agree compatibly with the
projections; together with the existence equivalences `HasLimit M ↔ HasLimit (F ⋙ M)` this
is the formal reading of the source's cone bijection.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v u v' u'

/-- The morphism `f : a ⟶ b` lies in the multiplicative closure of the finite list
of generating morphisms `gens` (a list of triples `⟨a, b, f⟩`): the smallest family
of morphisms containing all identities and all generators, and closed under
composition.  Identity morphisms correspond to the empty composition. -/
inductive GeneratedByList {I : Type u} [Category.{v} I]
    (gens : List (Σ a b : I, a ⟶ b)) :
    ∀ {a b : I}, (a ⟶ b) → Prop
  | id (a : I) : GeneratedByList gens (𝟙 a)
  | gen {a b : I} (f : a ⟶ b) (h : ⟨a, b, f⟩ ∈ gens) : GeneratedByList gens f
  | comp {a b c : I} {f : a ⟶ b} {g : b ⟶ c} :
      GeneratedByList gens f → GeneratedByList gens g →
      GeneratedByList gens (f ≫ g)

/-- The hypotheses Stacks 05XU puts on the shape category `I`: the type of objects is
finite, and there is a finite list of generating morphisms such that every morphism of
`I` is a finite composite of generators (identities being the empty composite).  This is
weaker than `FinCategory I`, which additionally requires the hom-sets to be finite. -/
structure FinitelyGeneratedShape (I : Type u) [Category.{v} I] : Prop where
  /-- The type of objects of `I` is finite. -/
  finite_objects : Finite I
  /-- Every morphism of `I` is generated, by composition, from a fixed finite list of
  generating morphisms. -/
  finitely_generated_arrows :
    ∃ gens : List (Σ a b : I, a ⟶ b),
      ∀ {a b : I} (f : a ⟶ b), GeneratedByList gens f

namespace FinitelyGeneratedShape

variable {I : Type u} [SmallCategory I] {gens : List (Σ a b : I, a ⟶ b)}

/-- Objects of `J`: two disjoint copies of `Ob I` (`down = inl i = y_i`,
`down = inr i = z_i`).  **Parameterized by `gens`** (a one-field structure wrapper):
this is essential so that type-class synthesis finds the bespoke `jCategory`
instance for `JObj gens`.  With `abbrev JObj := I ⊕ I` instead, Mathlib's
`CategoryTheory.sum` instance fires on `I ⊕ I` and silently shadows the intended
category structure, making `(X ⟶ Y) = JHom …` false.  With this wrapper the `sum`
instance no longer applies and `jCategory` is the unique category on `JObj`. -/
structure JObj (gens : List (Σ a b : I, a ⟶ b)) where
  /-- The underlying element of `I ⊕ I` (`inl` = `y`-copy, `inr` = `z`-copy). -/
  down : I ⊕ I

/-- Morphisms of `J`.  All non-identity arrows go `inl → inr`; an arrow `y_i → z_j`
is either the diagonal `h_i` (witnessed by `i = j`) or a generator `g_k` (a `k` with
source `i` and target `j`). -/
@[reducible] def JHom : JObj gens → JObj gens → Type u
  | ⟨Sum.inl i⟩, ⟨Sum.inl j⟩ => ULift.{u} (PLift (i = j))
  | ⟨Sum.inr i⟩, ⟨Sum.inr j⟩ => ULift.{u} (PLift (i = j))
  | ⟨Sum.inl i⟩, ⟨Sum.inr j⟩ =>
      ULift.{u} (PLift (i = j)) ⊕
        ULift.{u} { k : Fin gens.length // (gens.get k).1 = i ∧ (gens.get k).snd.fst = j }
  | ⟨Sum.inr _⟩, ⟨Sum.inl _⟩ => PEmpty.{u+1}

/-- Identity arrows of `J`. -/
def jId : ∀ (a : JObj gens), JHom a a
  | ⟨Sum.inl _⟩ => ⟨PLift.up rfl⟩
  | ⟨Sum.inr _⟩ => ⟨PLift.up rfl⟩

/-- Composition in `J`.  Since every non-identity arrow goes `inl → inr`, in any
composable pair at least one factor is an identity, so composition is forced. -/
def jComp : ∀ {a b c : JObj gens}, JHom a b → JHom b c → JHom a c
  | ⟨Sum.inl _⟩, ⟨Sum.inl _⟩, _, f, g => f.down.down ▸ g
  | ⟨Sum.inl _⟩, ⟨Sum.inr _⟩, ⟨Sum.inr _⟩, f, g => g.down.down ▸ f
  | ⟨Sum.inr _⟩, ⟨Sum.inr _⟩, _, f, g => f.down.down ▸ g

/-- The category structure on `JObj gens`. -/
instance jCategory : Category.{u} (JObj gens) where
  Hom a b := JHom a b
  id a := jId a
  comp f g := jComp f g
  id_comp := by
    rintro ⟨a|a⟩ ⟨b|b⟩ f
    · obtain ⟨⟨rfl⟩⟩ := f; rfl
    · rcases f with f | f <;> rfl
    · exact PEmpty.elim f
    · obtain ⟨⟨rfl⟩⟩ := f; rfl
  comp_id := by
    rintro ⟨a|a⟩ ⟨b|b⟩ f
    · obtain ⟨⟨rfl⟩⟩ := f; rfl
    · rcases f with f | f <;> rfl
    · exact PEmpty.elim f
    · obtain ⟨⟨rfl⟩⟩ := f; rfl
  assoc := by
    rintro ⟨a|a⟩ ⟨b|b⟩ ⟨c|c⟩ ⟨d|d⟩ f g h <;>
      first
      | exact PEmpty.elim f | exact PEmpty.elim g | exact PEmpty.elim h
      | (obtain ⟨⟨rfl⟩⟩ := f; rfl)
      | (rcases f with f | f <;> obtain ⟨⟨rfl⟩⟩ := g <;> rfl)

/-- Underlying object map of `F : J ⥤ I`: collapse the two copies. -/
@[implicit_reducible]
def jObjMap (a : JObj gens) : I := Sum.elim id id a.down

/-- Action of `F` on raw morphisms. -/
def jMap : ∀ {a b : JObj gens}, JHom a b → (jObjMap a ⟶ jObjMap b)
  | ⟨Sum.inl i⟩, ⟨Sum.inl _⟩, f => f.down.down ▸ 𝟙 i
  | ⟨Sum.inr i⟩, ⟨Sum.inr _⟩, f => f.down.down ▸ 𝟙 i
  | ⟨Sum.inl i⟩, ⟨Sum.inr _⟩, Sum.inl f => f.down.down ▸ 𝟙 i
  | ⟨Sum.inl i⟩, ⟨Sum.inr j⟩, Sum.inr k => by
      obtain ⟨⟨k, h1, h2⟩⟩ := k; exact h2 ▸ h1 ▸ (gens.get k).snd.snd

/-- The type `X ⟶ Y` in `J` is by definition `JHom X Y`: the `gens`-parameterized
`JObj` makes `jCategory` the category Lean uses for `⟶`. -/
lemma jHom_eq (X Y : JObj gens) : (X ⟶ Y) = JHom X Y := rfl

/-- `F` on morphisms, phrased over the bundled category hom `X ⟶ Y` (which is
definitionally `JHom X Y`, so no cast is required). -/
def jFmap {X Y : JObj gens} (f : X ⟶ Y) : (jObjMap X ⟶ jObjMap Y) := jMap f

/-- The identity of a `y`-copy. -/
lemma jId_inl (a : I) : jId (⟨Sum.inl a⟩ : JObj gens) = ⟨PLift.up rfl⟩ := rfl

/-- The identity of a `z`-copy. -/
lemma jId_inr (a : I) : jId (⟨Sum.inr a⟩ : JObj gens) = ⟨PLift.up rfl⟩ := rfl

/-- `jComp` is unital on the left. -/
lemma jComp_jId_left {a c : JObj gens} (g : JHom a c) : jComp (jId a) g = g := by
  rcases a with ⟨a | a⟩ <;> rfl

/-- `jComp` is unital on the right, for arrows from a `y`-copy to a `z`-copy. -/
lemma jComp_jId_right {a b : I} (f : JHom (⟨Sum.inl a⟩ : JObj gens) ⟨Sum.inr b⟩) :
    jComp f (jId _) = f := rfl

/-- `jMap` sends identities to identities. -/
lemma jMap_jId (a : JObj gens) : jMap (jId a) = 𝟙 (jObjMap a) := by
  rcases a with ⟨a | a⟩ <;> rfl

/-- `jMap` turns `jComp` into composition in `I`. Every non-identity arrow of `J` goes from a
`y`-copy to a `z`-copy, so in each composable pair one factor is an identity and both sides reduce
to the image of the other factor. This is the `map_comp` axiom of `jFunctor`, phrased for raw
`JHom`s. -/
lemma jMap_comp : ∀ {a b c : JObj gens} (f : JHom a b) (g : JHom b c),
    jMap (jComp f g) = jMap f ≫ jMap g := by
  rintro ⟨a|a⟩ ⟨b|b⟩ ⟨c|c⟩ f g
  · obtain ⟨⟨rfl⟩⟩ := f
    rw [← jId_inl, jComp_jId_left, jMap_jId, Category.id_comp]
  · obtain ⟨⟨rfl⟩⟩ := f
    rw [← jId_inl, jComp_jId_left, jMap_jId, Category.id_comp]
  · exact PEmpty.elim g
  · obtain ⟨⟨rfl⟩⟩ := g
    rw [← jId_inr, jComp_jId_right, jMap_jId, Category.comp_id]
  · exact PEmpty.elim f
  · exact PEmpty.elim f
  · exact PEmpty.elim g
  · obtain ⟨⟨rfl⟩⟩ := f
    rw [← jId_inr, jComp_jId_left, jMap_jId, Category.id_comp]

/-- `jMap_comp` restated for the bundled category hom `X ⟶ Y`, which is what `jFunctor` needs for
its `map_comp` field; no cast intervenes since `X ⟶ Y` is definitionally `JHom X Y`. -/
lemma jFmap_comp {X Y Z : JObj gens} (f : X ⟶ Y) (g : Y ⟶ Z) :
    jFmap (f ≫ g) = jFmap f ≫ jFmap g := jMap_comp f g

/-- The functor `F : J ⥤ I` collapsing the two copies of `Ob I`. -/
def jFunctor (gens : List (Σ a b : I, a ⟶ b)) : JObj gens ⥤ I where
  obj := jObjMap
  map {X Y} f := jFmap f
  map_id := by rintro ⟨a|a⟩ <;> rfl
  map_comp f g := jFmap_comp f g

/-- `jFunctor` acts on morphisms by `jMap`. -/
lemma jFunctor_map {X Y : JObj gens} (f : X ⟶ Y) : (jFunctor gens).map f = jMap f := rfl

/-- Each hom-set of `J` is finite: an `inl→inl` or `inr→inr` hom is a proposition
`i = j`, and an `inl→inr` hom is such a proposition plus a subtype of the finite index
set `Fin gens.length`. -/
@[reducible] noncomputable def jFintypeHom [Finite I] (a b : JObj gens) :
    Fintype (JHom a b) := by
  classical
  have : Fintype I := Fintype.ofFinite I
  match a, b with
  | ⟨Sum.inl i⟩, ⟨Sum.inl j⟩ => exact inferInstanceAs (Fintype (ULift (PLift (i = j))))
  | ⟨Sum.inr i⟩, ⟨Sum.inr j⟩ => exact inferInstanceAs (Fintype (ULift (PLift (i = j))))
  | ⟨Sum.inl i⟩, ⟨Sum.inr j⟩ =>
      exact inferInstanceAs (Fintype (ULift (PLift (i = j)) ⊕
        ULift { k : Fin gens.length // (gens.get k).1 = i ∧ (gens.get k).snd.fst = j }))
  | ⟨Sum.inr _⟩, ⟨Sum.inl _⟩ => exact inferInstanceAs (Fintype PEmpty)

/-- The objects of `J` form a finite type (two copies of the finite `Ob I`). -/
noncomputable instance jFintypeObj [Finite I] : Fintype (JObj gens) := by
  classical
  have : Fintype I := Fintype.ofFinite I
  exact Fintype.ofEquiv (I ⊕ I) ⟨JObj.mk, JObj.down, fun _ => rfl, fun _ => rfl⟩

/-- `J` is a finite category. -/
noncomputable instance jFinCategory [Finite I] : FinCategory (JObj gens) where
  fintypeObj := jFintypeObj
  fintypeHom a b := jFintypeHom a b

/-- The object map of `jFunctor` on a `y`-copy is the underlying object. -/
lemma jFunctor_obj_inl (i : I) :
    (jFunctor gens).obj ⟨Sum.inl i⟩ = i := rfl

/-- The object map of `jFunctor` on a `z`-copy is the underlying object. -/
lemma jFunctor_obj_inr (i : I) :
    (jFunctor gens).obj ⟨Sum.inr i⟩ = i := rfl

/-- The diagonal arrow `h_i : y_i ⟶ z_i`. -/
def jDiag (i : I) : (⟨Sum.inl i⟩ : JObj gens) ⟶ ⟨Sum.inr i⟩ := Sum.inl ⟨PLift.up rfl⟩

/-- `F` sends the diagonal arrow `h_i` to the identity. -/
lemma jFunctor_map_diag (i : I) :
    (jFunctor gens).map (jDiag (gens := gens) i) = 𝟙 i := rfl

/-- The generator arrow `g_k : y_{s k} ⟶ z_{t k}` for an index `k`. -/
def jGen (k : Fin gens.length) :
    (⟨Sum.inl (gens.get k).1⟩ : JObj gens) ⟶ ⟨Sum.inr (gens.get k).snd.fst⟩ :=
  Sum.inr ⟨⟨k, rfl, rfl⟩⟩

/-- `F` sends the generator arrow `g_k` to the underlying generating morphism. -/
lemma jFunctor_map_gen (k : Fin gens.length) :
    (jFunctor gens).map (jGen (gens := gens) k) = (gens.get k).snd.snd := by
  simp only [jFunctor_map, jMap, jGen]
  generalize_proofs h
  cases h
  rfl

/-- A generator in the list is the image under `jFunctor` of an arrow `y_a ⟶ z_b` of `J`. -/
private lemma exists_jHom_map_eq_of_mem {a b : I} {f : a ⟶ b} (hmem : ⟨a, b, f⟩ ∈ gens) :
    ∃ g : (⟨Sum.inl a⟩ : JObj gens) ⟶ ⟨Sum.inr b⟩, (jFunctor gens).map g = f := by
  obtain ⟨k, hk⟩ := List.get_of_mem hmem
  have e1 : (gens.get k).1 = a := by rw [hk]
  have e2 : (gens.get k).snd.fst = b := by rw [hk]
  have hgenval : HEq ((gens.get k).snd.snd) f := by rw [hk]
  subst e1 e2
  exact ⟨jGen k, (jFunctor_map_gen k).trans (eq_of_heq hgenval)⟩

/-- **`jFunctor gens` is an initial functor** — the cone half of the Stacks 05XU
bijection.

Initiality means that each comma category `CostructuredArrow F d` is connected.  Its
objects are pairs `(B, φ : F B ⟶ d)` with `B` a `y`-copy or a `z`-copy.  It is nonempty,
containing the basepoint `(z_d, 𝟙 d)`; the diagonal `h_i`, which `F` sends to an identity,
joins each `y`-object `(y_i, φ)` to the corresponding `z`-object `(z_i, φ)`; and inducting
on the decomposition of `φ : i ⟶ d` into generators joins each `z`-object to the basepoint,
because a generator `f_k : a ⟶ b` is the image of the arrow `g_k : y_a ⟶ z_b` of `J`. -/
lemma jFunctor_initial (hgen : ∀ {a b : I} (f : a ⟶ b), GeneratedByList gens f) :
    (jFunctor gens).Initial := by
  refine ⟨fun d => ?_⟩
  let yObj (i : I) (φ : i ⟶ d) : CostructuredArrow (jFunctor gens) d :=
    CostructuredArrow.mk (S := jFunctor gens) (Y := (⟨Sum.inl i⟩ : JObj gens)) φ
  let zObj (i : I) (φ : i ⟶ d) : CostructuredArrow (jFunctor gens) d :=
    CostructuredArrow.mk (S := jFunctor gens) (Y := (⟨Sum.inr i⟩ : JObj gens)) φ
  set base : CostructuredArrow (jFunctor gens) d := zObj d (𝟙 d) with hbase
  have hdiag : ∀ (i : I) (φ : i ⟶ d), Zigzag (yObj i φ) (zObj i φ) := by
    intro i φ
    refine Zigzag.of_hom (CostructuredArrow.homMk (jDiag (gens := gens) i) ?_)
    simp only [yObj, zObj]
    rw [jFunctor_map_diag]
    exact Category.id_comp φ
  have hcongr : ∀ {a : I} {φ φ' : a ⟶ d}, φ = φ' →
      Zigzag (zObj a φ) base → Zigzag (zObj a φ') base := fun h hz => h ▸ hz
  have htrans : ∀ {b c : I} (g : b ⟶ c), GeneratedByList gens g → ∀ (ψ : c ⟶ d),
      Zigzag (zObj c ψ) base → Zigzag (zObj b (g ≫ ψ)) base := by
    intro b c g hg
    induction hg with
    | id a => exact fun ψ hψ => hcongr (Category.id_comp ψ).symm hψ
    | @gen a b f hmem =>
        intro ψ hψ
        obtain ⟨g, hg⟩ := exists_jHom_map_eq_of_mem hmem
        have step : Zigzag (yObj a (f ≫ ψ)) (zObj b ψ) := by
          refine Zigzag.of_hom (CostructuredArrow.homMk g ?_)
          simp only [yObj, zObj]
          exact congrArg (· ≫ ψ) hg
        exact (hdiag a (f ≫ ψ)).symm.trans (step.trans hψ)
    | @comp a b c f g hf hg ihf ihg =>
        intro ψ hψ
        exact hcongr (Category.assoc f g ψ).symm (ihf (g ≫ ψ) (ihg ψ hψ))
  have hz : ∀ (i : I) (φ : i ⟶ d), Zigzag (zObj i φ) base := fun i φ =>
    hcongr (Category.comp_id φ) (htrans φ (hgen φ) (𝟙 d) (by
      simpa [hbase] using Zigzag.refl (J := CostructuredArrow (jFunctor gens) d) base))
  have : Nonempty (CostructuredArrow (jFunctor gens) d) := ⟨base⟩
  apply zigzag_isConnected
  intro X Y
  have key : ∀ Z : CostructuredArrow (jFunctor gens) d, Zigzag Z base := by
    intro Z
    obtain ⟨⟨l⟩, -, φ⟩ := Z
    rcases l with i | i
    · exact (hdiag i φ).trans (hz i φ)
    · exact hz i φ
  exact (key X).trans (key Y).symm

/-- **`jFunctor gens` is a final functor** — the cocone half of the Stacks 05XU
bijection, dual to `jFunctor_initial`.

Finality means that each comma category `StructuredArrow d F` is connected.  Its objects
are pairs `(B, φ : d ⟶ F B)`; the diagonal `h_i` joins each `y`-object `(y_i, φ)` to the
corresponding `z`-object `(z_i, φ)`, and the generators `g_k` propagate along the
decomposition of an arbitrary `d ⟶ i` into generators, joining everything to the basepoint
`(y_d, 𝟙 d)`. -/
lemma jFunctor_final (hgen : ∀ {a b : I} (f : a ⟶ b), GeneratedByList gens f) :
    (jFunctor gens).Final := by
  refine ⟨fun d => ?_⟩
  let yObj (i : I) (φ : d ⟶ i) : StructuredArrow d (jFunctor gens) :=
    StructuredArrow.mk (T := jFunctor gens) (Y := (⟨Sum.inl i⟩ : JObj gens)) φ
  let zObj (i : I) (φ : d ⟶ i) : StructuredArrow d (jFunctor gens) :=
    StructuredArrow.mk (T := jFunctor gens) (Y := (⟨Sum.inr i⟩ : JObj gens)) φ
  set base : StructuredArrow d (jFunctor gens) := yObj d (𝟙 d) with hbase
  have hdiag : ∀ (i : I) (φ : d ⟶ i), Zigzag (yObj i φ) (zObj i φ) := by
    intro i φ
    refine Zigzag.of_hom (StructuredArrow.homMk (jDiag (gens := gens) i) ?_)
    simp only [yObj, zObj]
    rw [jFunctor_map_diag]
    exact Category.comp_id φ
  have hcongr : ∀ {a : I} {φ φ' : d ⟶ a}, φ = φ' →
      Zigzag (yObj a φ) base → Zigzag (yObj a φ') base := fun h hz => h ▸ hz
  have htrans : ∀ {b c : I} (g : b ⟶ c), GeneratedByList gens g → ∀ (ψ : d ⟶ b),
      Zigzag (yObj b ψ) base → Zigzag (yObj c (ψ ≫ g)) base := by
    intro b c g hg
    induction hg with
    | id a => exact fun ψ hψ => hcongr (Category.comp_id ψ).symm hψ
    | @gen a b f hmem =>
        intro ψ hψ
        obtain ⟨g, hg⟩ := exists_jHom_map_eq_of_mem hmem
        have step : Zigzag (yObj a ψ) (zObj b (ψ ≫ f)) := by
          refine Zigzag.of_hom (StructuredArrow.homMk g ?_)
          simp only [yObj, zObj]
          exact congrArg (ψ ≫ ·) hg
        exact (hdiag b (ψ ≫ f)).trans (step.symm.trans hψ)
    | @comp a b c f g hf hg ihf ihg =>
        intro ψ hψ
        exact hcongr (Category.assoc ψ f g) (ihg (ψ ≫ f) (ihf ψ hψ))
  have hy : ∀ (i : I) (φ : d ⟶ i), Zigzag (yObj i φ) base := fun i φ =>
    hcongr (Category.id_comp φ) (htrans φ (hgen φ) (𝟙 d) (by
      simpa [hbase] using Zigzag.refl (J := StructuredArrow d (jFunctor gens)) base))
  have : Nonempty (StructuredArrow d (jFunctor gens)) := ⟨base⟩
  apply zigzag_isConnected
  intro X Y
  have key : ∀ Z : StructuredArrow d (jFunctor gens), Zigzag Z base := by
    intro Z
    obtain ⟨-, ⟨l⟩, φ⟩ := Z
    rcases l with i | i
    · exact hy i φ
    · exact (hdiag i φ).symm.trans (hy i φ)
  exact (key X).trans (key Y).symm

end FinitelyGeneratedShape

/-- **Stacks Tag 05XU.**  Let `I` be a small category whose objects form a finite type
and whose morphisms are generated, by composition, from a finite list of arrows.
Then there exist a finite category `J` and a functor `F : J ⥤ I` such that:

* (a) `J` is a finite category (witnessed by the `FinCategory J` instance);
* (b) for every category `C` and every diagram `M : I ⥤ C`:
    - `HasLimit M ↔ HasLimit (F ⋙ M)` and `HasColimit M ↔ HasColimit (F ⋙ M)`
      (existence equivalences), and
    - whenever both limits exist, the *canonical comparison morphism*
      `limit.pre M F : limit M ⟶ limit (F ⋙ M)` is an isomorphism; dually, whenever
      both colimits exist, `colimit.pre M F : colimit (F ⋙ M) ⟶ colimit M` is an
      isomorphism.  Since these comparison morphisms are, by construction,
      compatible with the projections / injections through `F`
      (`limit.pre_π`, `colimit.ι_pre`), this is precisely the statement that `M` and
      `F ⋙ M` have canonically isomorphic (co)limits via the comparison induced by
      `F`;
* (c) `J` is connected iff `I` is connected; and
* (d) `J` is nonempty iff `I` is nonempty. -/
@[stacks 05XU]
theorem exists_finCategory_functor_of_finitelyGeneratedShape {I : Type u} [SmallCategory I]
    (hI : FinitelyGeneratedShape I) :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : FinCategory J) (F : J ⥤ I),
      -- (b) existence equivalences for limits and colimits, for every diagram
      (∀ {C : Type u'} [Category.{v'} C] (M : I ⥤ C),
        (HasLimit M ↔ HasLimit (F ⋙ M)) ∧
        (HasColimit M ↔ HasColimit (F ⋙ M))) ∧
      -- (b) the canonical comparison morphism on limits is an isomorphism
      (∀ {C : Type u'} [Category.{v'} C] (M : I ⥤ C) [HasLimit M] [HasLimit (F ⋙ M)],
        IsIso (limit.pre M F)) ∧
      -- (b) the canonical comparison morphism on colimits is an isomorphism
      (∀ {C : Type u'} [Category.{v'} C] (M : I ⥤ C) [HasColimit M] [HasColimit (F ⋙ M)],
        IsIso (colimit.pre M F)) ∧
      -- (c) connectedness is preserved
      (IsConnected J ↔ IsConnected I) ∧
      -- (d) nonemptiness is preserved
      (Nonempty J ↔ Nonempty I) := by
  obtain ⟨hfin, gens, hgen⟩ := hI
  have : Finite I := hfin
  -- The witness is `FinitelyGeneratedShape.JObj gens` together with the functor
  -- `FinitelyGeneratedShape.jFunctor gens`, which is both initial and final.
  have hinit : (FinitelyGeneratedShape.jFunctor gens).Initial :=
    FinitelyGeneratedShape.jFunctor_initial hgen
  have hfinal : (FinitelyGeneratedShape.jFunctor gens).Final :=
    FinitelyGeneratedShape.jFunctor_final hgen
  refine ⟨FinitelyGeneratedShape.JObj gens, FinitelyGeneratedShape.jCategory,
      FinitelyGeneratedShape.jFinCategory, FinitelyGeneratedShape.jFunctor gens,
      ?_, ?_, ?_, ?_, ?_⟩
  · -- (b1) existence equivalences
    intro C _ M
    exact ⟨(Functor.Initial.hasLimit_comp_iff
              (F := FinitelyGeneratedShape.jFunctor gens) (G := M)).symm,
           (Functor.Final.hasColimit_comp_iff
              (F := FinitelyGeneratedShape.jFunctor gens) (G := M)).symm⟩
  · -- (b2) limit comparison is iso (instance `Functor.Initial.limit_pre_isIso`)
    intro C _ M _ _
    infer_instance
  · -- (b3) colimit comparison is iso (instance `Functor.Final.colimit_pre_isIso`)
    intro C _ M _ _
    infer_instance
  · -- (c) connectedness preserved
    exact Functor.isConnected_iff_of_initial (FinitelyGeneratedShape.jFunctor gens)
  · -- (d) nonemptiness preserved
    constructor
    · rintro ⟨⟨a | a⟩⟩ <;> exact ⟨a⟩
    · rintro ⟨a⟩; exact ⟨⟨Sum.inl a⟩⟩

end CategoryTheory
