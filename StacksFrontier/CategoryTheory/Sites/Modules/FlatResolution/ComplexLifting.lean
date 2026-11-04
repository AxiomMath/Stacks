module

public import StacksCore.Algebra.Homology.QuasiIso
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatResolution.BaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatResolution.CycleBoundaryLifts
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatResolution.SheafFlatQuotient
import StacksCore.Tactic.StacksAttribute

/-!
# Lifting a bounded-above complex across a surjection of sheaves of rings

Let `f : O ⟶ O₀` be a locally surjective morphism of sheaves of commutative rings on a site,
`G` a graded family of flat sheaves of `O`-modules with maps in consecutive degrees, and `K₀` a
cochain complex of `O₀`-modules. Suppose the maps of `G` become a complex, with a specified map
to `K₀`, after extension of scalars, and suppose both `G` and the homology of `K₀` vanish in
sufficiently high degrees. Then `G` can be enlarged to a graded family `F` of flat
`O`-modules, still vanishing in sufficiently high degrees, whose extension of scalars is a
complex *quasi-isomorphic* to `K₀`.

The construction is a descending induction. Above the common bound nothing is changed. At each
step down, the term already built is enlarged by a flat module chosen so that every cycle of
the next term that ought to be a boundary becomes one: Stacks 03EW supplies a flat sheaf
surjecting onto the relevant pullback, and the universal property of extension of scalars turns
that surjection into one after base change. The resulting map of complexes satisfies the
lifting criterion of `HasCycleBoundaryLifts` in every degree below the bound, hence is an
isomorphism on homology there, while above the bound both sides are acyclic.

## Main definitions

* `Stacks.SheafOfModules.ComplexLifting.GradedDifferential`: a graded family with maps in
  consecutive degrees, with no square-zero condition.
* `Stacks.SheafOfModules.ComplexLifting.BaseChangeTo`: the data expressing that a graded
  differential becomes a complex mapping to a given target after extension of scalars.
* `Stacks.SheafOfModules.ComplexLifting.LiftedComplex`: the solution to the lifting problem.

## Main results

* `Stacks.SheafOfModules.ComplexLifting.exists_liftedComplex`: the lifted family exists.

## Implementation notes

The source does not assert that either family of consecutive maps is a complex before base
change, so `GradedDifferential` deliberately has no square-zero field. Extension of scalars is
recorded by its universal property `IsExtensionOfScalars`, which avoids committing to a
particular sheafification model. Vanishing "in sufficiently high degrees" is expressed by an
integer bound.

The object, arrow, ring and extra module universes are independent. The existence theorem uses
their maximum as the ambient module universe, because the flat covers it needs are built from
sums of extensions by zero indexed by objects and sections of the sheaf being covered; the
definitions themselves apply in any module universe.

The descending induction is organised as a well-founded recursion `liftTower` on the integer
degree, whose value at `n` is a `LiftState`: the term in degree `n`, the term in degree `n + 1`
and the arrow between them. Carrying the next term inside the state, rather than reading it off
a separate recursive call, is what keeps the recursion structurally decreasing; the price is
the propositional identification `liftTower_next` between the state's own next term and the
term of the next state, and `LiftArrow.cast` transports arrows along it.

## References

* [Stacks Project, Tag 0DIT](https://stacks.math.columbia.edu/tag/0DIT)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

universe v u w z

namespace Stacks.SheafOfModules.ComplexLifting

open Stacks.Sheaves.ChangeOfRings (ringSheafMap extensionOfScalars)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- A graded family with a map to the next degree. Unlike a cochain complex, no square-zero
condition is imposed. -/
structure GradedDifferential (A : Type*) [Category A] where
  /-- The object in degree `n`. -/
  X : ℤ → A
  /-- The map from degree `n` to degree `n + 1`. -/
  d (n : ℤ) : X n ⟶ X (n + 1)

/-- Data saying that a graded differential becomes a complex over `O₀` after extension of
scalars, together with the induced map to `K₀`. -/
structure BaseChangeTo {O O₀ : Sheaf J CommRingCat.{w}} (f : O ⟶ O₀)
    (G : GradedDifferential (_root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (K₀ : CochainComplex (_root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ)
    (toTarget : ∀ n, G.X n ⟶
      (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj (K₀.X n)) where
  /-- The complex obtained after extension of scalars. -/
  complex : CochainComplex (_root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ
  /-- The canonical map into extension of scalars in every degree. -/
  unit (n : ℤ) : G.X n ⟶
    (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj (complex.X n)
  /-- Each term has the universal property of extension of scalars. -/
  isExtension (n : ℤ) : IsExtensionOfScalars f (G.X n) (complex.X n) (unit n)
  /-- The differential on `complex` is induced by that on `G`. -/
  differential (n : ℤ) :
    G.d n ≫ unit (n + 1) = unit n ≫
      (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).map (complex.d n (n + 1))
  /-- The induced map of complexes to the target. -/
  map : complex ⟶ K₀
  /-- The induced map agrees with the originally specified map in every degree. -/
  map_unit (n : ℤ) :
    unit n ≫ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).map (map.f n) =
      toTarget n

/-- An epimorphism can be lifted through a generating class after pullback. -/
lemma exists_cover_lifting {A : Type*} [Category A] [Abelian A] (P : A → Prop)
    (hP : ∀ X : A, ∃ Y : A, P Y ∧ ∃ p : Y ⟶ X, Epi p)
    {X Y Z : A} (e : X ⟶ Z) [Epi e] (g : Y ⟶ Z) :
    ∃ T : A, P T ∧ ∃ (a : T ⟶ X) (b : T ⟶ Y), Epi b ∧ a ≫ e = b ≫ g := by
  obtain ⟨T, hT, p, _⟩ := hP (pullback e g)
  refine ⟨T, hT, p ≫ pullback.fst e g, p ≫ pullback.snd e g, inferInstance, ?_⟩
  simp only [Category.assoc, pullback.condition]

section Construction

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w z}]
  [HasSheafify J AddCommGrpCat.{max u v w z}]
  {O O₀ : Sheaf J CommRingCat.{w}} {f : O ⟶ O₀}
  {G : GradedDifferential
    (_root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
  {K : CochainComplex
    (_root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ}
  {g : ∀ n, G.X n ⟶
    (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj (K.X n)}
  (B : BaseChangeTo f G K g)

/-- One term of the tower: a flat `O`-module with the universal property of extension of
scalars, a map from the corresponding term of `G`, and compatible maps to the corresponding
terms of `B.complex` and `K`. -/
structure LiftTerm (n : ℤ) where
  /-- The `O`-module in this degree. -/
  X : _root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O)
  /-- Its extension of scalars. -/
  X₀ : _root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)
  /-- The universal morphism. -/
  unit : X ⟶ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj X₀
  /-- `X₀` is the extension of scalars of `X`. -/
  extension : IsExtensionOfScalars f X X₀ unit
  /-- `X` is flat. -/
  flat : AlgebraicGeometry.SheafOfModules.IsFlat X
  /-- The map from the prescribed term of `G`. -/
  ι : G.X n ⟶ X
  /-- The map from the prescribed term after base change. -/
  β : B.complex.X n ⟶ X₀
  /-- The two prescribed maps are compatible with the universal morphisms. -/
  ι_unit : ι ≫ unit = B.unit n ≫
    (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).map β
  /-- The map to the target. -/
  α : X₀ ⟶ K.X n
  /-- The map to the target extends the prescribed one. -/
  β_α : β ≫ α = B.map.f n

/-- An arrow of the tower between consecutive terms, compatible with everything in sight. -/
structure LiftArrow {n : ℤ} (T : LiftTerm B n) (T' : LiftTerm B (n + 1)) where
  /-- The map of `O`-modules. -/
  d : T.X ⟶ T'.X
  /-- The map of `O₀`-modules. -/
  d₀ : T.X₀ ⟶ T'.X₀
  /-- The two maps correspond under the universal morphisms. -/
  unit_d : d ≫ T'.unit = T.unit ≫
    (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).map d₀
  /-- Compatibility with the maps from `G`. -/
  ι_d : G.d n ≫ T'.ι = T.ι ≫ d
  /-- Compatibility with the maps from `B.complex`. -/
  β_d : B.complex.d n (n + 1) ≫ T'.β = T.β ≫ d₀
  /-- Compatibility with the maps to `K`. -/
  α_d : T.α ≫ K.d n (n + 1) = d₀ ≫ T'.α

/-- A term of the tower in degree `n`, the term in degree `n + 1`, and the arrow between
them. -/
structure LiftState (n : ℤ) where
  /-- The term in degree `n`. -/
  term : LiftTerm B n
  /-- The term in degree `n + 1`. -/
  next : LiftTerm B (n + 1)
  /-- The arrow between them. -/
  arrow : LiftArrow B term next

/-- The term of the tower above the bound: the prescribed data, unchanged. -/
noncomputable def initialTerm
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (G.X n)) (n : ℤ) :
    LiftTerm B n where
  X := G.X n
  X₀ := B.complex.X n
  unit := B.unit n
  extension := B.isExtension n
  flat := hflat n
  ι := 𝟙 _
  β := 𝟙 _
  ι_unit := by simp
  α := B.map.f n
  β_α := by simp

/-- The state of the tower above the bound. -/
noncomputable def initialState
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (G.X n)) (n : ℤ) :
    LiftState B n where
  term := initialTerm B hflat n
  next := initialTerm B hflat (n + 1)
  arrow :=
    { d := G.d n
      d₀ := B.complex.d n (n + 1)
      unit_d := B.differential n
      ι_d := by simp [initialTerm]
      β_d := by simp [initialTerm]
      α_d := B.map.comm n (n + 1) }

/-- The map from the kernel of the arrow of a state to the cycles of `K`, induced by the map to
the target. -/
noncomputable def stateCyclesMap {n : ℤ} (S : LiftState B n) :
    kernel S.arrow.d₀ ⟶ K.cycles n :=
  K.liftCycles (kernel.ι S.arrow.d₀ ≫ S.term.α) (n + 1) (by simp) (by
    rw [Category.assoc, S.arrow.α_d, ← Category.assoc, kernel.condition, zero_comp])

/-- `stateCyclesMap` is characterized by its composition with the inclusion of cycles. -/
lemma stateCyclesMap_i {n : ℤ} (S : LiftState B n) :
    stateCyclesMap B S ≫ K.iCycles n = kernel.ι S.arrow.d₀ ≫ S.term.α :=
  K.liftCycles_i _ _ _ _

/-- The pullback whose surjection is what the enlargement at one step must supply. -/
noncomputable abbrev stepPullback {n : ℤ} (S : LiftState B (n + 1)) :=
  pullback (stateCyclesMap B S) (K.toCycles n (n + 1))

/-- The flat module added at one step of the descending induction, with its surjection onto
`stepPullback`. -/
structure LiftCell {n : ℤ} (S : LiftState B (n + 1)) where
  /-- The added `O`-module. -/
  Q : _root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O)
  /-- Its extension of scalars. -/
  Q₀ : _root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)
  /-- The added module is flat. -/
  flat : AlgebraicGeometry.SheafOfModules.IsFlat Q
  /-- The universal morphism. -/
  unit : Q ⟶ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj Q₀
  /-- `Q₀` is the extension of scalars of `Q`. -/
  extension : IsExtensionOfScalars f Q Q₀ unit
  /-- The map into the term already built. -/
  a : Q ⟶ S.term.X
  /-- The surjection onto the pullback. -/
  q : Q₀ ⟶ stepPullback B S
  /-- `q` is an epimorphism. -/
  epi_q : Epi q
  /-- The two maps correspond under the universal morphisms. -/
  a_unit : a ≫ S.term.unit = unit ≫
    (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).map
      (q ≫ pullback.fst _ _ ≫ kernel.ι S.arrow.d₀)

/-- The enlargement datum exists: Stacks 03EW supplies a flat sheaf of modules surjecting onto
any sheaf of modules, and the universal property of extension of scalars converts that
surjection into one onto the pullback. -/
noncomputable def liftingCell (hf : Sheaf.IsLocallySurjective f) {n : ℤ}
    (S : LiftState B (n + 1)) : LiftCell B S := Classical.choice <| by
  let R := _root_.SheafOfModules.restrictScalars (ringSheafMap f)
  have : Epi S.term.unit :=
    IsExtensionOfScalars.epi_unit.{v, u, w, max u v z} f hf S.term.extension
  have hc (M : _root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
    Stacks.SheafOfModules.FlatResolution.exists_epi_from_flat J O M
  obtain ⟨Q, hQ, a, b, hb, hab⟩ := exists_cover_lifting
    AlgebraicGeometry.SheafOfModules.IsFlat hc S.term.unit
    (R.map (pullback.fst (stateCyclesMap B S) (K.toCycles n (n + 1)) ≫
      kernel.ι S.arrow.d₀))
  let uQ := extensionOfScalarsUnit.{v, u, w, max u v z} f Q
  have hQext := extensionOfScalarsUnit_isExtension.{v, u, w, max u v z} f Q
  let q := IsExtensionOfScalars.desc f hQext b
  have hq : uQ ≫ R.map q = b := IsExtensionOfScalars.desc_spec f hQext b
  exact ⟨
    { Q := Q
      Q₀ := (extensionOfScalars.{max u v z, v, u, w} f).obj Q
      flat := hQ
      unit := uQ
      extension := hQext
      a := a
      q := q
      epi_q := IsExtensionOfScalars.epi_desc f hQext b
      a_unit := by rwa [R.map_comp, ← Category.assoc, hq] }⟩

/-- The term of the tower in degree `n` produced by one step of the descending induction: the
prescribed term of `G` enlarged by the added flat module. -/
noncomputable def enlargedTerm {n : ℤ} (S : LiftState B (n + 1)) (D : LiftCell B S)
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (G.X n)) : LiftTerm B n where
  X := pairObj (G.X n) D.Q
  X₀ := pairObj (B.complex.X n) D.Q₀
  unit := pairDesc
    (B.unit n ≫ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).map (pairInl _ _))
    (D.unit ≫ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).map (pairInr _ _))
  extension := IsExtensionOfScalars.pair f (B.isExtension n) D.extension
  flat := pair_isFlat (hflat n) D.flat
  ι := pairInl _ _
  β := pairInl _ _
  ι_unit := pairInl_desc _ _
  α := pairDesc (B.map.f n) (D.q ≫ pullback.snd _ _)
  β_α := pairInl_desc _ _

/-- The arrow out of `enlargedTerm`. -/
noncomputable def enlargedArrow {n : ℤ} (S : LiftState B (n + 1)) (D : LiftCell B S)
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (G.X n)) :
    LiftArrow B (enlargedTerm B S D hflat) S.term where
  d := pairDesc (G.d n ≫ S.term.ι) D.a
  d₀ := pairDesc (B.complex.d n (n + 1) ≫ S.term.β)
    (D.q ≫ pullback.fst _ _ ≫ kernel.ι S.arrow.d₀)
  unit_d := by
    apply pair_hom_ext
    · simp only [enlargedTerm, ← Category.assoc, pairInl_desc]
      rw [Category.assoc, S.term.ι_unit, ← Category.assoc, B.differential,
        Category.assoc, ← Functor.map_comp, Category.assoc, ← Functor.map_comp, pairInl_desc]
    · simp only [enlargedTerm, ← Category.assoc, pairInr_desc]
      rw [Category.assoc, ← Functor.map_comp, pairInr_desc]
      exact D.a_unit
  ι_d := (pairInl_desc _ _).symm
  β_d := (pairInl_desc _ _).symm
  α_d := by
    apply pair_hom_ext
    · simp only [enlargedTerm, ← Category.assoc, pairInl_desc]
      rw [Category.assoc, S.term.β_α, B.map.comm]
    · simp only [enlargedTerm, ← Category.assoc, pairInr_desc]
      simp only [Category.assoc]
      rw [← stateCyclesMap_i, ← Category.assoc (pullback.fst _ _) (stateCyclesMap B S),
        pullback.condition, Category.assoc, K.toCycles_i]

/-- One step of the descending induction. -/
noncomputable def nextState (hf : Sheaf.IsLocallySurjective f)
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (G.X n)) {n : ℤ}
    (S : LiftState B (n + 1)) : LiftState B n where
  term := enlargedTerm B S (liftingCell B hf S) hflat
  next := S.term
  arrow := enlargedArrow B S (liftingCell B hf S) hflat

attribute [local implicit_reducible] initialTerm initialState enlargedTerm enlargedArrow
  nextState

/-- The two consecutive arrows produced by one step of the induction compose to zero after base
change. -/
lemma enlargedArrow_comp {n : ℤ} (S : LiftState B (n + 1)) (D : LiftCell B S)
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (G.X n)) :
    (enlargedArrow B S D hflat).d₀ ≫ S.arrow.d₀ = 0 := by
  apply pair_hom_ext
  · dsimp only [enlargedArrow]
    rw [← Category.assoc, pairInl_desc, Category.assoc, ← S.arrow.β_d, ← Category.assoc,
      B.complex.d_comp_d]
    simp
  · dsimp only [enlargedArrow]
    rw [← Category.assoc, pairInr_desc, Category.assoc, Category.assoc, kernel.condition]
    simp

/-- The cycle-boundary lifting property at one step of the induction: a cycle of the term
already built that maps to a boundary of `K` lifts to the enlarged term after passing to a
cover. -/
lemma enlarged_lift {n : ℤ} (S : LiftState B (n + 1)) (D : LiftCell B S)
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (G.X n))
    {T : _root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    (a : T ⟶ S.term.X₀) (b : T ⟶ K.X n) (ha : a ≫ S.arrow.d₀ = 0)
    (hab : a ≫ S.term.α = b ≫ K.d n (n + 1)) :
    ∃ (Y : _root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
      (e : Y ⟶ T),
      Epi e ∧ ∃ c : Y ⟶ (enlargedTerm B S D hflat).X₀,
        c ≫ (enlargedArrow B S D hflat).d₀ = e ≫ a ∧
        c ≫ (enlargedTerm B S D hflat).α = e ≫ b := by
  let a' := kernel.lift S.arrow.d₀ a ha
  have hab' : a' ≫ stateCyclesMap B S = b ≫ K.toCycles n (n + 1) := by
    rw [← cancel_mono (K.iCycles (n + 1)), Category.assoc, stateCyclesMap_i, ← Category.assoc,
      kernel.lift_ι, Category.assoc, K.toCycles_i]
    exact hab
  let k : T ⟶ stepPullback B S := pullback.lift a' b hab'
  have : Epi D.q := D.epi_q
  let e := pullback.snd D.q k
  let c := pullback.fst D.q k ≫ pairInr (B.complex.X n) D.Q₀
  refine ⟨pullback D.q k, e, inferInstance, c, ?_, ?_⟩
  · simp [c, e, k, a', enlargedArrow, pullback.condition_assoc, pullback.lift_fst_assoc]
  · simp only [c, e, k, enlargedTerm, Category.assoc, pairInr_desc, pullback.condition_assoc]
    rw [pullback.lift_snd]

/-- Transport an arrow of the tower along an equality of its target term. -/
def LiftArrow.cast {n : ℤ} {T : LiftTerm B n} {T' T'' : LiftTerm B (n + 1)}
    (a : LiftArrow B T T') (h : T' = T'') : LiftArrow B T T'' := h ▸ a

/-- The base-changed map of a transported arrow, up to the induced `eqToHom`. -/
lemma LiftArrow.cast_d₀ {n : ℤ} {T : LiftTerm B n} {T' T'' : LiftTerm B (n + 1)}
    (a : LiftArrow B T T') (h : T' = T'') :
    (a.cast B h).d₀ = a.d₀ ≫ eqToHom (congrArg LiftTerm.X₀ h) := by
  subst h
  simp [LiftArrow.cast]

/-- Two consecutive arrows compose to zero when the lower one comes from a step of the
induction. -/
lemma state_comp_of_next (hf : Sheaf.IsLocallySurjective f)
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (G.X n)) {n : ℤ}
    (S : LiftState B n) (S' : LiftState B (n + 1)) (T : LiftTerm B (n + 1 + 1))
    (h : S.next = S'.term) (h' : S'.next = T) (hs : S = nextState B hf hflat S') :
    (S.arrow.cast B h).d₀ ≫ (S'.arrow.cast B h').d₀ = 0 := by
  subst S
  simp only [nextState, LiftArrow.cast_d₀, eqToHom_refl, Category.comp_id, ← Category.assoc]
  rw [enlargedArrow_comp, zero_comp]

/-- Two consecutive arrows compose to zero when both are the prescribed ones. -/
lemma state_comp_of_initial
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (G.X n)) {n : ℤ}
    (S : LiftState B n) (S' : LiftState B (n + 1)) (T : LiftTerm B (n + 1 + 1))
    (h : S.next = S'.term) (h' : S'.next = T) (hs : S = initialState B hflat n)
    (hs' : S' = initialState B hflat (n + 1)) :
    (S.arrow.cast B h).d₀ ≫ (S'.arrow.cast B h').d₀ = 0 := by
  subst S S'
  cases h
  cases h'
  simp only [LiftArrow.cast_d₀, initialState, initialTerm, eqToHom_refl, Category.comp_id]
  rw [B.complex.d_comp_d]

/-- The cycle-boundary lifting property for a step of the induction, transported to the
tower's arrows. -/
lemma state_lift_of_next (hf : Sheaf.IsLocallySurjective f)
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (G.X n)) {n : ℤ}
    (S : LiftState B n) (S' : LiftState B (n + 1)) (h : S.next = S'.term)
    (hs : S = nextState B hf hflat S')
    {T : _root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    (a : T ⟶ S'.term.X₀) (b : T ⟶ K.X n) (ha : a ≫ S'.arrow.d₀ = 0)
    (hab : a ≫ S'.term.α = b ≫ K.d n (n + 1)) :
    ∃ (Y : _root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
      (e : Y ⟶ T),
      Epi e ∧ ∃ c : Y ⟶ S.term.X₀,
        c ≫ (S.arrow.cast B h).d₀ = e ≫ a ∧ c ≫ S.term.α = e ≫ b := by
  subst S
  cases h
  simpa only [nextState, LiftArrow.cast] using
    enlarged_lift B S' (liftingCell B hf S') hflat a b ha hab

variable (hf : Sheaf.IsLocallySurjective f)
  (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (G.X n)) (N : ℤ)

/-- The tower: above `N` the prescribed data, and below it one step of enlargement at a time. -/
noncomputable def liftTower (n : ℤ) : LiftState B n :=
  if N < n then initialState B hflat n
  else nextState B hf hflat (liftTower (n + 1))
termination_by (N + 1 - n).toNat
decreasing_by
  simp_wf
  omega

/-- Above the bound the tower is the prescribed data. -/
lemma liftTower_of_gt (n : ℤ) (hn : N < n) :
    liftTower B hf hflat N n = initialState B hflat n := by
  rw [liftTower, if_pos hn]

/-- Below the bound the tower is one step of enlargement. -/
lemma liftTower_of_le (n : ℤ) (hn : n ≤ N) :
    liftTower B hf hflat N n = nextState B hf hflat (liftTower B hf hflat N (n + 1)) := by
  rw [liftTower, if_neg (not_lt.mpr hn)]

/-- The next term carried by the tower's state at `n` is the term of its state at `n + 1`. -/
lemma liftTower_next (n : ℤ) :
    (liftTower B hf hflat N n).next = (liftTower B hf hflat N (n + 1)).term := by
  by_cases hn : N < n
  · rw [liftTower_of_gt B hf hflat N n hn, liftTower_of_gt B hf hflat N (n + 1) (by omega)]
    rfl
  · rw [liftTower_of_le B hf hflat N n (by omega)]
    rfl

/-- The arrow of the tower from degree `n` to degree `n + 1`. -/
noncomputable def towerArrow (n : ℤ) :
    LiftArrow B (liftTower B hf hflat N n).term (liftTower B hf hflat N (n + 1)).term :=
  ((liftTower B hf hflat N n).arrow).cast B (liftTower_next B hf hflat N n)

/-- The base-changed arrow of the tower, up to the induced `eqToHom`. -/
lemma towerArrow_d₀ (n : ℤ) :
    (towerArrow B hf hflat N n).d₀ = (liftTower B hf hflat N n).arrow.d₀ ≫
      eqToHom (congrArg LiftTerm.X₀ (liftTower_next B hf hflat N n)) :=
  LiftArrow.cast_d₀ B _ _

/-- The base-changed arrows of the tower form a complex. -/
lemma towerArrow_comp (n : ℤ) :
    (towerArrow B hf hflat N n).d₀ ≫ (towerArrow B hf hflat N (n + 1)).d₀ = 0 := by
  by_cases hn : N < n
  · exact state_comp_of_initial B hflat _ _ _ (liftTower_next B hf hflat N n)
      (liftTower_next B hf hflat N (n + 1)) (liftTower_of_gt B hf hflat N n hn)
      (liftTower_of_gt B hf hflat N (n + 1) (by omega))
  · exact state_comp_of_next B hf hflat _ _ _ (liftTower_next B hf hflat N n)
      (liftTower_next B hf hflat N (n + 1)) (liftTower_of_le B hf hflat N n (by omega))

/-- The tower satisfies the cycle-boundary lifting property in every degree below the bound. -/
lemma tower_lift (n : ℤ) (hn : n ≤ N)
    {T : _root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    (a : T ⟶ (liftTower B hf hflat N (n + 1)).term.X₀) (b : T ⟶ K.X n)
    (ha : a ≫ (towerArrow B hf hflat N (n + 1)).d₀ = 0)
    (hab : a ≫ (liftTower B hf hflat N (n + 1)).term.α = b ≫ K.d n (n + 1)) :
    ∃ (Y : _root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
      (e : Y ⟶ T),
      Epi e ∧ ∃ c : Y ⟶ (liftTower B hf hflat N n).term.X₀,
        c ≫ (towerArrow B hf hflat N n).d₀ = e ≫ a ∧
        c ≫ (liftTower B hf hflat N n).term.α = e ≫ b := by
  have ha' : a ≫ (liftTower B hf hflat N (n + 1)).arrow.d₀ = 0 := by
    rw [towerArrow_d₀, ← Category.assoc] at ha
    exact (cancel_mono _).mp (by simpa only [zero_comp] using ha)
  exact state_lift_of_next B hf hflat _ _ (liftTower_next B hf hflat N n)
    (liftTower_of_le B hf hflat N n hn) a b ha' hab

/-- The base-changed terms and arrows of the tower, as a cochain complex. -/
noncomputable def towerComplex : CochainComplex
    (_root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ :=
  CochainComplex.of (fun n => (liftTower B hf hflat N n).term.X₀)
    (fun n => (towerArrow B hf hflat N n).d₀) (towerArrow_comp B hf hflat N)

/-- The differential of the tower's complex is the base-changed arrow of the tower. -/
lemma towerComplex_d (n : ℤ) :
    (towerComplex B hf hflat N).d n (n + 1) = (towerArrow B hf hflat N n).d₀ := by
  simp only [towerComplex, CochainComplex.of_d]

/-- The map from the tower's complex to the target. -/
noncomputable def towerComplexMap : towerComplex B hf hflat N ⟶ K where
  f n := (liftTower B hf hflat N n).term.α
  comm' i j hij := by
    obtain rfl : j = i + 1 := by simpa using hij.symm
    simpa only [towerComplex, CochainComplex.of_d] using (towerArrow B hf hflat N i).α_d

/-- Above the bound the terms of the tower vanish when those of `G` do. -/
lemma isZero_liftTower_X (hG : ∀ n, N < n → IsZero (G.X n)) (n : ℤ) (hn : N < n) :
    IsZero (liftTower B hf hflat N n).term.X := by
  rw [liftTower_of_gt B hf hflat N n hn]
  exact hG n hn

/-- The map from the tower's complex satisfies the cycle-boundary lifting property below the
bound. -/
lemma hasCycleBoundaryLifts_towerComplexMap (n : ℤ) (hn : n ≤ N) :
    HasCycleBoundaryLifts (towerComplexMap B hf hflat N) n := by
  intro V a b ha hab
  rw [towerComplex_d]
  exact tower_lift B hf hflat N n hn a b (by rwa [towerComplex_d] at ha) hab

/-- The map from the tower's complex is a quasi-isomorphism when `G` and the homology of `K`
vanish above the bound. -/
lemma quasiIso_towerComplexMap (hG : ∀ n, N < n → IsZero (G.X n))
    (hK : ∀ n, N < n → IsZero (K.homology n)) : QuasiIso (towerComplexMap B hf hflat N) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hn : n ≤ N
  · exact isIso_homologyMap_of_lifts _ n (hasCycleBoundaryLifts_towerComplexMap B hf hflat N n hn)
      (hasCycleBoundaryLifts_towerComplexMap B hf hflat N (n - 1) (by omega))
  · have hz : IsZero ((towerComplex B hf hflat N).X n) :=
      isZero_of_isExtensionOfScalars f (liftTower B hf hflat N n).term.extension
        (isZero_liftTower_X B hf hflat N hG n (by omega))
    exact (HomologicalComplex.ExactAt.of_isZero hz).isZero_homology.isIso (hK n (by omega)) _

end Construction

/-- A solution to the lifting problem of Stacks 0DIT. -/
structure LiftedComplex [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [HasSheafify J AddCommGrpCat.{z}] {O O₀ : Sheaf J CommRingCat.{w}} (f : O ⟶ O₀)
    (G : GradedDifferential (_root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (K₀ : CochainComplex (_root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ)
    (g : ∀ n, G.X n ⟶
      (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj (K₀.X n)) where
  /-- The lifted graded family and its consecutive maps. -/
  F : GradedDifferential (_root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O))
  /-- Every lifted term is flat. -/
  flat (n : ℤ) : AlgebraicGeometry.SheafOfModules.IsFlat (F.X n)
  /-- The lifted family vanishes in sufficiently high degrees. -/
  boundedAbove : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (F.X n)
  /-- The map from the initially prescribed family. -/
  fromG (n : ℤ) : G.X n ⟶ F.X n
  /-- The maps from `G` commute with the consecutive maps. -/
  fromG_d (n : ℤ) : G.d n ≫ fromG (n + 1) = fromG n ≫ F.d n
  /-- The specified maps from the lifted terms to the target terms. -/
  toTarget (n : ℤ) : F.X n ⟶
    (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj (K₀.X n)
  /-- The composite from `G` to the target is the originally specified map. -/
  fromG_toTarget (n : ℤ) : fromG n ≫ toTarget n = g n
  /-- After extension of scalars, `F` becomes a complex mapping to `K₀`. -/
  baseChange : BaseChangeTo f F K₀ toTarget
  /-- The resulting map after extension of scalars is a quasi-isomorphism. -/
  quasiIso : QuasiIso baseChange.map

/-- **Stacks 0DIT.** A bounded-above flat lifting exists for a bounded-above complex and a
bounded-above graded flat family whose given maps form a map of complexes after extension of
scalars. The ambient module universe contains the site and the ring sheaves. -/
@[stacks 0DIT]
theorem exists_liftedComplex [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w z}]
    [HasSheafify J AddCommGrpCat.{max u v w z}] {O O₀ : Sheaf J CommRingCat.{w}} (f : O ⟶ O₀)
    (hf : Sheaf.IsLocallySurjective f)
    (G : GradedDifferential
      (_root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (K₀ : CochainComplex
      (_root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ)
    (g : ∀ n, G.X n ⟶
      (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj (K₀.X n))
    (hGflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (G.X n))
    (hGbounded : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (G.X n))
    (hKbounded : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n))
    (hG₀ : BaseChangeTo f G K₀ g) :
    Nonempty (LiftedComplex f G K₀ g) := by
  classical
  obtain ⟨NG, hG⟩ := hGbounded
  obtain ⟨NK, hK⟩ := hKbounded
  let N := max NG NK
  have hGN (n : ℤ) (hn : N < n) : IsZero (G.X n) := hG n (by dsimp only [N] at hn; omega)
  have hKN (n : ℤ) (hn : N < n) : IsZero (K₀.homology n) := hK n (by dsimp only [N] at hn; omega)
  let T := liftTower hG₀ hf hGflat N
  let d := towerArrow hG₀ hf hGflat N
  let F : GradedDifferential
      (_root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
    ⟨fun n => (T n).term.X, fun n => (d n).d⟩
  let p := towerComplexMap hG₀ hf hGflat N
  let t : ∀ n, F.X n ⟶
      (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj (K₀.X n) :=
    fun n => (T n).term.unit ≫
      (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).map (p.f n)
  refine ⟨{
    F := F
    flat := fun n => (T n).term.flat
    boundedAbove := ⟨N + 1, fun n hn => isZero_liftTower_X hG₀ hf hGflat N hGN n (by omega)⟩
    fromG := fun n => (T n).term.ι
    fromG_d := fun n => (d n).ι_d
    toTarget := t
    fromG_toTarget := ?_
    baseChange := {
      complex := towerComplex hG₀ hf hGflat N
      unit := fun n => (T n).term.unit
      isExtension := fun n => (T n).term.extension
      differential := ?_
      map := p
      map_unit := fun n => rfl }
    quasiIso := quasiIso_towerComplexMap hG₀ hf hGflat N hGN hKN }⟩
  · intro n
    dsimp only [t, T, p, towerComplexMap]
    rw [← Category.assoc, LiftTerm.ι_unit, Category.assoc, ← Functor.map_comp,
      LiftTerm.β_α, hG₀.map_unit]
  · intro n
    simpa only [F, T, d, towerComplex, CochainComplex.of_d] using (d n).unit_d

end Stacks.SheafOfModules.ComplexLifting

end
