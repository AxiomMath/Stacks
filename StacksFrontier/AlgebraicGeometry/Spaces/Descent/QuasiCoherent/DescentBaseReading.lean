module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.DatumBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FamilyPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcChartFullness

/-!
# Reading a quasi-coherent descent datum through a module on an intermediate base

Let `(w i : W i ⟶ R)` be a family of algebraic spaces over `R`, let `ρ : R ⟶ X` and let `D` be a
descent datum for quasi-coherent modules relative to `(w i ≫ ρ : W i ⟶ X)`.  Suppose the base
change of `D` to `R` — `AlgebraicGeometry.Space.QuasiCoherentDescent.baseChangeDatum` — is the
canonical descent datum of an `𝒪_R`-module `N`, by isomorphisms `ε i : D.F i ≅ (w i)^*N`.

For a test space `T` carrying `α : T ⟶ W i` and `β : T ⟶ W j` with equal composites to `X`, the
pairwise isomorphism `D.transition i j` then reads as an isomorphism of the two inverse images
of `N` along `α ≫ w i` and `β ≫ w j`.  **That reading is the object this file is about**: it is
transitive, it is compatible with inverse images, and — this is where `ε` enters — it depends on
`α` and `β` only through those two composites.

The last property is what a descent datum for the one-member family `{ρ}` is made of: the two
inverse images of `N` to `R ×_X R` are identified by gluing these readings along a covering of
`R ×_X R` whose members map to members of `(w i)` over both projections.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.readN` is the reading.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.readN_trans`: **the readings compose**, which is
  the cocycle condition of `D`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.readN_map`: **the inverse image of a reading is
  the reading on the source**, which is the compatibility of the pairwise isomorphisms of `D`
  with further inverse images.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_eq_canonicalComparison`: read at two
  morphisms with equal composites **to `R`**, the pairwise isomorphism of `D` is the canonical
  comparison of Stacks 04W5 of the two inverse images of `N`, conjugated by `ε`.  This is the
  hypothesis on `ε` carried to an arbitrary test space.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.readN_refl` and `…readN_legs`: **the reading at
  two morphisms with equal composites to `R` is the identity**, and consequently **the reading
  depends on the two legs only through their composites to `R`.**

## Implementation notes

The reading is built from the comparisons with their legs named, so that it is stated at
morphisms `x`, `y` to `R` given together with the equations `α ≫ w i = x` and `β ≫ w j = y`
rather than at the composites themselves; `…readN_map` then produces the reading at a further
test space with no transport, which is what makes the gluing below affordable.

`CategoryTheory.Iso.eq_of_trans_eq_trans` cancels one isomorphism on each side of an equality of
composites of isomorphisms.  It is stated at a variable category, so that nothing is normalized
at the types of the modules on an algebraic space; the two middle composites are allowed
different middle objects, which is what the conjugation by `ε` produces.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Iso

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

/-- **One isomorphism cancelled on each side of an equality of composites.**  The two composites
are allowed different middle objects, and the four factors are named arguments at a variable
category, so that a consumer whose isomorphisms are comparisons of inverse images of modules
instantiates it with no reduction. -/
theorem eq_of_trans_eq_trans {A B₁ B₂ C₁ C₂ A' : C} (e : A ≅ B₁) (f : B₂ ≅ A')
    {g : B₁ ≅ C₁} {g' : C₁ ≅ B₂} {h : B₁ ≅ C₂} {h' : C₂ ≅ B₂}
    (H : e ≪≫ g ≪≫ g' ≪≫ f = e ≪≫ h ≪≫ h' ≪≫ f) : g ≪≫ g' = h ≪≫ h' := by
  have key := congrArg (fun t : A ≅ A' => e.symm ≪≫ t ≪≫ f.symm) H
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id, Iso.trans_refl]
    using key

/-- **One isomorphism cancelled on each side of an equality of two conjugates.**  The
conjugating isomorphisms are the same on the two sides, which is what distinguishes this from
`…eq_of_trans_eq_trans`, whose two composites have different middle objects. -/
theorem cancel_conj {A B D E : C} (e : A ≅ B) (f : D ≅ E) {g h : B ≅ D}
    (H : e ≪≫ g ≪≫ f = e ≪≫ h ≪≫ f) : g = h := by
  simpa using eq_of_trans_eq_trans e f (g := g) (g' := Iso.refl D) (h := h) (h' := Iso.refl D)
    (by simpa using H)

end CategoryTheory.Iso

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Legs

variable {I : Type v} {X : AlgebraicSpaces B S hS}

/-- Two morphisms out of a test space with equal composites to `X` factor through the pairwise
fibre product. -/
theorem exists_pairLeg (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    {T : AlgebraicSpaces B S hS} (i j : I) (α : T ⟶ Y i) (β : T ⟶ Y j)
    (h : α ≫ f i = β ≫ f j) :
    ∃ v : T ⟶ pair B S hS Y f i j,
      v ≫ pairFst B S hS Y f i j = α ∧ v ≫ pairSnd B S hS Y f i j = β :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS (f i) (f j)).exists_lift α β h

end Legs

section Reading

variable {I : Type v} {X R : AlgebraicSpaces B S hS} (W : I → AlgebraicSpaces B S hS)
  (w : ∀ i, W i ⟶ R) (ρ : R ⟶ X) (D : DescentDatum B S hS W (fun t => w t ≫ ρ))
  (N : Modules.{u, u} B S hS R.1 R.2)
  (ε : ∀ i, D.F i ≅ (modulePullback B S hS (w i)).obj N)

/-- **The pairwise isomorphism of `D` at `i`, `j`, read on a test space carrying `α : T ⟶ W i`
and `β : T ⟶ W j`, as an isomorphism of the two inverse images of `N` along `x = α ≫ w i` and
`y = β ≫ w j`.** -/
def readN {T : AlgebraicSpaces B S hS} (i j : I) (α : T ⟶ W i) (β : T ⟶ W j)
    (x y : T ⟶ R) (hx : α ≫ w i = x) (hy : β ≫ w j = y)
    (v : T ⟶ pair B S hS W (fun t => w t ≫ ρ) i j)
    (hv₁ : v ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j = α)
    (hv₂ : v ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j = β) :
    (modulePullback B S hS x).obj N ≅ (modulePullback B S hS y).obj N :=
  pullbackComparison B S hS α (w i) x hx N ≪≫
    (modulePullback B S hS α).mapIso (ε i).symm ≪≫
    transitionOn B S hS W (fun t => w t ≫ ρ) D.F D.transition i j v α β hv₁ hv₂ ≪≫
    (modulePullback B S hS β).mapIso (ε j) ≪≫
    (pullbackComparison B S hS β (w j) y hy N).symm

/-- **The readings compose.**  This is the cocycle condition of `D`, the conjugating
isomorphisms at the middle index cancelling. -/
theorem readN_trans {T : AlgebraicSpaces B S hS} (i j k : I) (α : T ⟶ W i) (β : T ⟶ W j)
    (γ : T ⟶ W k) (x y z : T ⟶ R) (hx : α ≫ w i = x) (hy : β ≫ w j = y) (hz : γ ≫ w k = z)
    (vij : T ⟶ pair B S hS W (fun t => w t ≫ ρ) i j)
    (hij₀ : vij ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j = α)
    (hij₁ : vij ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j = β)
    (vjk : T ⟶ pair B S hS W (fun t => w t ≫ ρ) j k)
    (hjk₀ : vjk ≫ pairFst B S hS W (fun t => w t ≫ ρ) j k = β)
    (hjk₁ : vjk ≫ pairSnd B S hS W (fun t => w t ≫ ρ) j k = γ)
    (vik : T ⟶ pair B S hS W (fun t => w t ≫ ρ) i k)
    (hik₀ : vik ≫ pairFst B S hS W (fun t => w t ≫ ρ) i k = α)
    (hik₁ : vik ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i k = γ) :
    readN B S hS W w ρ D N ε i j α β x y hx hy vij hij₀ hij₁ ≪≫
        readN B S hS W w ρ D N ε j k β γ y z hy hz vjk hjk₀ hjk₁ =
      readN B S hS W w ρ D N ε i k α γ x z hx hz vik hik₀ hik₁ := by
  rw [readN, readN, readN]
  simp only [Functor.mapIso_symm, Iso.trans_assoc, Iso.symm_self_id_assoc,
    Iso.self_symm_id_assoc]
  rw [Iso.subst_trans₂ (D.cocycle i j k T α β γ vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁)]

/-- **The inverse image of a reading along a further morphism is the reading on the source.** -/
theorem readN_map {T T' : AlgebraicSpaces B S hS} (q : T' ⟶ T) (i j : I) (α : T ⟶ W i)
    (β : T ⟶ W j) (x y : T ⟶ R) (hx : α ≫ w i = x) (hy : β ≫ w j = y)
    (v : T ⟶ pair B S hS W (fun t => w t ≫ ρ) i j)
    (hv₁ : v ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j = α)
    (hv₂ : v ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j = β)
    (α' : T' ⟶ W i) (β' : T' ⟶ W j) (hα' : q ≫ α = α') (hβ' : q ≫ β = β')
    (x' y' : T' ⟶ R) (hx' : q ≫ x = x') (hy' : q ≫ y = y')
    (hxx : α' ≫ w i = x') (hyy : β' ≫ w j = y')
    (hv₁' : (q ≫ v) ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j = α')
    (hv₂' : (q ≫ v) ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j = β') :
    (modulePullback B S hS q).mapIso (readN B S hS W w ρ D N ε i j α β x y hx hy v hv₁ hv₂) =
      (pullbackComparison B S hS q x x' hx' N).symm ≪≫
        readN B S hS W w ρ D N ε i j α' β' x' y' hxx hyy (q ≫ v) hv₁' hv₂' ≪≫
        pullbackComparison B S hS q y y' hy' N := by
  rw [readN, readN]
  simp only [Functor.mapIso_trans, Functor.mapIso_symm]
  rw [modulePullback_mapIso_pullbackComparison B S hS q α (w i) x hx α' hα' x' hxx hx' N,
    modulePullback_mapIso_mapIso B S hS q α α' hα' (ε i),
    modulePullback_mapIso_transitionOn B S hS W (fun t => w t ≫ ρ) D.F D.transition q i j v
      α β hv₁ hv₂ α' β' hα' hβ' hv₁' hv₂',
    modulePullback_mapIso_mapIso B S hS q β β' hβ' (ε j),
    modulePullback_mapIso_pullbackComparison B S hS q β (w j) y hy β' hβ' y' hyy hy' N]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.self_symm_id_assoc]

variable (hcan : ∀ i j, (modulePullback B S hS (pairFst B S hS W w i j)).mapIso (ε i) ≪≫
    canonicalComparison (pairFst B S hS W w i j) (pairSnd B S hS W w i j) (w i) (w j)
      (pair_condition B S hS W w i j) N =
  baseChangeTransition B S hS W w ρ D i j ≪≫
    (modulePullback B S hS (pairSnd B S hS W w i j)).mapIso (ε j))

include hcan in
/-- **Read at two morphisms with equal composites to `R`, the pairwise isomorphism of `D` is the
canonical comparison of Stacks 04W5 of the two inverse images of `N`, conjugated by `ε`.**  This
is the hypothesis on `ε` — which is an equation on the pairwise fibre products over `R` — carried
to an arbitrary test space, by pulling it back along the induced morphism to such a fibre
product. -/
theorem transitionOn_eq_canonicalComparison {T : AlgebraicSpaces B S hS} (i j : I)
    (α : T ⟶ W i) (β : T ⟶ W j) (hαβ : α ≫ w i = β ≫ w j)
    (v : T ⟶ pair B S hS W (fun t => w t ≫ ρ) i j)
    (hv₁ : v ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j = α)
    (hv₂ : v ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j = β) :
    (modulePullback B S hS α).mapIso (ε i) ≪≫ canonicalComparison α β (w i) (w j) hαβ N =
      transitionOn B S hS W (fun t => w t ≫ ρ) D.F D.transition i j v α β hv₁ hv₂ ≪≫
        (modulePullback B S hS β).mapIso (ε j) := by
  obtain ⟨z, hz₁, hz₂⟩ := exists_pairLeg B S hS W w i j α β hαβ
  have key : (modulePullback B S hS z).mapIso
        ((modulePullback B S hS (pairFst B S hS W w i j)).mapIso (ε i) ≪≫
          canonicalComparison (pairFst B S hS W w i j) (pairSnd B S hS W w i j) (w i) (w j)
            (pair_condition B S hS W w i j) N) =
      (modulePullback B S hS z).mapIso
        (baseChangeTransition B S hS W w ρ D i j ≪≫
          (modulePullback B S hS (pairSnd B S hS W w i j)).mapIso (ε j)) := by
    rw [hcan i j]
  simp only [Functor.mapIso_trans] at key
  rw [modulePullback_mapIso_mapIso B S hS z (pairFst B S hS W w i j) α hz₁ (ε i),
    modulePullback_mapIso_canonicalComparison B S hS z (pairFst B S hS W w i j)
      (pairSnd B S hS W w i j) (w i) (w j) (pair_condition B S hS W w i j) α β hz₁ hz₂ hαβ N,
    baseChangeTransition,
    modulePullback_mapIso_transitionOn B S hS W (fun t => w t ≫ ρ) D.F D.transition z i j
      (pairOver B S hS W w ρ i j) (pairFst B S hS W w i j) (pairSnd B S hS W w i j)
      (pairOver_fst B S hS W w ρ i j) (pairOver_snd B S hS W w ρ i j) α β hz₁ hz₂
      (by rw [Category.assoc, pairOver_fst, hz₁]) (by rw [Category.assoc, pairOver_snd, hz₂]),
    modulePullback_mapIso_mapIso B S hS z (pairSnd B S hS W w i j) β hz₂ (ε j),
    transitionOn_congr_map B S hS W (fun t => w t ≫ ρ) D.F D.transition i j
      (show z ≫ pairOver B S hS W w ρ i j = v from
        (AlgebraicSpaces.isPullback_fiberProduct B S hS (w i ≫ ρ) (w j ≫ ρ)).hom_ext
          (by rw [Category.assoc, pairOver_fst, hz₁, hv₁])
          (by rw [Category.assoc, pairOver_snd, hz₂, hv₂]))
      α β (by rw [Category.assoc, pairOver_fst, hz₁]) (by rw [Category.assoc, pairOver_snd, hz₂])
      hv₁ hv₂] at key
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc] at key
  exact Iso.eq_of_trans_eq_trans _ _ key

include hcan in
/-- **The reading at two morphisms with equal composites to `R` is the identity.** -/
theorem readN_refl {T : AlgebraicSpaces B S hS} (i j : I) (α : T ⟶ W i) (β : T ⟶ W j)
    (x : T ⟶ R) (hx : α ≫ w i = x) (hy : β ≫ w j = x)
    (v : T ⟶ pair B S hS W (fun t => w t ≫ ρ) i j)
    (hv₁ : v ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j = α)
    (hv₂ : v ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j = β) :
    readN B S hS W w ρ D N ε i j α β x x hx hy v hv₁ hv₂ = Iso.refl _ := by
  rw [readN, Iso.subst_trans₂ (transitionOn_eq_canonicalComparison B S hS W w ρ D N ε hcan
    i j α β (hx.trans hy.symm) v hv₁ hv₂).symm]
  simp only [Functor.mapIso_symm, Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [canonicalComparison_eq_pullbackComparison B S hS α β (w i) (w j) (hx.trans hy.symm) x
    hx hy N]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.self_symm_id]

include hcan in
/-- **The reading depends on the two legs only through their composites to `R`.**  Between the
two readings sit the readings at two pairs of legs with equal composites to `R`, which are
identities. -/
theorem readN_legs {T : AlgebraicSpaces B S hS} (i j i' j' : I) (α : T ⟶ W i) (β : T ⟶ W j)
    (α' : T ⟶ W i') (β' : T ⟶ W j') (x y : T ⟶ R) (hx : α ≫ w i = x) (hy : β ≫ w j = y)
    (hx' : α' ≫ w i' = x) (hy' : β' ≫ w j' = y)
    (v : T ⟶ pair B S hS W (fun t => w t ≫ ρ) i j)
    (hv₁ : v ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j = α)
    (hv₂ : v ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j = β)
    (v' : T ⟶ pair B S hS W (fun t => w t ≫ ρ) i' j')
    (hv₁' : v' ≫ pairFst B S hS W (fun t => w t ≫ ρ) i' j' = α')
    (hv₂' : v' ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i' j' = β') :
    readN B S hS W w ρ D N ε i j α β x y hx hy v hv₁ hv₂ =
      readN B S hS W w ρ D N ε i' j' α' β' x y hx' hy' v' hv₁' hv₂' := by
  have hxy : x ≫ ρ = y ≫ ρ := by
    rw [← hx, ← hy, Category.assoc, Category.assoc, ← hv₁, ← hv₂, Category.assoc,
      Category.assoc, pair_condition B S hS W (fun t => w t ≫ ρ) i j]
  obtain ⟨v₁, hv₁₁, hv₁₂⟩ := exists_pairLeg B S hS W (fun t => w t ≫ ρ) i' i α' α
    (by rw [← Category.assoc, ← Category.assoc, hx', hx])
  obtain ⟨v₂, hv₂₁, hv₂₂⟩ := exists_pairLeg B S hS W (fun t => w t ≫ ρ) j j' β β'
    (by rw [← Category.assoc, ← Category.assoc, hy, hy'])
  obtain ⟨v₃, hv₃₁, hv₃₂⟩ := exists_pairLeg B S hS W (fun t => w t ≫ ρ) i' j α' β
    (by rw [← Category.assoc, ← Category.assoc, hx', hy]; exact hxy)
  have step₁ : readN B S hS W w ρ D N ε i' j α' β x y hx' hy v₃ hv₃₁ hv₃₂ =
      readN B S hS W w ρ D N ε i j α β x y hx hy v hv₁ hv₂ := by
    rw [← readN_trans B S hS W w ρ D N ε i' i j α' α β x x y hx' hx hy v₁ hv₁₁ hv₁₂ v hv₁ hv₂
        v₃ hv₃₁ hv₃₂,
      readN_refl B S hS W w ρ D N ε hcan i' i α' α x hx' hx v₁ hv₁₁ hv₁₂, Iso.refl_trans]
  rw [← step₁, ← readN_trans B S hS W w ρ D N ε i' j j' α' β β' x y y hx' hy hy' v₃ hv₃₁ hv₃₂
      v₂ hv₂₁ hv₂₂ v' hv₁' hv₂',
    readN_refl B S hS W w ρ D N ε hcan j j' β β' y hy hy' v₂ hv₂₁ hv₂₂, Iso.trans_refl]

end Reading

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
