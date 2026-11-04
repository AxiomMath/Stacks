module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesFibreExtBaseChange

/-!
# Transport of the relative Hom functor of a pullback pseudofunctor datum

Let `P` be a coherent pullback pseudofunctor datum on a category `A`, and let
`CategoryTheory.PullbackData.relHomFunctor` be its relative Hom functor at a cone `κ` of test
objects over `a₀ : A`, sending a test object `i` to `Hom((κ i)^*M, (κ i)^*N)`.  This file proves
the three invariances of that functor which a reduction "to the case `W = Y`" uses:

* **reindexing**: along a functor `G` between index categories, the relative Hom functor of the
  reindexed cone is the relative Hom functor composed with `G`;
* **postcomposition**: for a cone `κ` over `b` and `r : b ⟶ a₀`, the relative Hom functor of
  `M`, `N` at the cone `κ ≫ r` is the relative Hom functor of `r^*M`, `r^*N` at `κ`;
* **isomorphic diagrams**: two cones over `a₀` whose diagrams are isomorphic compatibly with the
  legs have isomorphic relative Hom functors.

The naturality of the last two is the associativity coherence of `P`.

## Main definitions

* `CategoryTheory.PullbackData.ConeTo.reindex`, `CategoryTheory.PullbackData.ConeTo.postcomp`.
* `CategoryTheory.PullbackData.relHomFunctorReindexIso`,
  `CategoryTheory.PullbackData.relHomPostcompIso`,
  `CategoryTheory.PullbackData.relHomIsoOfIso`: the three isomorphisms.

## Main results

* `CategoryTheory.PullbackData.conjHom_triangle_comp`: conjugating along two comparison
  triangles is conjugating along the comparison of the composite.
-/

@[expose] public noncomputable section

namespace CategoryTheory

namespace PullbackData

universe v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
    (P : PullbackData A D)

/-- **Conjugation along two comparison triangles** is conjugation along the comparison of the
composite: for `f ≫ g = k`, `g ≫ p = q`, `f ≫ q = r` and `k ≫ p = r`, conjugating a morphism of
inverse images along `p` first by the comparison for `q` and then by the one for `r` is
conjugating it by the comparison `p^* ⋙ k^*` for `r`.  This is the associativity coherence. -/
theorem conjHom_triangle_comp (hP : P.IsCoherent) {a b c d : A} {f : a ⟶ b} {g : b ⟶ c}
    {p : c ⟶ d} {k : a ⟶ c} {q : b ⟶ d} {r : a ⟶ d}
    (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r) (hkr : k ≫ p = r) {M N : D d}
    (α : (P.pull p).obj M ⟶ (P.pull p).obj N) :
    Functor.conjHom (P.triangle hr) (Functor.conjHom (P.triangle hq) α) =
      Functor.conjHom (P.triangle hkr) α :=
  (Functor.conjHom_comp (P.triangle hq) (P.triangle hr) (P.triangle hkr) (P.triangle hk)
    (hP.triangle_comp' hk hq hr hkr) α).symm

variable {I : Type*} [Category* I] {π : I ⥤ A} {a₀ : A}

/-- The cone reindexed along a functor `G : J ⥤ I` of index categories. -/
def ConeTo.reindex {J : Type*} [Category* J] (G : J ⥤ I) (κ : ConeTo π a₀) :
    ConeTo (G ⋙ π) a₀ where
  leg j := κ.leg (G.obj j)
  w g := κ.w (G.map g)

/-- **Reindexing**: the relative Hom functor of a reindexed cone is the relative Hom functor
composed with the reindexing functor. -/
def relHomFunctorReindexIso (hP : P.IsCoherent) {J : Type*} [Category* J] (G : J ⥤ I)
    (κ : ConeTo π a₀) (M N : D a₀) :
    G.op ⋙ P.relHomFunctor hP κ M N ≅ P.relHomFunctor hP (κ.reindex G) M N :=
  Iso.refl _

/-- The cone `κ ≫ r`: the legs of a cone over `b` followed by `r : b ⟶ a₀`. -/
def ConeTo.postcomp {b : A} (κ : ConeTo π b) (r : b ⟶ a₀) : ConeTo π a₀ where
  leg i := κ.leg i ≫ r
  w g := by rw [← Category.assoc, κ.w g]


/-- The comparison of the relative Hom functors at a cone and at its postcomposition is natural:
the associativity coherence for `π g ≫ κ i ≫ r`. -/
theorem transportHom_conjHom_postcomp (hP : P.IsCoherent) {b : A} (κ : ConeTo π b)
    (r : b ⟶ a₀) {M N : D a₀} {j i : I} (g : j ⟶ i)
    (β : (P.pull (κ.leg i)).obj ((P.pull r).obj M) ⟶ (P.pull (κ.leg i)).obj ((P.pull r).obj N)) :
    Functor.transportHom (P.triangle (rfl : κ.leg j ≫ r = (κ.postcomp r).leg j))
        (Functor.conjHom (P.triangle (κ.w g)) β) =
      Functor.conjHom (P.triangle ((κ.postcomp r).w g))
        (Functor.transportHom (P.triangle (rfl : κ.leg i ≫ r = (κ.postcomp r).leg i)) β) := by
  rw [← Functor.conjHom_isoWhiskerLeft (P.pull r) (P.triangle (κ.w g)) β]
  refine Functor.transportHom_conjHom
    (Functor.isoWhiskerLeft (P.pull r) (P.triangle (κ.w g)) ≪≫ (Functor.associator _ _ _).symm)
    (P.triangle ((κ.postcomp r).w g)) (P.triangle (rfl : κ.leg i ≫ r = (κ.postcomp r).leg i))
    (P.triangle (rfl : κ.leg j ≫ r = (κ.postcomp r).leg j)) ?_ β
  have h := hP.triangle_comp (κ.w g) (rfl : κ.leg i ≫ r = _) ((κ.postcomp r).w g)
    (rfl : κ.leg j ≫ r = _)
  rw [← Iso.trans_assoc, h]
  ext
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id]
  rfl

/-- **Postcomposition**: the relative Hom functor of `r^*M`, `r^*N` at a cone `κ` over `b` is the
relative Hom functor of `M`, `N` at the cone `κ ≫ r`, through the comparisons
`(κ i ≫ r)^* ≅ r^* ⋙ (κ i)^*`. -/
def relHomPostcompIso (hP : P.IsCoherent) {b : A} (κ : ConeTo π b) (r : b ⟶ a₀) (M N : D a₀) :
    P.relHomFunctor hP κ ((P.pull r).obj M) ((P.pull r).obj N) ≅
      P.relHomFunctor hP (κ.postcomp r) M N :=
  NatIso.ofComponents
    (fun i => (Functor.transportHomEquiv
      (P.triangle (rfl : κ.leg i.unop ≫ r = (κ.postcomp r).leg i.unop)) M N).toIso)
    (fun {i j} g => by
      ext β
      exact P.transportHom_conjHom_postcomp hP κ r g.unop β)


/-- The comparison of the relative Hom functors at two cones with isomorphic diagrams is natural:
the associativity coherence for the two factorizations of `π₁ g ≫ φ i ≫ κ₂ i`. -/
theorem conjHom_conjHom_of_iso (hP : P.IsCoherent) {π₁ π₂ : I ⥤ A} (κ₁ : ConeTo π₁ a₀)
    (κ₂ : ConeTo π₂ a₀) (φ : π₁ ≅ π₂) (hφ : ∀ i, φ.hom.app i ≫ κ₂.leg i = κ₁.leg i)
    {M N : D a₀} {j i : I} (g : j ⟶ i)
    (β : (P.pull (κ₂.leg i)).obj M ⟶ (P.pull (κ₂.leg i)).obj N) :
    Functor.conjHom (P.triangle (hφ j)) (Functor.conjHom (P.triangle (κ₂.w g)) β) =
      Functor.conjHom (P.triangle (κ₁.w g)) (Functor.conjHom (P.triangle (hφ i)) β) := by
  have hnat : φ.hom.app j ≫ π₂.map g = π₁.map g ≫ φ.hom.app i := (φ.hom.naturality g).symm
  have hkr : (π₁.map g ≫ φ.hom.app i) ≫ κ₂.leg i = κ₁.leg j := by
    rw [Category.assoc, hφ, κ₁.w]
  rw [P.conjHom_triangle_comp hP hnat (κ₂.w g) (hφ j) hkr,
    P.conjHom_triangle_comp hP rfl (hφ i) (κ₁.w g) hkr]

/-- **Isomorphic diagrams**: if the diagrams of two cones over `a₀` are isomorphic by `φ`,
compatibly with the legs, the two relative Hom functors are isomorphic, through conjugation by
the comparisons `(κ₁ i)^* ≅ (κ₂ i)^* ⋙ (φ i)^*`, which are bijective because the inverse image
along an isomorphism is an equivalence. -/
def relHomIsoOfIso (hP : P.IsCoherent) {π₁ π₂ : I ⥤ A} (κ₁ : ConeTo π₁ a₀) (κ₂ : ConeTo π₂ a₀)
    (φ : π₁ ≅ π₂) (hφ : ∀ i, φ.hom.app i ≫ κ₂.leg i = κ₁.leg i) (M N : D a₀) :
    P.relHomFunctor hP κ₂ M N ≅ P.relHomFunctor hP κ₁ M N :=
  NatIso.ofComponents
    (fun i => Equiv.toIso
      (((P.pullEquivalence (φ.app i.unop)).fullyFaithfulFunctor.homEquiv).trans
        (Iso.homCongr ((P.triangle (hφ i.unop)).app M).symm
          ((P.triangle (hφ i.unop)).app N).symm)))
    (fun {i j} g => by
      ext β
      exact P.conjHom_conjHom_of_iso hP κ₁ κ₂ φ hφ g.unop β)

end PullbackData

end CategoryTheory

end
