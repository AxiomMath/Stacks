module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Small.Set

/-!
# A limit cone bounds the compatible families, and a finite-transition system with none

A cone over a diagram of schemes with vertex `Z` is the same thing as a compatible family of
morphisms out of `Z`, and the hom-sets of `Scheme.{u}` live in `Type u`. So a diagram with a
limit cone has, for every `Z`, only a `u`-small type of compatible families out of `Z`, whatever
the universe of its index category. That is `small_natTrans_of_isLimit`.

## The system

Index by the finite sets of types, `Finset (Type u)`, a nonempty directed preorder in
`Type (u+1)`. The stage at `T` is the spectrum of the ring of `ZMod 2`-valued functions on the
subsets of `T`, a finite ring, copied into `Type u` by `Shrink`; the transition along `T ⊆ T'`
is precomposition with the restriction `Set ↑T' → Set ↑T`. Every transition is finite, because
every stage ring is a finite type, and every stage is a nonempty affine scheme. Each family
`V : Set (Type u)` gives a compatible family of `ZMod 2`-points, namely evaluation at the trace
`V ∩ T`, and distinct families are distinct already at a singleton stage. So the compatible
families out of `Spec (ZMod 2)` are at least as many as the subsets of `Type u`, which is not a
`u`-small type — and therefore no cone over this system is a limit cone.

## Main results

* `small_natTrans_of_isLimit`: a limit cone bounds the compatible families out of any fixed
  scheme. Stated for an arbitrary index category, at a universe independent of the schemes.
* `boolDiagram`: the system, with `isFinite_boolDiagram_map` and `isAffine_boolDiagram_obj`.
* `coneFamily`, `coneFamily_injective`: the large family of compatible families.
* `not_small_natTrans`, `not_nonempty_isLimit`: the system has no limit cone.
* `boolDiagram_hypotheses`: every hypothesis Tag 09ZN imposes on its system, checked by instance
  synthesis, together with the nonexistence of the limit cone.

## References

* [The Stacks Project, Tag 09ZN](https://stacks.math.columbia.edu/tag/09ZN)
* [The Stacks Project, Tag 09ZM](https://stacks.math.columbia.edu/tag/09ZM)
* [The Stacks Project, Tag 081D](https://stacks.math.columbia.edu/tag/081D)
-/


@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w w' u

namespace Stacks.LimitConeBound

/-- The morphism to the vertex of a limit cone induced by a compatible family. -/
def liftOf {J : Type w} [Category.{w'} J] {F : J ⥤ Scheme.{u}} {c : Cone F} (hc : IsLimit c)
    (Z : Scheme.{u}) (t : (Functor.const J).obj Z ⟶ F) : Z ⟶ c.pt :=
  hc.lift ⟨Z, t⟩

/-- If `c` is a limit cone over `F`, then for every scheme `Z` the compatible families out of `Z`
form a `u`-small type. -/
theorem small_natTrans_of_isLimit {J : Type w} [Category.{w'} J] {F : J ⥤ Scheme.{u}}
    {c : Cone F} (hc : IsLimit c) (Z : Scheme.{u}) :
    Small.{u} ((Functor.const J).obj Z ⟶ F) := by
  refine small_of_injective (f := liftOf hc Z) ?_
  intro t₁ t₂ hteq
  ext j
  rw [← hc.fac ⟨Z, t₁⟩ j, ← hc.fac ⟨Z, t₂⟩ j]
  exact congrArg (fun m => m ≫ c.π.app j) hteq

/-- The subsets of a stage `T`: a finite set, because `T` is a finite set. -/
abbrev stageSet (T : Finset (Type u)) : Type (u + 1) := Set {x // x ∈ T}

/-- The stage ring: the `ZMod 2`-valued functions on `stageSet T`, copied into `Type u`. -/
abbrev stageRing (T : Finset (Type u)) : Type u := Shrink.{u} (stageSet.{u} T → ZMod 2)

/-- The chosen isomorphism of the stage ring with the function ring it copies. -/
abbrev stageRingEquiv (T : Finset (Type u)) :
    stageRing.{u} T ≃+* (stageSet.{u} T → ZMod 2) :=
  Shrink.ringEquiv _

/-- Restriction of a subset of a later stage to an earlier one. -/
def restrict {T T' : Finset (Type u)} (h : T ≤ T') :
    stageSet.{u} T' → stageSet.{u} T :=
  fun U => (fun x : {x // x ∈ T} => (⟨x.1, h x.2⟩ : {x // x ∈ T'})) ⁻¹' U

/-- Precomposition with a map of index sets, as a ring homomorphism of function rings. -/
def precomp {A B : Type (u + 1)} (r : A → B) : (B → ZMod 2) →+* (A → ZMod 2) where
  toFun f := f ∘ r
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The transition homomorphism of stage rings along an inclusion of stages. -/
def stageHom {T T' : Finset (Type u)} (h : T ≤ T') : stageRing.{u} T →+* stageRing.{u} T' :=
  ((stageRingEquiv T').symm.toRingHom).comp
    ((precomp (restrict h)).comp (stageRingEquiv T).toRingHom)

/-- Under `stageRingEquiv`, `stageHom h a` is the function `U ↦ a (restrict h U)`. -/
@[simp] theorem stageRingEquiv_stageHom {T T' : Finset (Type u)} (h : T ≤ T')
    (a : stageRing.{u} T) (U : stageSet.{u} T') :
    stageRingEquiv T' (stageHom h a) U = stageRingEquiv T a (restrict h U) := by
  simp [stageHom, precomp, Function.comp_def]

/-- Restriction along `T ≤ T` is the identity. -/
theorem restrict_refl {T : Finset (Type u)} (U : stageSet.{u} T) : restrict le_rfl U = U := rfl

/-- Restriction along a composite inclusion is the composite of the restrictions. -/
theorem restrict_trans {T₁ T₂ T₃ : Finset (Type u)} (h₁ : T₁ ≤ T₂) (h₂ : T₂ ≤ T₃)
    (U : stageSet.{u} T₃) : restrict (h₁.trans h₂) U = restrict h₁ (restrict h₂ U) := rfl

/-- The transition homomorphism along `T ≤ T` is the identity. -/
theorem stageHom_refl {T : Finset (Type u)} (a : stageRing.{u} T) : stageHom le_rfl a = a := by
  refine (stageRingEquiv T).injective (funext fun U => ?_)
  rw [stageRingEquiv_stageHom, restrict_refl]

/-- The transition homomorphism along a composite inclusion is the composite of the transition
homomorphisms. -/
theorem stageHom_trans {T₁ T₂ T₃ : Finset (Type u)} (h₁ : T₁ ≤ T₂) (h₂ : T₂ ≤ T₃)
    (a : stageRing.{u} T₁) :
    stageHom (h₁.trans h₂) a = stageHom h₂ (stageHom h₁ a) := by
  refine (stageRingEquiv T₃).injective (funext fun U => ?_)
  rw [stageRingEquiv_stageHom, stageRingEquiv_stageHom, stageRingEquiv_stageHom, restrict_trans]

/-- The transition morphism in `CommRingCat` along `T ≤ T` is the identity. -/
theorem ofHom_stageHom_id (T : Finset (Type u)) :
    CommRingCat.ofHom (stageHom (le_refl T)) = 𝟙 (CommRingCat.of (stageRing.{u} T)) :=
  CommRingCat.hom_ext (RingHom.ext fun a => stageHom_refl a)

/-- The transition morphisms in `CommRingCat` compose along a composite inclusion. -/
theorem ofHom_stageHom_comp {T₁ T₂ T₃ : Finset (Type u)} (h₁ : T₁ ≤ T₂) (h₂ : T₂ ≤ T₃) :
    CommRingCat.ofHom (stageHom (h₁.trans h₂)) =
      CommRingCat.ofHom (stageHom h₁) ≫ CommRingCat.ofHom (stageHom h₂) :=
  CommRingCat.hom_ext (RingHom.ext fun a => stageHom_trans h₁ h₂ a)

/-- The directed system of finite affine schemes, indexed by the finite sets of `Type u`. -/
def boolDiagram : (Finset (Type u))ᵒᵖ ⥤ Scheme.{u} where
  obj T := Spec (CommRingCat.of (stageRing.{u} T.unop))
  map {T T'} f := Spec.map (CommRingCat.ofHom (stageHom (leOfHom f.unop)))
  map_id T := by rw [ofHom_stageHom_id, Spec.map_id]
  map_comp f g := by rw [← Spec.map_comp, ← ofHom_stageHom_comp]

/-- Each stage ring is a finite type. -/
instance finite_stageRing (T : Finset (Type u)) : Finite (stageRing.{u} T) :=
  Finite.of_equiv _ (stageRingEquiv.{u} T).toEquiv.symm

/-- A morphism of affine schemes whose source ring is finite is a finite morphism. -/
theorem isFinite_specMap {R S : Type u} [CommRing R] [CommRing S] [Finite S] (φ : R →+* S) :
    IsFinite (Spec.map (CommRingCat.ofHom φ)) :=
  (IsFinite.SpecMap_iff _).mpr (let : Algebra R S := φ.toAlgebra; Module.Finite.of_finite)

/-- Every transition morphism of `boolDiagram` is finite. -/
instance isFinite_boolDiagram_map {i j : (Finset (Type u))ᵒᵖ} (g : i ⟶ j) :
    IsFinite (boolDiagram.{u}.map g) :=
  isFinite_specMap _

/-- Every transition morphism of `boolDiagram` is affine. -/
instance isAffineHom_boolDiagram_map {i j : (Finset (Type u))ᵒᵖ} (g : i ⟶ j) :
    IsAffineHom (boolDiagram.{u}.map g) :=
  inferInstanceAs (IsAffineHom (Spec.map _))

/-- Each stage ring is nontrivial. -/
instance nontrivial_stageRing (T : Finset (Type u)) : Nontrivial (stageRing.{u} T) :=
  inferInstanceAs (Nontrivial (Shrink.{u} (stageSet.{u} T → ZMod 2)))

/-- Every stage of `boolDiagram` is a nonempty scheme. -/
instance nonempty_boolDiagram_obj (T : (Finset (Type u))ᵒᵖ) :
    Nonempty (boolDiagram.{u}.obj T) :=
  inferInstanceAs (Nonempty (PrimeSpectrum (stageRing.{u} T.unop)))

/-- Every stage of `boolDiagram` is an affine scheme. -/
instance isAffine_boolDiagram_obj (T : (Finset (Type u))ᵒᵖ) :
    IsAffine (boolDiagram.{u}.obj T) :=
  inferInstanceAs (IsAffine (Spec _))

/-- The vertex of the cones below: the spectrum of `ZMod 2`, copied into `Type u`. -/
abbrev vertexRing : Type u := ULift.{u} (ZMod 2)

/-- The spectrum of `ZMod 2`. -/
abbrev vertex : Scheme.{u} := Spec (CommRingCat.of vertexRing.{u})

/-- The structure homomorphism of a stage ring: the constant functions. -/
def structHom (T : Finset (Type u)) : vertexRing.{u} →+* stageRing.{u} T :=
  ((stageRingEquiv T).symm.toRingHom).comp
    ((Pi.constRingHom _ _).comp ULift.ringEquiv.toRingHom)

/-- Under `stageRingEquiv`, `structHom T z` is the constant function with value `z`. -/
@[simp] theorem stageRingEquiv_structHom (T : Finset (Type u)) (z : vertexRing.{u})
    (U : stageSet.{u} T) : stageRingEquiv T (structHom T z) U = ULift.ringEquiv z :=
  congrFun (RingEquiv.apply_symm_apply (stageRingEquiv T) _) U

/-- The transition homomorphisms commute with the structure homomorphisms. -/
theorem stageHom_comp_structHom {T T' : Finset (Type u)} (h : T ≤ T') :
    (stageHom h).comp (structHom T) = structHom T' := by
  refine RingHom.ext fun z => (stageRingEquiv T').injective (funext fun U => ?_)
  show stageRingEquiv T' (stageHom h (structHom T z)) U = stageRingEquiv T' (structHom T' z) U
  rw [stageRingEquiv_stageHom, stageRingEquiv_structHom, stageRingEquiv_structHom]

/-- The structure morphisms of the system, over the spectrum of `ZMod 2`. -/
def structMap : boolDiagram.{u} ⟶ (Functor.const (Finset (Type u))ᵒᵖ).obj vertex.{u} where
  app T := Spec.map (CommRingCat.ofHom (structHom T.unop))
  naturality := by
    intro T T' g
    have h : CommRingCat.ofHom (structHom T'.unop) ≫
        CommRingCat.ofHom (stageHom (leOfHom g.unop)) =
        CommRingCat.ofHom (structHom T.unop) := by
      rw [← CommRingCat.ofHom_comp, stageHom_comp_structHom]
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
      boolDiagram, ← Spec.map_comp, h]

/-- Every structure morphism `structMap.app T` is finite. -/
instance isFinite_structMap (T : (Finset (Type u))ᵒᵖ) : IsFinite (structMap.{u}.app T) :=
  isFinite_specMap _

/-- The trace of a family of types on a stage. -/
def trace (V : Set (Type u)) (T : Finset (Type u)) : stageSet.{u} T := Subtype.val ⁻¹' V

/-- Restricting the trace of `V` on `T'` to `T` gives the trace of `V` on `T`. -/
theorem restrict_trace {T T' : Finset (Type u)} (h : T ≤ T') (V : Set (Type u)) :
    restrict h (trace V T') = trace V T := rfl

/-- The `ZMod 2`-point of the stage `T` given by evaluation at the trace of `V`. -/
def evalHom (V : Set (Type u)) (T : Finset (Type u)) :
    stageRing.{u} T →+* vertexRing.{u} :=
  (ULift.ringEquiv.symm.toRingHom).comp
    ((Pi.evalRingHom _ (trace V T)).comp (stageRingEquiv T).toRingHom)

/-- `evalHom V T a` is the value of `a` at the trace of `V` on `T`. -/
@[simp] theorem evalHom_apply (V : Set (Type u)) (T : Finset (Type u)) (a : stageRing.{u} T) :
    evalHom V T a = ULift.up (stageRingEquiv T a (trace V T)) := rfl

/-- The evaluation homomorphisms are compatible with the transition homomorphisms. -/
theorem evalHom_comp_stageHom (V : Set (Type u)) {T T' : Finset (Type u)} (h : T ≤ T') :
    (evalHom V T').comp (stageHom h) = evalHom V T := by
  ext a
  simp [restrict_trace]

/-- The compatible family of `ZMod 2`-points cut out by a family of types. -/
def coneOf (V : Set (Type u)) : Cone boolDiagram.{u} where
  pt := vertex.{u}
  π :=
    { app := fun T => Spec.map (CommRingCat.ofHom (evalHom V T.unop))
      naturality := by
        intro T T' g
        have : CommRingCat.ofHom (stageHom (leOfHom g.unop)) ≫
            CommRingCat.ofHom (evalHom V T.unop) =
            CommRingCat.ofHom (evalHom V T'.unop) := by
          rw [← CommRingCat.ofHom_comp, evalHom_comp_stageHom]
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
          boolDiagram, ← Spec.map_comp, this] }

/-- The compatible family, typed as a natural transformation out of the constant diagram. -/
def coneFamily (V : Set (Type u)) :
    (Functor.const (Finset (Type u))ᵒᵖ).obj vertex.{u} ⟶ boolDiagram.{u} :=
  (coneOf V).π

/-- Distinct families of types give distinct compatible families. -/
theorem coneFamily_injective : Function.Injective coneFamily.{u} := by
  intro V W hVW
  have key : ∀ T : Finset (Type u), evalHom V T = evalHom W T := by
    intro T
    have h := congrArg (fun t : (Functor.const _).obj vertex.{u} ⟶ boolDiagram.{u} =>
      t.app (op T)) hVW
    simp only [coneFamily, coneOf] at h
    have h' : CommRingCat.ofHom (evalHom V T) = CommRingCat.ofHom (evalHom W T) :=
      Spec.map_inj.mp h
    exact congrArg CommRingCat.Hom.hom h'
  have htrace : ∀ T : Finset (Type u), trace V T = trace W T := by
    intro T
    classical
    by_contra hne
    have h := congrArg
      (fun φ : stageRing.{u} T →+* vertexRing.{u} =>
        φ ((stageRingEquiv T).symm (fun U => if U = trace V T then 1 else 0))) (key T)
    have hne' : trace W T ≠ trace V T := fun e => hne e.symm
    simp only [evalHom_apply, RingEquiv.apply_symm_apply, hne'] at h
    exact one_ne_zero (ULift.up_injective h)
  ext X
  have h := htrace {X}
  have e : ∀ s : Set (Type u),
      ((⟨X, Finset.mem_singleton_self X⟩ : {x // x ∈ ({X} : Finset (Type u))}) ∈
        trace s {X}) ↔ X ∈ s := fun _ => Iff.rfl
  rw [← e V, ← e W, h]

/-- The compatible families of `ZMod 2`-points of `boolDiagram` do not form a `u`-small type. -/
theorem not_small_natTrans :
    ¬ Small.{u} ((Functor.const (Finset (Type u))ᵒᵖ).obj vertex.{u} ⟶ boolDiagram.{u}) := by
  intro _
  have h1 : Small.{u} (Set (Type u)) := small_of_injective coneFamily_injective
  exact not_small_type (small_of_injective (f := fun X : Type u => ({X} : Set (Type u)))
    Set.singleton_injective)

/-- No cone over `boolDiagram` is a limit cone. -/
theorem not_nonempty_isLimit (c : Cone boolDiagram.{u}) : ¬ Nonempty (IsLimit c) :=
  fun h => not_small_natTrans (small_natTrans_of_isLimit h.some vertex.{u})

/-- **Every hypothesis Tag 09ZN imposes on its system holds here, and no limit cone exists.**
The index is a nonempty directed preorder one universe above the schemes; the transition
morphisms are finite, hence affine; every stage is a nonempty quasi-compact and
quasi-separated scheme; the structure morphisms to the base are finite, hence locally of finite
type; and no cone over the system is a limit cone. -/
theorem boolDiagram_hypotheses :
    IsDirected (Finset (Type u)) (· ≤ ·) ∧ Nonempty (Finset (Type u)) ∧
      (∀ (i j : (Finset (Type u))ᵒᵖ) (g : i ⟶ j), IsFinite (boolDiagram.{u}.map g)) ∧
      (∀ (i j : (Finset (Type u))ᵒᵖ) (g : i ⟶ j), IsAffineHom (boolDiagram.{u}.map g)) ∧
      (∀ T : (Finset (Type u))ᵒᵖ, CompactSpace (boolDiagram.{u}.obj T)) ∧
      (∀ T : (Finset (Type u))ᵒᵖ, QuasiSeparatedSpace (boolDiagram.{u}.obj T)) ∧
      (∀ T : (Finset (Type u))ᵒᵖ, Nonempty (boolDiagram.{u}.obj T)) ∧
      (∀ T : (Finset (Type u))ᵒᵖ, LocallyOfFiniteType (structMap.{u}.app T)) ∧
      (∀ c : Cone boolDiagram.{u}, ¬ Nonempty (IsLimit c)) :=
  ⟨inferInstance, inferInstance, fun _ _ _ => inferInstance, fun _ _ _ => inferInstance,
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, not_nonempty_isLimit⟩

end Stacks.LimitConeBound

end
