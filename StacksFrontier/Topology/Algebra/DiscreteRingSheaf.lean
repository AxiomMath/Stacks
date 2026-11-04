module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Category.TopCommRingCat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Discrete topological rings and sheaves of them

A commutative ring with the discrete topology is a topological ring, and a ring homomorphism is
continuous for the discrete topologies, so a commutative ring determines a discrete topological
ring functorially. This file records that functor — with a universe lift built in, as the
inverse limits that sheaves of topological rings on formal algebraic spaces take live one
universe up — and proves the one statement about sheaves that is needed: on a site in which
every covering sieve contains a finite covering family, a sheaf of rings becomes a sheaf of
topological rings once its values are given the discrete topology.

The finiteness is necessary: for an infinite covering family the product topology on the
sections over the members is not discrete, so the equalizer it induces on the sections over the
covered object is not the discrete topology.

## Main definitions

* `TopCommRingCat.DiscreteULift`: the universe lift of a commutative ring, with the discrete
  topology.
* `TopCommRingCat.discreteULiftFunctor`: the functor `CommRingCat ⥤ TopCommRingCat` it defines.

## Main results

* `TopCommRingCat.isSheaf_comp_discreteULiftFunctor`: a sheaf of commutative rings on a site
  whose covering sieves contain finite covering families is a sheaf of topological rings for the
  discrete topologies.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u u' w'

namespace TopCommRingCat

/-- The universe lift of a commutative ring, to be given the discrete topology. -/
def DiscreteULift (R : Type u) : Type max u w := ULift.{w} R

instance (R : Type u) [CommRing R] : CommRing (DiscreteULift.{w} R) :=
  inferInstanceAs (CommRing (ULift.{w} R))

instance (R : Type u) : TopologicalSpace (DiscreteULift.{w} R) := ⊥

instance (R : Type u) : DiscreteTopology (DiscreteULift.{w} R) := ⟨rfl⟩

instance (R : Type u) [CommRing R] : IsTopologicalRing (DiscreteULift.{w} R) where
  continuous_add := continuous_of_discreteTopology
  continuous_mul := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

/-- The element of the discrete lift of a ring corresponding to an element of the ring. -/
def DiscreteULift.up {R : Type u} (x : R) : DiscreteULift.{w} R := ULift.up x

/-- The element of a ring corresponding to an element of its discrete lift. -/
def DiscreteULift.down {R : Type u} (x : DiscreteULift.{w} R) : R := ULift.down x

@[simp]
theorem DiscreteULift.down_up {R : Type u} (x : R) : (DiscreteULift.up.{w} x).down = x := rfl

@[simp]
theorem DiscreteULift.up_down {R : Type u} (x : DiscreteULift.{w} R) :
    DiscreteULift.up x.down = x := rfl

theorem DiscreteULift.down_injective {R : Type u} :
    Function.Injective (DiscreteULift.down : DiscreteULift.{w} R → R) :=
  ULift.down_injective

/-- The ring isomorphism between the discrete lift of a ring and the ring. -/
def DiscreteULift.ringEquiv (R : Type u) [CommRing R] : DiscreteULift.{w} R ≃+* R :=
  ULift.ringEquiv

@[simp]
theorem DiscreteULift.ringEquiv_apply {R : Type u} [CommRing R] (x : DiscreteULift.{w} R) :
    DiscreteULift.ringEquiv R x = x.down := rfl

/-- A ring homomorphism, lifted to the discrete lifts. -/
def DiscreteULift.map {R R' : Type u} [CommRing R] [CommRing R'] (f : R →+* R') :
    DiscreteULift.{w} R →+* DiscreteULift.{w} R' :=
  (DiscreteULift.ringEquiv R').symm.toRingHom.comp (f.comp (DiscreteULift.ringEquiv R).toRingHom)

@[simp]
theorem DiscreteULift.map_down {R R' : Type u} [CommRing R] [CommRing R'] (f : R →+* R')
    (x : DiscreteULift.{w} R) : (DiscreteULift.map f x).down = f x.down := rfl

/-- **The discrete topological ring on the universe lift of a commutative ring**, as a functor. -/
def discreteULiftFunctor : CommRingCat.{u} ⥤ TopCommRingCat.{max u w} where
  obj R := TopCommRingCat.of (DiscreteULift.{w} R)
  map f := ⟨DiscreteULift.map f.hom, continuous_of_discreteTopology⟩
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem discreteULiftFunctor_map_apply_down {R R' : CommRingCat.{u}} (f : R ⟶ R')
    (x : DiscreteULift.{w} R) :
    (DiscreteULift.down ((discreteULiftFunctor.{w}.map f).1 x) : R') = f x.down := rfl

/-- **A sheaf of rings is a sheaf of discrete topological rings on a site with finite
coverings.** Let `J` be a Grothendieck topology on `C` in which every covering sieve contains the
arrows of a finite family that generates a covering sieve, and let `P` be a presheaf of
commutative rings whose underlying presheaf of sets is a sheaf. Then `P`, with the discrete
topology on its values, is a sheaf of topological rings.

A compatible family of continuous homomorphisms `E ⟶ P(Y)` glues pointwise, by the sheaf
condition on sets, to a homomorphism `E ⟶ P(X)`; it is continuous for the discrete topology
because the preimage of a section is the finite intersection of the preimages of its
restrictions to the members of a finite covering family, by the separation of `P`. -/
@[ega "0 3.8.1" "partial"]
theorem isSheaf_comp_discreteULiftFunctor {C : Type u'} [Category.{v} C]
    (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ CommRingCat.{u})
    (hP : Presieve.IsSheaf J (P ⋙ CategoryTheory.forget CommRingCat.{u}))
    (hfin : ∀ (X : C) (S : Sieve X), S ∈ J X →
      ∃ (ι : Type w') (_ : Finite ι) (Y : ι → C) (f : ∀ i, Y i ⟶ X),
        (∀ i, S (f i)) ∧ Sieve.ofArrows Y f ∈ J X) :
    Presheaf.IsSheaf J (P ⋙ discreteULiftFunctor.{w}) := by
  intro E X S hS x hx
  -- the pointwise families of sections
  let xe : E → Presieve.FamilyOfElements (P ⋙ CategoryTheory.forget CommRingCat.{u}) S.arrows :=
    fun e Y g hg ↦ ((x g hg).1 e).down
  have hxe : ∀ e, (xe e).Compatible := by
    intro e Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    have := congrArg (fun φ : E ⟶ (P ⋙ discreteULiftFunctor.{w}).obj (op Z) ↦ (φ.1 e).down)
      (hx g₁ g₂ h₁ h₂ w)
    exact this
  choose t ht htu using fun e ↦ hP S hS (xe e) (hxe e)
  -- the amalgamation is a ring homomorphism, by uniqueness of amalgamations
  have hres : ∀ {Y : C} (g : Y ⟶ X) (hg : S g) (e : E), P.map g.op (t e) = (xe e) g hg :=
    fun g hg e ↦ ht e g hg
  have uniq : ∀ (e : E) (s : P.obj (op X)),
      (∀ {Y : C} (g : Y ⟶ X) (hg : S g), ((x g hg).1 e).down = P.map g.op s) → t e = s :=
    fun e s h ↦ (hP S hS).isSeparatedFor.ext fun Y g hg ↦ (hres g hg e).trans (h g hg)
  let φ : E →+* DiscreteULift.{w} (P.obj (op X)) :=
    { toFun := fun e ↦ DiscreteULift.up (t e)
      map_one' := DiscreteULift.down_injective <| uniq _ _ fun g hg ↦ by
        change ((x g hg).1 1).down = P.map g.op 1
        rw [map_one, map_one]; rfl
      map_mul' := fun e e' ↦ DiscreteULift.down_injective <| uniq _ _ fun g hg ↦ by
        change ((x g hg).1 (e * e')).down = P.map g.op (t e * t e')
        rw [map_mul, map_mul, hres g hg, hres g hg]; rfl
      map_zero' := DiscreteULift.down_injective <| uniq _ _ fun g hg ↦ by
        change ((x g hg).1 0).down = P.map g.op 0
        rw [map_zero, map_zero]; rfl
      map_add' := fun e e' ↦ DiscreteULift.down_injective <| uniq _ _ fun g hg ↦ by
        change ((x g hg).1 (e + e')).down = P.map g.op (t e + t e')
        rw [map_add, map_add, hres g hg, hres g hg]; rfl }
  -- continuity: the preimage of a section is cut out by finitely many restrictions
  obtain ⟨ι, hι, Y, f, hfS, hfcov⟩ := hfin X S hS
  have hcont : Continuous φ := by
    rw [continuous_discrete_rng]
    intro s
    have hset : φ ⁻¹' {s} =
        ⋂ i, (fun e ↦ (x (f i) (hfS i)).1 e) ⁻¹'
          {DiscreteULift.up (P.map (f i).op s.down)} := by
      ext e
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
      constructor
      · rintro h i
        apply DiscreteULift.down_injective
        show ((x (f i) (hfS i)).1 e).down = P.map (f i).op s.down
        rw [← h]
        exact (hres (f i) (hfS i) e).symm
      · intro h
        apply DiscreteULift.down_injective
        show t e = s.down
        refine (hP _ hfcov).isSeparatedFor.ext fun Z g hg ↦ ?_
        obtain ⟨W, a, b, ⟨i⟩, rfl⟩ := hg
        show P.map (a ≫ f i).op (t e) = P.map (a ≫ f i).op s.down
        rw [op_comp, P.map_comp]
        show (P.map a.op) (P.map (f i).op (t e)) = (P.map a.op) (P.map (f i).op s.down)
        rw [hres (f i) (hfS i) e]
        congr 1
        exact congrArg DiscreteULift.down (h i)
    rw [hset]
    exact isOpen_iInter_of_finite fun i ↦
      (isOpen_discrete (α := DiscreteULift.{w} (P.obj (op (Y i)))) _).preimage (x (f i) (hfS i)).2
  refine ⟨⟨φ, hcont⟩, ?_, ?_⟩
  · intro Y g hg
    apply Subtype.ext
    apply RingHom.ext
    intro e
    apply DiscreteULift.down_injective
    exact hres g hg e
  · intro y hy
    apply Subtype.ext
    apply RingHom.ext
    intro e
    apply DiscreteULift.down_injective
    refine (uniq e _ fun g hg ↦ ?_).symm
    have h1 := congrArg (fun ψ : E ⟶ (P ⋙ discreteULiftFunctor.{w}).obj _ ↦ (ψ.1 e).down)
      (hy g hg)
    exact h1.symm

end TopCommRingCat

end
