module

public import Mathlib.RingTheory.Derivation.Basic
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses
public import StacksFrontier.Deformation.TangentSpace.Functor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tangent spaces of predeformation categories

The tangent space of a predeformation category at a point, the
differential of a morphism, and the derivation map to the tangent space.

## Main definitions

* `differential` is the induced map on tangent spaces.
* `tangentSpaceAtPoint` is the tangent space
  of the slice category over a point.
* `sliceBasedFunctorAtPoint` is the induced
  morphism of slice predeformation categories.
* `differentialAtPoint` is its map on tangent spaces.
* `derivationToTangentSpace` is the canonical map from derivations to the
  tangent space of the associated functor.

## Main results

* `derivationToTangentSpace_naturality` states that this map commutes
  with morphisms of predeformation categories.

## Implementation notes

### Differential of a morphism of predeformation categories

The tangent spaces use the direct Artinian presentation of Tag 06IB, with residue field `k`,
not a universe-lifted field. The map is the component of the associated natural transformation
of Tag 07W5 at the augmented dual numbers. Its source and target categories may inhabit
different universes. The predeformation special-fibre condition is unnecessary for this map;
cofiberedness suffices.
The representative and naturality API is supplied by Tag 07W5, since the differential is
an abbreviation for the corresponding component of its associated transformation.

### Tangent space at a point of a cofibered category

The category of objects over `x` is `Over x`, with its structure functor to
`𝒞_Λ`. Its tangent space is the value of the associated isomorphism-class functor
of Tag 07W5 at the dual numbers of Tag 06IB. The rank-one module is `ULift k`,
so the carrier universe of the Artinian algebras remains independent of that of `k`.

### Differential at a point of a cofibered category

The induced functor is `Over.post` applied to the underlying functor. Its source
and target projections commute with it because the original functor is based.
The residue-field point in the target is the image of the given point. The
differential uses the same isomorphism-class natural transformation as the
differential of Tag 06II, evaluated at the universe-polymorphic dual numbers used
by the tangent space at a point. This makes its domain and codomain definitionally
the pointwise tangent spaces.

### The derivation map to the tangent space

The map is characterized by its value for every choice of special-fibre object and
every morphism whose coordinates are `a ↦ a + D(a) ε`. This makes independence of
the choice of special-fibre object part of its specification.

## References

* [Stacks Project, Tag 06II](https://stacks.math.columbia.edu/tag/06II)
* [Stacks Project, Tag 06IK](https://stacks.math.columbia.edu/tag/06IK)
* [Stacks Project, Tag 06SV](https://stacks.math.columbia.edu/tag/06SV)
-/

@[expose] public section

namespace Deformation

/-! ### Differential of a morphism of predeformation categories -/

section
open CategoryTheory
universe u w u₁ v₁ u₂ v₂


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The augmented dual numbers in the Artinian category used by the direct tangent space. -/
@[sga "3 III 4.38" "partial", sga "7 VI 1.3(c)" "special case"]
noncomputable abbrev augmentedDualNumbers : ArtinianLocalAlgCat.{u, w, w} Λ k :=
  (artinianLocalOverToArtinian Λ k).obj
    ⟨dualNumbersOver Λ k,
      squareZeroExtension_mem_artinianLocalOver Λ k (FGModuleCat.of k k)⟩

/-- **Stacks Project, Tag 06II.** The differential is the map on associated
isomorphism-class functors evaluated at the dual numbers. -/
@[stacks 06II]
noncomputable abbrev differential
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p)
    (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖) :
    artinianTangentSpace Λ k (isomorphismClasses 𝓕 h𝓕) →
      artinianTangentSpace Λ k (isomorphismClasses 𝓖 h𝓖) :=
  mapIsomorphismClasses h𝓕 h𝓖 φ (augmentedDualNumbers (Λ := Λ) (k := k))

end

/-! ### Tangent space at a point of a cofibered category -/

section
open CategoryTheory
universe u v w u₁ v₁


/-- The tangent space of a category cofibered over `𝒞_Λ` at a point over `k`:
the tangent space of its slice predeformation category. -/
@[stacks 06IK "tangent_space_at_a_point"]
noncomputable abbrev tangentSpaceAtPoint
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (x : p.Fiber (residueFieldObject.{u, v, w} Λ k)) : Type (max u₁ v₁) :=
  tangentSpaceArtinian Λ k
    (isomorphismClasses
      (BasedCategory.ofFunctor
        (objectsOverFunctor p x.1))
      (isPredeformationCategory_objectsOverFunctor p hp x).cofibered)

end

/-! ### Differential at a point of a cofibered category -/

section
open CategoryTheory


universe u v w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type u₁} [Category.{v₁} F] {G : Type u₂} [Category.{v₂} G]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
variable {q : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

/-- The image of an object over the residue field under a based functor. -/
def imagePoint (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (x : p.Fiber (residueFieldObject.{u, v, w} Λ k)) :
    q.Fiber (residueFieldObject.{u, v, w} Λ k) :=
  ⟨φ.obj x.1, (φ.w_obj x.1).trans x.2⟩

/-- The morphism of slice predeformation categories induced by a based functor:
it sends an arrow `y ⟶ x` to its image arrow `φ(y) ⟶ φ(x)`. -/
@[stacks 06IK "differential_at_point", implicit_reducible]
def sliceBasedFunctorAtPoint
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (x : p.Fiber (residueFieldObject.{u, v, w} Λ k)) :
    BasedFunctor
      (BasedCategory.ofFunctor
        (objectsOverFunctor p x.1))
      (BasedCategory.ofFunctor
        (objectsOverFunctor q (imagePoint φ x).1)) where
  toFunctor := Over.post φ.toFunctor
  w := by
    dsimp only [BasedCategory.ofFunctor, objectsOverFunctor,
      imagePoint, Subtype.coe_mk]
    calc
      _ = Over.forget x.1 ⋙ (φ.toFunctor ⋙ q) := rfl
      _ = Over.forget x.1 ⋙ p :=
        congrArg (fun r : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k =>
          Over.forget x.1 ⋙ r) φ.w

/-- The differential of a morphism of cofibered categories at a point over `k`:
the differential of its induced morphism between slice predeformation categories. -/
@[stacks 06IK "differential_at_point"]
noncomputable abbrev differentialAtPoint
    (hp : IsCofiberedInGroupoids p)
    (hq : IsCofiberedInGroupoids q)
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (x : p.Fiber (residueFieldObject.{u, v, w} Λ k)) :
    tangentSpaceAtPoint p hp x →
      tangentSpaceAtPoint q hq (imagePoint φ x) :=
  mapIsomorphismClasses
    (isPredeformationCategory_objectsOverFunctor p hp x).cofibered
    (isPredeformationCategory_objectsOverFunctor q hq (imagePoint φ x)).cofibered
    (sliceBasedFunctorAtPoint φ x) (artinianDualNumbers Λ k)

end

/-! ### The derivation map to the tangent space -/

section
open CategoryTheory
universe u v w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)

/-- The morphism `k → k[ε]` of `𝒞_Λ` with coordinates `a ↦ a + D(a) ε` attached to a
derivation `D` of the residue field. -/
noncomputable def derivationMorphism (D : Derivation Λ k k) :
    residueFieldObject.{u, v, w} Λ k ⟶
      artinianDualNumbers.{u, w, v} Λ k := by
  let V : FGModuleCat.{max v w} k := FGModuleCat.of k (ULift.{v} k)
  let : Module kᵐᵒᵖ V := Module.compHom V
    { toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by simp [mul_comm]
      map_zero' := rfl
      map_add' := by intros; rfl }
  let : IsCentralScalar k V := by
    refine ⟨fun r x => ?_⟩
    change MulOpposite.op r • x = r • x
    simp
  let target := artinianDualNumbers.{u, w, v} Λ k
  let : CommRing (TrivSqZeroExt k (↑V)) := target.commRing
  let : Semiring (TrivSqZeroExt k (↑V)) :=
    target.commRing.toCommSemiring.toSemiring
  let : Mul (TrivSqZeroExt k (↑V)) :=
    target.commRing.toCommSemiring.toSemiring.toMul
  let : Algebra Λ (TrivSqZeroExt k (↑V)) := target.algebra
  let pair (a : ULift.{v} k) : TrivSqZeroExt k (↑V) :=
    (a.down, ULift.up (D a.down))
  let φ : residueFieldObject.{u, v, w} Λ k →ₐ[Λ]
      artinianDualNumbers.{u, w, v} Λ k :=
    { toFun := pair
      map_one' := by
        dsimp [residueFieldObject, artinianDualNumbers,
          squareZeroExtensionArtinian]
        exact TrivSqZeroExt.ext rfl (congrArg ULift.up D.map_one_eq_zero)
      map_mul' := by
        intro a b
        dsimp [residueFieldObject, artinianDualNumbers,
          squareZeroExtensionArtinian]
        apply TrivSqZeroExt.ext
        · rfl
        · change ULift.up (D (a.down * b.down)) =
            TrivSqZeroExt.snd (pair a * pair b)
          rw [D.leibniz]
          rfl
      map_zero' := by
        dsimp [residueFieldObject, artinianDualNumbers,
          squareZeroExtensionArtinian]
        exact TrivSqZeroExt.ext rfl (congrArg ULift.up D.map_zero)
      map_add' := by
        intro a b
        dsimp [residueFieldObject, artinianDualNumbers,
          squareZeroExtensionArtinian]
        exact TrivSqZeroExt.ext rfl (congrArg ULift.up (D.map_add a.down b.down))
      commutes' := by
        intro r
        dsimp [residueFieldObject, artinianDualNumbers,
          squareZeroExtensionArtinian]
        apply TrivSqZeroExt.ext
        · change (algebraMap Λ k) r =
            (algebraMap Λ (TrivSqZeroExt k (↑V)) r).fst
          rfl
        · change ULift.up (D (algebraMap Λ k r)) =
            (algebraMap Λ (TrivSqZeroExt k (↑V)) r).snd
          rw [D.map_algebraMap]
          rfl }
  refine ⟨φ, ?_, ?_⟩
  · refine ⟨fun a ha => ?_⟩
    let : Field (residueFieldObject.{u, v, w} Λ k) :=
      inferInstanceAs (Field (ULift.{v} k))
    have hres : IsUnit ((artinianDualNumbers.{u, w, v} Λ k).residueEquiv
        (IsLocalRing.residue (artinianDualNumbers.{u, w, v} Λ k) (φ a))) :=
      (ha.map (IsLocalRing.residue _)).map
        (artinianDualNumbers.{u, w, v} Λ k).residueEquiv.toRingHom
    have hfst : IsUnit a.down := by
      have hcoord : (artinianDualNumbers.{u, w, v} Λ k).residueEquiv
          (IsLocalRing.residue _ (φ a)) = a.down := by
        change (artinianDualNumbers.{u, w, v} Λ k).residueEquiv
          (IsLocalRing.residue _ (φ a)) = (φ a).fst
        rw [squareZeroExtensionArtinian_residue Λ k V (show TrivSqZeroExt k (↑V) from φ a)]
      rwa [hcoord] at hres
    exact isUnit_iff_ne_zero.2 fun hzero => isUnit_iff_ne_zero.1 hfst (congrArg ULift.down hzero)
  · intro a
    change (artinianDualNumbers.{u, w, v} Λ k).residueEquiv
        (IsLocalRing.residue _ (φ a)) =
      (residueFieldObject.{u, v, w} Λ k).residueEquiv
        (IsLocalRing.residue _ a)
    unfold artinianDualNumbers
    have htgt := squareZeroExtensionArtinian_residue Λ k V
      (show TrivSqZeroExt k (↑V) from φ a)
    have hsrc :
        (residueFieldObject.{u, v, w} Λ k).residueEquiv
          (IsLocalRing.residue _ a) = a.down := by
      let : CommRing (ULift.{v} k) :=
        (residueFieldObject.{u, v, w} Λ k).commRing
      let : IsLocalRing (ULift.{v} k) :=
        (residueFieldObject.{u, v, w} Λ k).isLocalRing
      let : Field (ULift.{v} k) := inferInstanceAs (Field (ULift.{v} k))
      let : Field (residueFieldObject.{u, v, w} Λ k) :=
        inferInstanceAs (Field (ULift.{v} k))
      let e := (Ideal.quotientEquivAlgOfEq Λ
          (IsLocalRing.maximalIdeal_eq_bot (R := ULift.{v} k))).trans
          ((AlgEquiv.quotientBot Λ (ULift.{v} k)).trans
            (ULift.algEquiv (R := Λ) (A := k)))
      change e (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (ULift.{v} k)) a) = a.down
      simp [e]
    rw [htgt, hsrc]
    rfl

/-- A morphism representing the derivation `D` has coordinates `a ↦ a + D(a) ε`. -/
def IsDerivationMorphism (D : Derivation Λ k k)
    (f : residueFieldObject.{u, v, w} Λ k ⟶
      artinianDualNumbers.{u, w, v} Λ k) : Prop :=
  ∀ a : k, (f.hom (ULift.up a)).fst = a ∧
    (f.hom (ULift.up a)).snd.down = D a

/-- Characterization of the canonical map by pushforward from the special fibre. -/
def IsDerivationToTangentSpace
    (γ : Derivation Λ k k → tangentSpaceArtinian Λ k
      (isomorphismClasses (BasedCategory.ofFunctor p) hp.cofibered)) : Prop :=
  ∀ (D : Derivation Λ k k)
    (x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k))
    (f : residueFieldObject.{u, v, w} Λ k ⟶
      artinianDualNumbers.{u, w, v} Λ k),
    IsDerivationMorphism D f →
      γ D = (isomorphismClasses (BasedCategory.ofFunctor p) hp.cofibered).map f
        (classOf (BasedCategory.ofFunctor p) hp.cofibered x₀)

/-- Any two objects of the special fibre of a predeformation category are isomorphic: the special
fibre is equivalent to a one-object discrete category, so both are carried to the same object
there. -/
public theorem specialFiberObjects_isomorphic
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    (x y : p.Fiber
      (residueFieldObject.{u, v, w} Λ k)) : Nonempty (x ≅ y) := by
  obtain ⟨e⟩ := hp.specialFiber
  exact ⟨(e.unitIso.app x) ≪≫
    e.inverse.mapIso (eqToIso (Subsingleton.elim (e.functor.obj x) (e.functor.obj y))) ≪≫
    (e.unitIso.app y).symm⟩

/-- The morphism attached to a derivation has the coordinates of that derivation. -/
theorem derivationMorphism_isDerivationMorphism (D : Derivation Λ k k) :
    IsDerivationMorphism D (derivationMorphism (Λ := Λ) (k := k) D) :=
  fun _ => ⟨rfl, rfl⟩

private theorem derivationMorphism_unique (D : Derivation Λ k k)
    (f : residueFieldObject.{u, v, w} Λ k ⟶
      artinianDualNumbers.{u, w, v} Λ k)
    (hf : IsDerivationMorphism D f) :
    f = derivationMorphism (Λ := Λ) (k := k) D := by
  apply ArtinianLocalAlgCat.hom_ext
  exact AlgHom.ext fun ⟨a⟩ => TrivSqZeroExt.ext (hf a).1 (ULift.ext (hf a).2)

/-- The special-fibre class has a well-defined pushforward along derivation morphisms. -/
theorem existsUnique_derivationToTangentSpace :
    ∃! γ : Derivation Λ k k →
      tangentSpaceArtinian Λ k
        (isomorphismClasses (BasedCategory.ofFunctor p) hp.cofibered),
      IsDerivationToTangentSpace p hp γ := by
  classical
  let x₀ := specialFiberObject p hp
  let γ : Derivation Λ k k →
      tangentSpaceArtinian Λ k
        (isomorphismClasses (BasedCategory.ofFunctor p) hp.cofibered) :=
    fun D => (isomorphismClasses (BasedCategory.ofFunctor p) hp.cofibered).map
      (derivationMorphism D)
      (classOf (BasedCategory.ofFunctor p) hp.cofibered x₀)
  have hγ : IsDerivationToTangentSpace p hp γ := by
    intro D x f hf
    have hfx := derivationMorphism_unique D f hf
    have hx := classOf_eq_of_isIsomorphic (BasedCategory.ofFunctor p) hp.cofibered x x₀
      (specialFiberObjects_isomorphic p hp x x₀)
    dsimp only [γ]
    rw [← hfx, ← hx]
  refine ⟨γ, hγ, fun γ' hγ' => funext fun D => ?_⟩
  have key {γ} (h : IsDerivationToTangentSpace p hp γ) :=
    h D x₀ _ (derivationMorphism_isDerivationMorphism D)
  exact (key hγ').trans (key hγ).symm

/-- The canonical map `Der_Λ(k,k) → T𝓕`. -/
@[stacks 06SV "the map"]
noncomputable def derivationToTangentSpace :
    Derivation Λ k k → tangentSpaceArtinian Λ k
      (isomorphismClasses (BasedCategory.ofFunctor p) hp.cofibered) :=
  Classical.choose (existsUnique_derivationToTangentSpace p hp)

/-- The map sends a derivation to pushforward of the unique special-fibre class. -/
theorem derivationToTangentSpace_apply
    (D : Derivation Λ k k)
    (x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k))
    (f : residueFieldObject.{u, v, w} Λ k ⟶
      artinianDualNumbers.{u, w, v} Λ k)
    (hf : IsDerivationMorphism D f) :
    derivationToTangentSpace p hp D =
      (isomorphismClasses (BasedCategory.ofFunctor p) hp.cofibered).map f
        (classOf (BasedCategory.ofFunctor p) hp.cofibered x₀) :=
  (Classical.choose_spec (existsUnique_derivationToTangentSpace p hp)).1 D x₀ f hf

/-- A morphism of predeformation categories commutes with the derivation maps on
tangent spaces. -/
@[stacks 06SV "naturality"]
theorem derivationToTangentSpace_naturality
    {G : Type u₂} [Category.{v₂} G]
    (q : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hq : IsPredeformationCategory q)
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (D : Derivation Λ k k) :
    mapIsomorphismClasses hp.cofibered hq.cofibered φ
      (artinianDualNumbers.{u, w, v} Λ k)
      (derivationToTangentSpace p hp D) =
        derivationToTangentSpace q hq D := by
  classical
  let x := specialFiberObject p hp
  let f := derivationMorphism D
  have hf := derivationMorphism_isDerivationMorphism D
  rw [derivationToTangentSpace_apply p hp D x f hf,
    mapIsomorphismClasses_naturality hp.cofibered hq.cofibered φ f
      (classOf (BasedCategory.ofFunctor p) hp.cofibered x),
    mapIsomorphismClasses_classOf hp.cofibered hq.cofibered φ x]
  exact (derivationToTangentSpace_apply q hq D
    ((fiberFunctor φ (residueFieldObject.{u, v, w} Λ k)).obj x)
    f hf).symm

end

end Deformation
