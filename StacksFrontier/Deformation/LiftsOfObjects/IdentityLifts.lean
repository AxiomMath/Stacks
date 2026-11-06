module

public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Functor
public import StacksFrontier.Deformation.LiftsOfObjects.Basic
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.TangentSpace.Predeformation

/-!
# Infinitesimal automorphisms as lifts of the identity

For a category cofibered in groupoids, an automorphism of a pushforward is infinitesimal
relative to a further pushforward precisely when it is a lift of the identity automorphism. At
the dual numbers this exhibits the infinitesimal automorphism group as the fibre of the
automorphism functor over the identity, and hence as the tangent space of that functor at the
identity.

## Main definitions

* `Deformation.identityAutomorphismLifts`: the fibre category of lifts of the target identity
  automorphism.
* `Deformation.residueFieldMorphism`: the canonical morphism of `𝒞_Λ` to the residue-field
  object.
* `Deformation.residueAlgebrasToUnder`: Artinian local `k`-algebras realized as `Λ`-algebras
  under the residue-field object of `𝒞_Λ`.

## Main results

* `Deformation.relativeInfinitesimalAutomorphismsEquivIdentityLifts`: relative infinitesimal
  automorphisms are lifts of the identity.
* `Deformation.infinitesimalAutomorphismsEquivIdentityLifts`: the dual-number case.
* `Deformation.infinitesimalAutomorphisms_eq_tangentFiber`: the identity fibre of the
  automorphism functor.
* `Deformation.automorphismFunctorCategory_isCofiberedInGroupoids`: the category of elements of
  the automorphism functor is cofibered in groupoids over its undercategory base.
* `Deformation.infinitesimalAutomorphismsEquivTangentSpaceAtIdentity`: infinitesimal
  automorphisms are the tangent space of the automorphism functor at the identity.

## Implementation notes

`relativeInfinitesimalAutomorphismsEquivIdentityLifts` states the general equality using the
fibre of the map of discrete categories induced by pushforward on automorphisms, over the
identity of the target; because that fibre is discrete, its objects are exactly its isomorphism
classes. `infinitesimalAutomorphisms_eq_tangentFiber` expresses the identity fibre of the
set-valued automorphism functor as the kernel of the corresponding group homomorphism.

The automorphism functor of an object over `A` has base `A/𝒞_Λ`, which the source identifies
with `𝒞_A`. Its category of elements is cofibered over that base, as is the category of
elements after precomposing with a base-change functor; composing its projection with
`Under.forget` need not preserve cofiberedness, which is why the base change is kept.

At a residue-field point, `residueAlgebrasToUnder` realizes the base `𝒞_k` inside the
undercategory. The final equivalence uses `tangentSpaceAtPoint` over `𝒞_k` at the identity
automorphism, exactly as in the source; this needs no classical or surjectivity hypothesis on
`Λ → k`. The chosen pushforwards identify its dual-number fibre with the relative infinitesimal
automorphism group.

## References

* [Stacks Project, Tag 06JW](https://stacks.math.columbia.edu/tag/06JW)
-/

@[expose] public section

namespace Deformation

/-! ### Lifts of the identity automorphism -/

section
open CategoryTheory

universe u v w u₁ v₁ u₂ v₂

/-- The category of lifts of the identity automorphism of `x` along `g`:
the fibre of the map on automorphisms induced by pushforward. -/
public abbrev identityAutomorphismLifts
    {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C]
    {p : F ⥤ C} {A' A : C} {x' : p.Fiber A'} {x : p.Fiber A}
    (hp : IsCofiberedInGroupoids p)
    (g : A' ⟶ A) (f : x'.1 ⟶ x.1) (hf : p.IsHomLift g f) :=
  (Discrete.functor (fun a : Aut x' =>
    (⟨pushforwardAutomorphismHom hp g f hf a⟩ :
      Discrete (Aut x)))).Fiber (⟨1⟩ : Discrete (Aut x))

/-- Relative infinitesimal automorphisms are precisely lifts of the identity
automorphism along the given morphism. -/
@[stacks 06JW "relative identity lifts"]
public noncomputable def relativeInfinitesimalAutomorphismsEquivIdentityLifts
    {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C]
    {p : F ⥤ C} {A' A : C} {x' : p.Fiber A'} {x : p.Fiber A}
    (hp : IsCofiberedInGroupoids p)
    (g : A' ⟶ A) (f : x'.1 ⟶ x.1) (hf : p.IsHomLift g f) :
    relativeInfinitesimalAutomorphisms hp g f hf ≃
      identityAutomorphismLifts hp g f hf := by
  let φ := pushforwardAutomorphismHom hp g f hf
  refine {
    toFun := fun a => ⟨⟨a.1⟩, ?_⟩
    invFun := fun b => ⟨b.val.as, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · change Discrete.mk (φ a.1) = Discrete.mk 1
    exact congrArg Discrete.mk
      ((mem_relativeInfinitesimalAutomorphisms hp g f hf a.1).mp a.2)
  · apply (mem_relativeInfinitesimalAutomorphisms hp g f hf _).mpr
    have hb := congrArg Discrete.as b.2
    change φ b.val.as = 1
    exact hb
  · intro a
    rfl
  · intro b
    apply Subtype.ext
    cases b.val
    rfl

/-- Infinitesimal automorphisms at a residue-field object are lifts of its
identity automorphism to the dual numbers. -/
@[stacks 06JW "dual-number identity lifts"]
public noncomputable def infinitesimalAutomorphismsEquivIdentityLifts
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {A₀ Aε : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {x₀ : p.Fiber A₀} {xε : p.Fiber Aε}
    (hp : IsCofiberedInGroupoids p)
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i) :
    let r := canonicalRetraction hp g e hpair.split i hi
    infinitesimalAutomorphisms hp g e hpair i hi ≃
      identityAutomorphismLifts hp e r.1 r.2.1 := by
  let r := canonicalRetraction hp g e hpair.split i hi
  exact relativeInfinitesimalAutomorphismsEquivIdentityLifts hp e r.1 r.2.1

/-- At a point over the residue field, infinitesimal automorphisms are the
fibre over the identity of the automorphism functor at the dual numbers. -/
@[stacks 06JW "tangent fibre at the identity"]
public theorem infinitesimalAutomorphisms_eq_tangentFiber
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {x : F} (hp : IsCofiberedInGroupoids p)
    (P : ChosenPushforwardsAt p x)
    {A₀ Aε : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀)
    (hpair : IsCanonicalDualNumberPair g e)
    (hbase : p.obj x = A₀) :
    let U₀ : Under (p.obj x) := Under.mk (eqToHom hbase)
    let Uε : Under (p.obj x) := Under.mk (eqToHom hbase ≫ g)
    let j : U₀ ⟶ Uε := Under.homMk g (by simp [U₀, Uε])
    let r : Uε ⟶ U₀ := Under.homMk e (by simp [U₀, Uε, hpair.split])
    infinitesimalAutomorphisms hp g e hpair (P.map j)
      (P.map_isHomLift j) = MonoidHom.ker (P.transportAutHom r) := by
  let U₀ : Under (p.obj x) := Under.mk (eqToHom hbase)
  let Uε : Under (p.obj x) := Under.mk (eqToHom hbase ≫ g)
  let j : U₀ ⟶ Uε := Under.homMk g (by simp [U₀, Uε])
  let r : Uε ⟶ U₀ := Under.homMk e (by simp [U₀, Uε, hpair.split])
  show infinitesimalAutomorphisms hp g e hpair (P.map j)
      (P.map_isHomLift j) = MonoidHom.ker (P.transportAutHom r)
  let i := P.map j
  have hU₀ : U₀.right = A₀ := rfl
  have hUε : Uε.right = Aε := rfl
  let ha : p.obj (P.obj U₀).1 = A₀ := (P.obj U₀).2.trans hU₀
  let hb : p.obj (P.obj Uε).1 = Aε := (P.obj Uε).2.trans hUε
  have hi : p.IsHomLift g i := by
    apply IsHomLift.of_fac p g i ha hb
    simpa [i, j, U₀, Uε, ha, hb] using IsHomLift.fac p j.right i
  let ret := canonicalRetraction hp g e hpair.split i hi
  have hret : ret.1 = P.map r := by
    let _ := isStronglyCocartesian_of_isCofiberedInGroupoids hp g i hi
    let _ : p.IsHomLift e (P.map r) := P.map_isHomLift r
    let _ : p.IsHomLift e ret.1 := ret.2.1
    apply Functor.IsStronglyCocartesian.ext (p := p) (f := g) (φ := i) (g := e)
    have hjr : j ≫ r = 𝟙 U₀ := by
      apply Under.UnderMorphism.ext
      simp [j, r, U₀, Uε, hpair.split]
    calc
      i ≫ ret.1 = 𝟙 (P.obj U₀).1 := ret.2.2
      _ = i ≫ P.map r := by
        dsimp [i]
        rw [← P.map_comp j r, hjr, P.map_id]
  apply Subgroup.ext
  intro a
  show a ∈ infinitesimalAutomorphisms hp g e hpair i hi ↔
    a ∈ MonoidHom.ker (P.transportAutHom r)
  rw [mem_infinitesimalAutomorphisms_iff]
  rw [hret]
  show a.asIso.hom.val ≫ P.map r = P.map r ↔ P.transportAutHom r a = 1
  constructor
  · intro h
    apply Aut.ext
    apply Iso.ext
    apply Functor.Fiber.hom_ext
    show P.transportHom r a = 𝟙 (P.obj U₀).1
    let _ := P.map_cocartesian r
    let _ := P.transportHom_isHomLift r a
    let _ : p.IsHomLift (𝟙 U₀.right) (𝟙 (P.obj U₀).1) :=
      IsHomLift.id (P.obj U₀).2
    apply Functor.IsStronglyCocartesian.ext (p := p) (f := r.right)
      (φ := P.map r) (g := 𝟙 U₀.right)
    calc
      P.map r ≫ P.transportHom r a = a.asIso.hom.val ≫ P.map r := P.map_transportHom r a
      _ = P.map r := h
      _ = P.map r ≫ 𝟙 (P.obj U₀).1 := (Category.comp_id _).symm
  · intro h
    have hh := congrArg (fun z : Aut (P.obj U₀) => z.asIso.hom.val) h
    change P.transportHom r a = 𝟙 (P.obj U₀).1 at hh
    have hsq := P.map_transportHom r a
    rw [hh, Category.comp_id] at hsq
    exact hsq.symm

end

/-! ### Artinian local algebras over the residue field as algebras under it -/

section
open CategoryTheory

universe u v w

variable (Λ : Type u) (k : Type w) [CommRing Λ] [Field k] [Algebra Λ k]

/-- Restrict the scalars of an Artinian local `k`-algebra along `Λ → k`. -/
@[implicit_reducible]
public noncomputable def restrictResidueAlgebra
    (A : ArtinianLocalAlgCat.{w, max v w, w} k k) :
    ArtinianLocalAlgCat.{u, max v w, w} Λ k := by
  letI : Algebra Λ A := Algebra.compHom A (algebraMap Λ k)
  letI : IsScalarTower Λ k A := IsScalarTower.of_algebraMap_eq' rfl
  exact { carrier := A, residueEquiv := A.residueEquiv.restrictScalars Λ }

/-- The `k`-algebra structure as a morphism from the residue-field object. -/
@[implicit_reducible]
public noncomputable def residueAlgebraStructure
    (A : ArtinianLocalAlgCat.{w, max v w, w} k k) :
    residueFieldObject.{u, v, w} Λ k ⟶ restrictResidueAlgebra Λ k A := by
  letI : Algebra Λ A := Algebra.compHom A (algebraMap Λ k)
  letI : IsScalarTower Λ k A := IsScalarTower.of_algebraMap_eq' rfl
  refine
    { hom := (IsScalarTower.toAlgHom Λ k A).comp
        (ULift.algEquiv (R := Λ) (A := k)).toAlgHom
      isLocal := by
        let _ : Field (residueFieldObject.{u, v, w} Λ k) :=
          inferInstanceAs (Field (ULift.{v} k))
        infer_instance
      residue_comm := ?_ }
  intro a
  change A.residueEquiv (IsLocalRing.residue A (algebraMap k A a.down)) = _
  rw [← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  rw [AlgEquiv.commutes]
  change a.down = (residueFieldObject.{u, v, w} Λ k).residueEquiv
    (IsLocalRing.residue (ULift.{v} k) a)
  symm
  simp only [residueFieldObject, IsLocalRing.residue_def]
  rfl

/-- Regard an Artinian local `k`-algebra as a `Λ`-algebra under the residue
field. This realizes the source's identification `𝒞_k = k/𝒞_Λ`. -/
@[implicit_reducible]
public noncomputable def residueAlgebrasToUnder :
    ArtinianLocalAlgCat.{w, max v w, w} k k ⥤
      Under (residueFieldObject.{u, v, w} Λ k) where
  obj A := Under.mk (residueAlgebraStructure Λ k A)
  map {A B} f := by
    letI : Algebra Λ A := Algebra.compHom A (algebraMap Λ k)
    letI : Algebra Λ B := Algebra.compHom B (algebraMap Λ k)
    letI : IsScalarTower Λ k A := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Λ k B := IsScalarTower.of_algebraMap_eq' rfl
    refine Under.homMk
      { hom := f.hom.restrictScalars Λ
        isLocal := f.isLocal
        residue_comm := f.residue_comm } ?_
    exact ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun a => f.hom.commutes a.down)
  map_id A := Under.UnderMorphism.ext (ArtinianLocalAlgCat.hom_ext rfl)
  map_comp f g := Under.UnderMorphism.ext (ArtinianLocalAlgCat.hom_ext rfl)

end

/-! ### Dual numbers in the universe of the vector-space model -/

section
open CategoryTheory

universe u v w

/-- The dual numbers of `k` and the square-zero extension of `k` by its universe lift are
isomorphic as `Λ`-algebras. -/
public noncomputable def dualNumberLiftedEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] :
    DualNumber k ≃ₐ[Λ] TrivSqZeroExt k (ULift.{v} k) := by
  letI : IsScalarTower Λ k (DualNumber k) :=
    IsScalarTower.of_algebraMap_smul (R := Λ) (A := k)
      (M := DualNumber k) fun _ _ => by
        simp [Algebra.algebraMap_eq_smul_one]
  letI : IsScalarTower Λ k (TrivSqZeroExt k (ULift.{v} k)) :=
    IsScalarTower.of_algebraMap_smul (R := Λ) (A := k)
      (M := TrivSqZeroExt k (ULift.{v} k)) fun _ _ => by
        simp [Algebra.algebraMap_eq_smul_one]
  let e : k ≃ₗ[k] ULift.{v} k :=
    (ULift.algEquiv (R := k) (A := k)).symm.toLinearEquiv
  let fK := TrivSqZeroExt.map e.toLinearMap
  let f := fK.restrictScalars Λ
  apply AlgEquiv.ofBijective f
  constructor
  · intro x y h
    apply TrivSqZeroExt.ext
    · have hfst := congrArg TrivSqZeroExt.fst h
      change (TrivSqZeroExt.map e.toLinearMap x).fst =
        (TrivSqZeroExt.map e.toLinearMap y).fst at hfst
      simpa only [TrivSqZeroExt.fst_map] using hfst
    · apply e.injective
      have hsnd := congrArg TrivSqZeroExt.snd h
      change (TrivSqZeroExt.map e.toLinearMap x).snd =
        (TrivSqZeroExt.map e.toLinearMap y).snd at hsnd
      rwa [TrivSqZeroExt.snd_map, TrivSqZeroExt.snd_map] at hsnd
  · intro x
    obtain ⟨v', hv'⟩ := e.surjective x.snd
    let y : DualNumber k := (x.fst, v')
    refine ⟨y, TrivSqZeroExt.ext ?_ ?_⟩
    · change (TrivSqZeroExt.map e.toLinearMap y).fst = x.fst
      rw [TrivSqZeroExt.fst_map]
      rfl
    · change (TrivSqZeroExt.map e.toLinearMap y).snd = x.snd
      rw [TrivSqZeroExt.snd_map]
      exact hv'

/-- The identification of dual numbers preserves the constant coordinate. -/
public theorem dualNumberLiftedEquiv_fst
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (z : DualNumber k) :
    (dualNumberLiftedEquiv.{u, v} (Λ := Λ) z).fst = z.fst := by
  simp [dualNumberLiftedEquiv, TrivSqZeroExt.fst_map]

/-- The endomorphism of the dual numbers twisting both coordinates by an automorphism of `k`. -/
public noncomputable def dualNumberCoefficientHom
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (σ : k ≃ₐ[Λ] k) : DualNumber k →ₐ[Λ] DualNumber k := by
  let fBase : k →ₐ[Λ] DualNumber k :=
    { toFun := fun a => TrivSqZeroExt.inl (σ a)
      map_one' := by simp
      map_mul' := by intro a b; simp [map_mul]
      map_zero' := by simp
      map_add' := by intro a b; simp [map_add]
      commutes' := by
        intro r
        rw [TrivSqZeroExt.algebraMap_eq_inl']
        simp [σ.commutes] }
  let fMod : k →ₗ[Λ] DualNumber k :=
    (TrivSqZeroExt.inrHom k k).restrictScalars Λ ∘ₗ
      σ.toLinearMap.restrictScalars Λ
  exact TrivSqZeroExt.lift fBase fMod
    (by
      intro a b
      change TrivSqZeroExt.inr (σ a) * TrivSqZeroExt.inr (σ b) = 0
      rw [TrivSqZeroExt.inr_mul_inr])
    (by
      intro a b
      change TrivSqZeroExt.inr (σ (a * b)) =
        TrivSqZeroExt.inl (σ a) * TrivSqZeroExt.inr (σ b)
      rw [TrivSqZeroExt.inl_mul_inr]
      exact congrArg TrivSqZeroExt.inr (map_mul σ a b))
    (by
      intro a b
      change TrivSqZeroExt.inr (σ (b * a)) =
        TrivSqZeroExt.inr (σ b) * TrivSqZeroExt.inl (σ a)
      rw [TrivSqZeroExt.inr_mul_inl]
      exact congrArg TrivSqZeroExt.inr (map_mul σ b a))

/-- The twist acts by `σ` on the constant coordinate. -/
public theorem dualNumberCoefficientHom_fst
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (σ : k ≃ₐ[Λ] k) (z : DualNumber k) :
    (dualNumberCoefficientHom σ z).fst = σ z.fst := by
  simp [dualNumberCoefficientHom, TrivSqZeroExt.lift_def]

/-- The twist acts by `σ` on the infinitesimal coordinate. -/
public theorem dualNumberCoefficientHom_snd
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (σ : k ≃ₐ[Λ] k) (z : DualNumber k) :
    (dualNumberCoefficientHom σ z).snd = σ z.snd := by
  simp [dualNumberCoefficientHom, TrivSqZeroExt.lift_def]

/-- The twist is bijective. -/
public theorem dualNumberCoefficientHom_bijective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (σ : k ≃ₐ[Λ] k) : Function.Bijective (dualNumberCoefficientHom σ) := by
  constructor
  · intro z z' h
    apply TrivSqZeroExt.ext
    · apply σ.injective
      simpa only [dualNumberCoefficientHom_fst] using congrArg TrivSqZeroExt.fst h
    · apply σ.injective
      simpa only [dualNumberCoefficientHom_snd] using congrArg TrivSqZeroExt.snd h
  · intro z
    let w : DualNumber k := ⟨σ.symm z.fst, σ.symm z.snd⟩
    exact ⟨w, TrivSqZeroExt.ext
      ((dualNumberCoefficientHom_fst σ w).trans (σ.apply_symm_apply _))
      ((dualNumberCoefficientHom_snd σ w).trans (σ.apply_symm_apply _))⟩

/-- The twist of the dual numbers by an automorphism of `k`, as an isomorphism. -/
public noncomputable def dualNumberCoefficientEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (σ : k ≃ₐ[Λ] k) : DualNumber k ≃ₐ[Λ] DualNumber k :=
  AlgEquiv.ofBijective (dualNumberCoefficientHom σ)
    (dualNumberCoefficientHom_bijective σ)

/-- The twist on constants. -/
public theorem dualNumberCoefficientEquiv_inl
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (σ : k ≃ₐ[Λ] k) (a : k) :
    dualNumberCoefficientEquiv σ (TrivSqZeroExt.inl a) =
      TrivSqZeroExt.inl (σ a) := by
  simp [dualNumberCoefficientEquiv, dualNumberCoefficientHom,
    TrivSqZeroExt.lift_apply_inl]

/-- The twist on the constant coordinate. -/
public theorem dualNumberCoefficientEquiv_fst
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (σ : k ≃ₐ[Λ] k) (z : DualNumber k) :
    (dualNumberCoefficientEquiv σ z).fst = σ z.fst :=
  dualNumberCoefficientHom_fst σ z

/-- The twist on the infinitesimal coordinate. -/
public theorem dualNumberCoefficientEquiv_snd
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (σ : k ≃ₐ[Λ] k) (z : DualNumber k) :
    (dualNumberCoefficientEquiv σ z).snd = σ z.snd :=
  dualNumberCoefficientHom_snd σ z

/-- The automorphism of `k` determined by an identification of the residue-field object
with `k`. -/
public noncomputable def residueCoordinateTwist
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (i₀ : residueFieldObject.{u, v, w} Λ k ≃ₐ[Λ] k) :
    k ≃ₐ[Λ] k := (ULift.algEquiv (R := Λ) (A := k)).symm.trans i₀

/-- A canonical dual-number pair presents its target as the dual numbers in such a way that
the constant inclusion is the structural one. -/
public noncomputable def residueCorrectedDualNumberEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {g : residueFieldObject.{u, v, w} Λ k ⟶ Aε}
    {e : Aε ⟶ residueFieldObject.{u, v, w} Λ k}
    (hpair : IsCanonicalDualNumberPair g e) :
    Aε ≃ₐ[Λ] DualNumber k := by
  let i₀ := Classical.choose hpair
  let htail := Classical.choose_spec hpair
  let iε := Classical.choose htail
  exact iε.trans (dualNumberCoefficientEquiv (residueCoordinateTwist i₀).symm)

/-- The corrected presentation takes the structural inclusion to the constant inclusion. -/
public theorem residueCorrectedDualNumberEquiv_comp_inclusion
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {g : residueFieldObject.{u, v, w} Λ k ⟶ Aε}
    {e : Aε ⟶ residueFieldObject.{u, v, w} Λ k}
    (hpair : IsCanonicalDualNumberPair g e) :
    (residueCorrectedDualNumberEquiv hpair).toAlgHom.comp g.hom =
      (TrivSqZeroExt.inlAlgHom Λ k k).comp
        (ULift.algEquiv (R := Λ) (A := k)).toAlgHom := by
  let i₀ := Classical.choose hpair
  let htail := Classical.choose_spec hpair
  let iε := Classical.choose htail
  have hg := (Classical.choose_spec htail).1
  let u := ULift.algEquiv (R := Λ) (A := k)
  let σ := residueCoordinateTwist i₀
  apply AlgHom.ext
  intro a
  dsimp [residueCorrectedDualNumberEquiv]
  show dualNumberCoefficientEquiv σ.symm (iε (g.hom a)) =
    TrivSqZeroExt.inl (u a)
  have hi := congrArg (fun f : residueFieldObject.{u, v, w} Λ k →ₐ[Λ]
      DualNumber k => f a) hg
  change iε (g.hom a) = TrivSqZeroExt.inl (i₀ a) at hi
  rw [hi, dualNumberCoefficientEquiv_inl]
  simp [σ, residueCoordinateTwist, u]

/-- The corrected presentation computes the residue map. -/
public theorem residueCorrectedDualNumberEquiv_fst
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {g : residueFieldObject.{u, v, w} Λ k ⟶ Aε}
    {e : Aε ⟶ residueFieldObject.{u, v, w} Λ k}
    (hpair : IsCanonicalDualNumberPair g e) (a : Aε) :
    (residueCorrectedDualNumberEquiv hpair a).fst =
      Aε.residueEquiv (IsLocalRing.residue Aε a) := by
  let i₀ := Classical.choose hpair
  let htail := Classical.choose_spec hpair
  let iε := Classical.choose htail
  have he := (Classical.choose_spec htail).2.1
  have hEval : i₀ (e.hom a) = (iε a).fst := by
    have h := congrArg (fun f => f a) he
    simpa using h
  have hCoord : i₀.symm (iε a).fst = e.hom a := by
    apply i₀.injective
    simpa using hEval.symm
  let liftCoord := ULift.algEquiv (R := Λ) (A := k)
  have hResidue (y : residueFieldObject.{u, v, w} Λ k) :
      (residueFieldObject.{u, v, w} Λ k).residueEquiv
        (IsLocalRing.residue _ y) = liftCoord y := by
    simp only [residueFieldObject, IsLocalRing.residue_def]
    rfl
  calc
    (residueCorrectedDualNumberEquiv hpair a).fst =
        (residueCoordinateTwist i₀).symm (iε a).fst := by
      dsimp [residueCorrectedDualNumberEquiv]
      exact dualNumberCoefficientEquiv_fst _ _
    _ = liftCoord (i₀.symm (iε a).fst) := by
      simp [residueCoordinateTwist, liftCoord]
    _ = liftCoord (e.hom a) := congrArg liftCoord hCoord
    _ = (residueFieldObject.{u, v, w} Λ k).residueEquiv
        (IsLocalRing.residue _ (e.hom a)) := (hResidue (e.hom a)).symm
    _ = Aε.residueEquiv (IsLocalRing.residue Aε a) := e.residue_comm a

/-- The canonical morphism of `𝒞_Λ` into the residue-field object. -/
public noncomputable def residueFieldMorphism
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} :
    B ⟶ residueFieldObject.{u, v, w} Λ k where
  hom := (ULift.algEquiv (R := Λ) (A := k)).symm.toAlgHom.comp
    (B.residueEquiv.toAlgHom.comp
      (IsScalarTower.toAlgHom Λ B (IsLocalRing.ResidueField B)))
  isLocal := by
    refine ⟨fun a ha => (IsLocalRing.residue_ne_zero_iff_isUnit a).mp ?_⟩
    have hne := ha.ne_zero
    intro hz
    apply hne
    change ULift.up (B.residueEquiv (IsLocalRing.residue B a)) = 0
    simp only [hz, map_zero]
    rfl
  residue_comm := fun _ => rfl

/-- Every morphism of `𝒞_Λ` into the residue-field object is the canonical one. -/
public theorem eq_residueFieldMorphism
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {B : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : B ⟶ residueFieldObject.{u, v, w} Λ k) :
    f = residueFieldMorphism := homToResidueFieldObject_unique f residueFieldMorphism

end

/-! ### Isomorphism classes in the slice of a category of elements -/

section
open CategoryTheory

universe u₁ v₁ u₂

/-- The structure functor of the slice of a category of elements over a chosen element. -/
public abbrev elementSliceProjection
    {C : Type u₁} [Category.{v₁} C]
    (G : C ⥤ Type u₂) {B : C} (b : G.obj B) :=
  Over.forget (G.elementsMk B b) ⋙ CategoryOfElements.π G

/-- The element of `G` underlying an object of a fibre of that slice. -/
public noncomputable def elementSliceExtract
    {C : Type u₁} [Category.{v₁} C]
    (G : C ⥤ Type u₂) {B D : C} (b : G.obj B)
    (y : (elementSliceProjection G b).Fiber D) : G.obj D := by
  rcases y with ⟨⟨@⟨A, a⟩, _, m⟩, hy⟩
  change A = D at hy
  cases hy
  exact a

/-- The underlying element maps to the chosen one. -/
public theorem elementSliceExtract_condition
    {C : Type u₁} [Category.{v₁} C]
    (G : C ⥤ Type u₂) {B D : C} (b : G.obj B) (r : D ⟶ B)
    (hr : ∀ f : D ⟶ B, f = r)
    (y : (elementSliceProjection G b).Fiber D) :
    G.map r (elementSliceExtract G b y) = b := by
  rcases y with ⟨⟨@⟨A, a⟩, _, m⟩, hy⟩
  change A = D at hy
  cases hy
  have hm := m.map_val
  change G.map m.hom a = b at hm
  rw [hr m.hom] at hm
  exact hm

/-- Isomorphic objects of the fibre have the same underlying element. -/
public theorem elementSliceExtract_eq_of_iso
    {C : Type u₁} [Category.{v₁} C]
    (G : C ⥤ Type u₂) {B D : C} (b : G.obj B)
    (y y' : (elementSliceProjection G b).Fiber D) (i : y ≅ y') :
    elementSliceExtract G b y = elementSliceExtract G b y' := by
  rcases y with ⟨⟨@⟨A, a⟩, _, m⟩, hy⟩
  rcases y' with ⟨⟨@⟨A', a'⟩, _, m'⟩, hy'⟩
  change A = D at hy
  cases hy
  change A' = D at hy'
  cases hy'
  show a = a'
  let _ := i.hom.2
  have hbase : i.hom.val.left.hom = 𝟙 D := by
    have h := IsHomLift.fac' (elementSliceProjection G b) (𝟙 D) i.hom.val
    simp [elementSliceProjection, CategoryOfElements.π] at h
    exact h.trans (eqToHom_refl _ _)
  have hlabel := i.hom.val.left.map_val
  change G.map i.hom.val.left.hom a = a' at hlabel
  rw [hbase] at hlabel
  simpa using hlabel

/-- The object of the fibre determined by an element mapping to the chosen one. -/
public noncomputable def elementSliceRepresentative
    {C : Type u₁} [Category.{v₁} C]
    (G : C ⥤ Type u₂) {B D : C} (b : G.obj B) (r : D ⟶ B)
    (a : {z : G.obj D // G.map r z = b}) :
    (elementSliceProjection G b).Fiber D := by
  let x := G.elementsMk D a.1
  let m : x ⟶ G.elementsMk B b := Functor.Elements.homMk (x := x) r a.2
  exact ⟨Over.mk m, rfl⟩

/-- When `D ⟶ B` is unique, isomorphism classes in the fibre of the slice over `D` are the
elements of `G` over `D` mapping to the chosen element. -/
public noncomputable def elementSliceKernelEquiv
    {C : Type u₁} [Category.{v₁} C]
    (G : C ⥤ Type u₂) {B D : C} (b : G.obj B) (r : D ⟶ B)
    (hr : ∀ f : D ⟶ B, f = r) :
    Quotient (isIsomorphicSetoid ((elementSliceProjection G b).Fiber D)) ≃
      {a : G.obj D // G.map r a = b} := by
  let toKernel : (elementSliceProjection G b).Fiber D →
      {a : G.obj D // G.map r a = b} := fun y =>
    ⟨elementSliceExtract G b y, elementSliceExtract_condition G b r hr y⟩
  let fromKernel : {a : G.obj D // G.map r a = b} →
      Quotient (isIsomorphicSetoid ((elementSliceProjection G b).Fiber D)) :=
    fun a => Quotient.mk _ (elementSliceRepresentative G b r a)
  refine {
    toFun := Quotient.lift toKernel (by
      intro y y' h
      rcases h with ⟨i⟩
      exact Subtype.ext (elementSliceExtract_eq_of_iso G b y y' i))
    invFun := fromKernel
    left_inv := ?_
    right_inv := ?_ }
  · intro z
    induction z using Quotient.inductionOn with
    | h y =>
      apply Quotient.sound
      let a := toKernel y
      have hy : y = elementSliceRepresentative G b r a := by
        rcases y with ⟨⟨@⟨A, x⟩, _, m⟩, hA⟩
        change A = D at hA
        cases hA
        dsimp [a, toKernel, elementSliceRepresentative, elementSliceExtract]
        have hx : x = a.1 := rfl
        have h2 : G.map r x = b := by rw [hx]; exact a.2
        have hm : m.hom = r := hr m.hom
        have hm' : m = Functor.Elements.homMk (x := G.elementsMk D x)
            (y := G.elementsMk B b) r h2 :=
          Functor.Elements.hom_ext hm
        subst m
        rfl
      exact ⟨eqToIso hy.symm⟩
  · intro a
    exact Subtype.ext rfl

end

/-! ### The automorphism functor as a cofibered category and its tangent space -/

section
open CategoryTheory

universe u v w u₁ v₁ u₂ v₂

/-- The category of elements of the automorphism functor is cofibered in
groupoids over its undercategory base, also after any change of base. -/
public theorem automorphismFunctorCategory_isCofiberedInGroupoids
    {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C]
    {D : Type u₂} [Category.{v₂} D] {p : F ⥤ C} {x : F}
    (P : ChosenPushforwardsAt p x)
    (baseChange : D ⥤ Under (p.obj x)) :
    IsCofiberedInGroupoids
      (CategoryOfElements.π (baseChange ⋙ automorphismFunctor P)) := by
  let G := baseChange ⋙ automorphismFunctor P
  show Functor.IsFiberedInGroupoids (CategoryOfElements.π G).op
  constructor
  · intro V U f x hx
    rcases V with ⟨V⟩
    rcases U with ⟨U⟩
    rcases x with ⟨x⟩
    change Opposite.op ((CategoryOfElements.π G).obj x) = Opposite.op U at hx
    cases hx
    let y := G.elementsMk V (G.map f.unop x.val)
    let g : x ⟶ y := Functor.Elements.homMk (x := x) (y := y) f.unop rfl
    refine ⟨Opposite.op y, g.op, ?_⟩
    have hmap : (CategoryOfElements.π G).op.map g.op = f := by
      exact Quiver.Hom.opEquiv.symm.injective rfl
    rw [← hmap]
    exact IsHomLift.map (p := (CategoryOfElements.π G).op) g.op
  · intro x y z φ ψ f hf
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    rcases z with ⟨z⟩
    have hbase : φ.unop.hom ≫ f.unop = ψ.unop.hom := by
      exact congrArg Quiver.Hom.unop hf
    let g : y ⟶ z := Functor.Elements.homMk (x := y) (y := z) f.unop (by
      let f' : y.obj ⟶ z.obj := f.unop
      have hb' : φ.unop.hom ≫ f' = ψ.unop.hom := hbase
      have h1 := ψ.unop.map_val
      rw [← hb', Functor.map_comp_apply, φ.unop.map_val] at h1
      exact h1)
    refine ⟨g.op, ⟨?_, ?_⟩, ?_⟩
    · have hmap : (CategoryOfElements.π G).op.map g.op = f := by
        exact Quiver.Hom.opEquiv.symm.injective rfl
      exact hmap
    · apply Quiver.Hom.opEquiv.symm.injective
      apply Functor.Elements.hom_ext
      exact hbase
    · intro χ hχ
      apply Quiver.Hom.opEquiv.symm.injective
      apply Functor.Elements.hom_ext
      have hh := congrArg Quiver.Hom.unop hχ.1
      change χ.unop.hom = f.unop at hh
      show χ.unop.hom = f.unop
      exact hh

/-- Infinitesimal automorphisms at a residue-field object are the tangent
space at the identity of its automorphism functor. -/
@[stacks 06JW "tangent space at the identity"]
public noncomputable def infinitesimalAutomorphismsEquivTangentSpaceAtIdentity
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x : F}
    (hp : IsCofiberedInGroupoids p)
    (P : ChosenPushforwardsAt p x)
    (hbase : p.obj x = residueFieldObject.{u, v, w} Λ k)
    (Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (g : residueFieldObject.{u, v, w} Λ k ⟶ Aε)
    (e : Aε ⟶ residueFieldObject.{u, v, w} Λ k)
    (hpair : IsCanonicalDualNumberPair g e) :
    let U₀ : Under (p.obj x) := Under.mk (eqToHom hbase)
    let Uε : Under (p.obj x) := Under.mk (eqToHom hbase ≫ g)
    let j : U₀ ⟶ Uε := Under.homMk g (by simp [U₀, Uε])
    let baseChange := residueAlgebrasToUnder.{u, v, w} Λ k ⋙
      Under.map (eqToHom hbase)
    let AutFunctor := baseChange ⋙ automorphismFunctor P
    let q := CategoryOfElements.π AutFunctor
    let k₀ := residueFieldObject.{w, v, w} k k
    let identityPoint : q.Fiber k₀ :=
      ⟨AutFunctor.elementsMk k₀ (1 : Aut (P.obj (baseChange.obj k₀))), rfl⟩
    (infinitesimalAutomorphisms hp g e hpair (P.map j)
      (P.map_isHomLift j)) ≃
    tangentSpaceAtPoint q
        (automorphismFunctorCategory_isCofiberedInGroupoids P baseChange)
        identityPoint := by
  let U₀ : Under (p.obj x) := Under.mk (eqToHom hbase)
  let Uε : Under (p.obj x) := Under.mk (eqToHom hbase ≫ g)
  let j : U₀ ⟶ Uε := Under.homMk g (by simp [U₀, Uε])
  let r : Uε ⟶ U₀ := Under.homMk e (by simp [U₀, Uε, hpair.split])
  let baseChange := residueAlgebrasToUnder.{u, v, w} Λ k ⋙
    Under.map (eqToHom hbase)
  let AutFunctor := baseChange ⋙ automorphismFunctor P
  let q := CategoryOfElements.π AutFunctor
  let k₀ := residueFieldObject.{w, v, w} k k
  let identityPoint : q.Fiber k₀ :=
    ⟨AutFunctor.elementsMk k₀ (1 : Aut (P.obj (baseChange.obj k₀))), rfl⟩
  let D := artinianDualNumbers.{w, w, v} k k
  let red : D ⟶ k₀ := residueFieldMorphism
  have hredUnique : ∀ f : D ⟶ k₀, f = red := fun f => eq_residueFieldMorphism f
  let hpre := isPredeformationCategory_objectsOverFunctor q
    (automorphismFunctorCategory_isCofiberedInGroupoids P baseChange) identityPoint
  let hq := automorphismFunctorCategory_isCofiberedInGroupoids P baseChange
  let tangentCategory := BasedCategory.ofFunctor
    (objectsOverFunctor q identityPoint.1)
  have hclass :
      tangentSpaceAtPoint q hq identityPoint =
        Quotient (isIsomorphicSetoid (tangentCategory.p.Fiber D)) := by
    change (isomorphismClasses tangentCategory hpre.cofibered).obj D = _
    exact isomorphismClasses_obj tangentCategory hpre.cofibered D
  have htangentKernel :
      tangentSpaceAtPoint q hq identityPoint ≃
        {a : Aut (P.obj (baseChange.obj D)) //
          P.transportAutHom (baseChange.map red) a = 1} := by
    let G := baseChange ⋙ automorphismFunctor P
    change _ ≃ {a : G.obj D // G.map red a =
      (1 : Aut (P.obj (baseChange.obj k₀)))}
    rw [hclass]
    exact elementSliceKernelEquiv G (1 : Aut (P.obj (baseChange.obj k₀))) red hredUnique
  let DΛ := restrictResidueAlgebra Λ k D
  let V₀ := baseChange.obj k₀
  let Vε := baseChange.obj D
  let d : Vε ⟶ V₀ := baseChange.map red
  letI : AddCommGroup (FGModuleCat.of k (ULift.{v} k)) :=
    (FGModuleCat.of k (ULift.{v} k)).obj.isAddCommGroup
  letI : Module k (FGModuleCat.of k (ULift.{v} k)) :=
    (FGModuleCat.of k (ULift.{v} k)).obj.isModule
  letI : SMul k (FGModuleCat.of k (ULift.{v} k)) :=
    ((FGModuleCat.of k (ULift.{v} k)).obj.isModule).toDistribMulAction.toSMul
  let mopModule : Module kᵐᵒᵖ (FGModuleCat.of k (ULift.{v} k)) :=
    Module.compHom (FGModuleCat.of k (ULift.{v} k)) {
      toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by simp [mul_comm]
      map_zero' := rfl
      map_add' := by intros; rfl }
  letI : Module kᵐᵒᵖ (FGModuleCat.of k (ULift.{v} k)) := mopModule
  letI : SMul kᵐᵒᵖ (FGModuleCat.of k (ULift.{v} k)) :=
    mopModule.toDistribMulAction.toSMul
  letI : CommRing (TrivSqZeroExt k (FGModuleCat.of k (ULift.{v} k))) := D.commRing
  letI : Algebra k (TrivSqZeroExt k (FGModuleCat.of k (ULift.{v} k))) := D.algebra
  have hCentral : IsCentralScalar k (FGModuleCat.of k (ULift.{v} k)) :=
    ⟨fun _ _ => rfl⟩
  letI : IsCentralScalar k (FGModuleCat.of k (ULift.{v} k)) := hCentral
  let liftCoeff : k ≃ₗ[k] (FGModuleCat.of k (ULift.{v} k)) :=
    (ULift.algEquiv (R := k) (A := k)).symm.toLinearEquiv
  let fModel : DualNumber k →ₐ[k]
      TrivSqZeroExt k (FGModuleCat.of k (ULift.{v} k)) :=
    @TrivSqZeroExt.map k k _ _ _ _ _ (FGModuleCat.of k (ULift.{v} k)) _ _ _
      hCentral liftCoeff.toLinearMap
  have hfModel : Function.Bijective fModel := by
    constructor
    · intro y y' h
      apply TrivSqZeroExt.ext
      · have hfst := congrArg TrivSqZeroExt.fst h
        change (TrivSqZeroExt.map liftCoeff.toLinearMap y).fst =
          (TrivSqZeroExt.map liftCoeff.toLinearMap y').fst at hfst
        rwa [TrivSqZeroExt.fst_map, TrivSqZeroExt.fst_map] at hfst
      · apply liftCoeff.injective
        have hsnd := congrArg TrivSqZeroExt.snd h
        change (TrivSqZeroExt.map liftCoeff.toLinearMap y).snd =
          (TrivSqZeroExt.map liftCoeff.toLinearMap y').snd at hsnd
        rwa [TrivSqZeroExt.snd_map, TrivSqZeroExt.snd_map] at hsnd
    · intro z
      refine ⟨(z.fst, liftCoeff.symm z.snd), TrivSqZeroExt.ext ?_ ?_⟩
      · change (TrivSqZeroExt.map liftCoeff.toLinearMap
          (z.fst, liftCoeff.symm z.snd)).fst = z.fst
        exact TrivSqZeroExt.fst_map _ _
      · change (TrivSqZeroExt.map liftCoeff.toLinearMap
          (z.fst, liftCoeff.symm z.snd)).snd = z.snd
        exact (TrivSqZeroExt.snd_map _ _).trans
          (liftCoeff.apply_symm_apply z.snd)
  let fΛ : DualNumber k →ₐ[Λ] DΛ := {
    toFun := fModel
    map_one' := fModel.map_one
    map_mul' := fModel.map_mul
    map_zero' := fModel.map_zero
    map_add' := fModel.map_add
    commutes' := fun a => by
      change fModel (TrivSqZeroExt.inl (algebraMap Λ k a)) =
        (algebraMap k (TrivSqZeroExt k (FGModuleCat.of k (ULift.{v} k))))
          (algebraMap Λ k a)
      rw [TrivSqZeroExt.map_inl, TrivSqZeroExt.algebraMap_eq_inl']
      simp }
  let eModel : DualNumber k ≃ₐ[Λ] DΛ := AlgEquiv.ofBijective fΛ hfModel
  let E := residueCorrectedDualNumberEquiv hpair
  let E' : Aε ≃ₐ[Λ] DΛ := E.trans eModel
  have hEres (a : Aε) :
      Vε.right.residueEquiv (IsLocalRing.residue Vε.right (E' a)) =
        Aε.residueEquiv (IsLocalRing.residue Aε a) := by
    have h1 : Vε.right.residueEquiv (IsLocalRing.residue Vε.right (E' a))
        = (eModel (E a)).fst := rfl
    have h2 : (eModel (E a)).fst = (E a).fst :=
      TrivSqZeroExt.fst_map liftCoeff.toLinearMap (E a)
    rw [h1, h2]
    exact residueCorrectedDualNumberEquiv_fst hpair a
  let mHom : Aε ⟶ Vε.right := {
    hom := E'.toAlgHom
    isLocal := IsLocalHom.of_surjective E'.toRingEquiv.toRingHom
      E'.toRingEquiv.surjective
    residue_comm := hEres }
  let mInv : Vε.right ⟶ Aε := {
    hom := E'.symm.toAlgHom
    isLocal := IsLocalHom.of_surjective E'.symm.toRingEquiv.toRingHom
      E'.symm.toRingEquiv.surjective
    residue_comm := by
      intro a
      let a' : DΛ := a
      have hh' := hEres (E'.symm a')
      have hx : E' (E'.symm a') = a' := E'.apply_symm_apply a'
      have hxV : E' (E'.symm a') = a := hx
      rw [hxV] at hh'
      exact hh'.symm }
  let mArt : Aε ≅ Vε.right := {
    hom := mHom
    inv := mInv
    hom_inv_id := ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun a => E'.symm_apply_apply a)
    inv_hom_id := ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun a => E'.apply_symm_apply a) }
  have hscalar (z : k) :
      fModel (TrivSqZeroExt.inl z) = (algebraMap k D) z := by
    have hz : (TrivSqZeroExt.inl z : DualNumber k) = algebraMap k (DualNumber k) z := by
      simp [TrivSqZeroExt.algebraMap_eq_inl']
    rw [hz]
    exact fModel.commutes z
  have hmcomm : Uε.hom ≫ mArt.hom = Vε.hom := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro a
    change E' (g.hom ((eqToHom hbase).hom a)) =
      (residueAlgebraStructure Λ k D).hom ((eqToHom hbase).hom a)
    have hinc := congrArg (fun f => f ((eqToHom hbase).hom a))
      (residueCorrectedDualNumberEquiv_comp_inclusion hpair)
    change E (g.hom ((eqToHom hbase).hom a)) = _ at hinc
    change eModel (E (g.hom ((eqToHom hbase).hom a))) = _
    rw [hinc]
    exact hscalar _
  let m : Uε ≅ Vε := Under.isoMk mArt hmcomm
  let e0 : (restrictResidueAlgebra Λ k (residueFieldObject.{w, v, w} k k)).carrier ≃ₐ[Λ]
      (residueFieldObject.{u, v, w} Λ k).carrier :=
    AlgEquiv.ofRingEquiv (R := Λ) (f := RingEquiv.refl _) (fun _ => rfl)
  have e0res (a : V₀.right) :
      (residueFieldObject.{u, v, w} Λ k).residueEquiv
          (IsLocalRing.residue _ (e0 a)) =
        V₀.right.residueEquiv (IsLocalRing.residue V₀.right a) := by
    have hleft :
        (residueFieldObject.{u, v, w} Λ k).residueEquiv
            (IsLocalRing.residue _ (e0 a)) = (e0 a).down := by
      simp only [e0, residueFieldObject, IsLocalRing.residue_def]
      rfl
    have hright :
        V₀.right.residueEquiv (IsLocalRing.residue V₀.right a) = a.down := by
      change (residueFieldObject.{w, v, w} k k).residueEquiv
        (IsLocalRing.residue _ a) = a.down
      simp only [residueFieldObject]
      rfl
    rw [hleft, hright]
    rfl
  let m0Inv : V₀.right ⟶ U₀.right := {
    hom := e0.toAlgHom
    isLocal := IsLocalHom.of_surjective e0.toRingEquiv.toRingHom
      e0.toRingEquiv.surjective
    residue_comm := by
      intro a
      change U₀.right.residueEquiv (IsLocalRing.residue U₀.right (e0 a)) = _
      exact e0res a }
  have hm0res (a : U₀.right) :
      V₀.right.residueEquiv (IsLocalRing.residue V₀.right
        ((residueAlgebraStructure Λ k k₀).hom a)) =
        U₀.right.residueEquiv (IsLocalRing.residue U₀.right a) :=
    (residueAlgebraStructure Λ k k₀).residue_comm a
  let m0Hom : U₀.right ⟶ V₀.right := {
    hom := (residueAlgebraStructure Λ k k₀).hom
    isLocal := IsLocalHom.of_surjective
      (residueAlgebraStructure Λ k k₀).hom.toRingHom
      (by
        intro b
        refine ⟨e0 b, ?_⟩
        change (algebraMap k k₀) (ULift.algEquiv (R := Λ) (A := k) b) = b
        apply ULift.ext
        rfl)
    residue_comm := hm0res }
  let m0Art : U₀.right ≅ V₀.right := {
    hom := m0Hom
    inv := m0Inv
    hom_inv_id := by
      apply ArtinianLocalAlgCat.hom_ext
      apply AlgHom.ext
      intro a
      change e0 ((residueAlgebraStructure Λ k k₀).hom a) = a
      apply ULift.ext
      rfl
    inv_hom_id := by
      apply ArtinianLocalAlgCat.hom_ext
      apply AlgHom.ext
      intro a
      change (residueAlgebraStructure Λ k k₀).hom (e0 a) = a
      apply ULift.ext
      rfl }
  have hm0comm : U₀.hom ≫ m0Art.hom = V₀.hom := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro a
    simp [U₀, V₀, m0Art, m0Hom, baseChange, residueAlgebrasToUnder,
      residueAlgebraStructure]
  let m₀ : U₀ ≅ V₀ := Under.isoMk m0Art hm0comm
  have hsq : r ≫ m₀.hom = m.hom ≫ d := by
    apply Under.UnderMorphism.ext
    have hm₀iso : IsIso (Under.Hom.right m₀.inv) :=
      ⟨⟨Under.Hom.right m₀.hom,
        congrArg Under.Hom.right m₀.inv_hom_id,
        congrArg Under.Hom.right m₀.hom_inv_id⟩⟩
    apply (cancel_mono (Under.Hom.right m₀.inv)).1
    have huniq : e = m.hom.right ≫ d.right ≫ m₀.inv.right := by
      have he := eq_residueFieldMorphism e
      have hc := eq_residueFieldMorphism
        (m.hom.right ≫ d.right ≫ m₀.inv.right)
      exact he.trans hc.symm
    calc
      (r.right ≫ m₀.hom.right) ≫ m₀.inv.right = e := by
        rw [Category.assoc]
        simp [r]
      _ = m.hom.right ≫ d.right ≫ m₀.inv.right := huniq
      _ = (m.hom.right ≫ d.right) ≫ m₀.inv.right := (Category.assoc _ _ _).symm
  have htransport (a : Aut (P.obj Uε)) :
      P.transportAutHom d (P.transportAutHom m.hom a) =
        P.transportAutHom m₀.hom (P.transportAutHom r a) := by
    change P.transportAut d (P.transportAut m.hom a) =
      P.transportAut m₀.hom (P.transportAut r a)
    rw [← P.transportAut_comp, ← P.transportAut_comp, hsq]
  let eKernel :
      infinitesimalAutomorphisms hp g e hpair (P.map j)
          (P.map_isHomLift j) ≃
        {a : Aut (P.obj Vε) // P.transportAutHom d a = 1} := by
    have hinf := infinitesimalAutomorphisms_eq_tangentFiber hp P g e hpair hbase
    change _ = MonoidHom.ker (P.transportAutHom r) at hinf
    refine {
      toFun := fun a => ⟨P.transportAutHom m.hom a.1, ?_⟩
      invFun := fun b => ⟨P.transportAutHom m.inv b.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
    · have ha : P.transportAutHom r a.1 = 1 := by
        change a.1 ∈ MonoidHom.ker (P.transportAutHom r)
        rw [← hinf]
        exact a.2
      change P.transportAutHom d (P.transportAutHom m.hom a.1) = 1
      rw [htransport, ha]
      simp
    · have hb : P.transportAutHom d b.1 = 1 := b.2
      have hback (z : Aut (P.obj Vε)) :
          P.transportAutHom r (P.transportAutHom m.inv z) =
            P.transportAutHom m₀.inv (P.transportAutHom d z) := by
        change P.transportAut r (P.transportAut m.inv z) =
          P.transportAut m₀.inv (P.transportAut d z)
        rw [← P.transportAut_comp, ← P.transportAut_comp]
        congr 1
        apply (cancel_mono m₀.hom).1
        calc
          (m.inv ≫ r) ≫ m₀.hom = m.inv ≫ (r ≫ m₀.hom) := Category.assoc _ _ _
          _ = m.inv ≫ (m.hom ≫ d) := by rw [hsq]
          _ = (m.inv ≫ m.hom) ≫ d := (Category.assoc _ _ _).symm
          _ = d := by simp
          _ = (d ≫ m₀.inv) ≫ m₀.hom := by simp
      rw [hinf]
      change P.transportAutHom r (P.transportAutHom m.inv b.1) = 1
      rw [hback, hb]
      simp
    · intro a
      apply Subtype.ext
      change P.transportAut m.inv (P.transportAut m.hom a.1) = a.1
      rw [← P.transportAut_comp]
      simp
    · intro b
      apply Subtype.ext
      change P.transportAut m.hom (P.transportAut m.inv b.1) = b.1
      rw [← P.transportAut_comp]
      simp
  exact eKernel.trans htangentKernel.symm

end

end Deformation
