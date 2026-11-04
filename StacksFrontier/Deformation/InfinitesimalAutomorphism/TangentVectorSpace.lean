module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.BaseCategory.IdealQuotient
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Tangent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The vector-space structure on the tangent space of the automorphism functor (Stacks 06JV)

Let `𝓕` be a category cofibered in groupoids over `𝒞_Λ` satisfying (RS), let `x` be an object
of `𝓕` over `A`, and let `x₀` be a pushforward of `x` to the special fibre. Tag 06JT's
automorphism functor `Aut(x) : 𝒞_A → Sets`, localized at the identity of `x₀`, has a tangent
space at that point, built in `StacksFrontier.Deformation.InfinitesimalAutomorphism.Tangent` and
identified there with the group of infinitesimal automorphisms of the dual-number pushforward
of `x`. This file puts the `k`-vector space structure on it and compares it with the tangent
space of `Aut(x₀)`.

The Stacks proof of part (1) runs through the localized functor `F = Aut(x)_{id}`, a
deformation functor by Tags 06JU and 06JC, whose tangent space `F(k[ε])` carries the natural
vector-space structure of Tag 06IA; addition there is the composition
`F(k[ε]) × F(k[ε]) ≃ F(k[ε] ×_k k[ε]) → F(k[ε])`, whose first map is the inverse of the
bijection (RS) supplies and whose second is induced by `ε ↦ (ε, ε)`. The proof here is that
composition read off directly on infinitesimal automorphisms: `k[ε] ×_k k[ε]` is the
square-zero extension by a rank-two module, (RS) for `p` itself makes the square of chosen
pushforwards over its two coordinates a fibre square, and the resulting addition is a
homomorphism for composition with composition's unit as a two-sided unit — so by
Eckmann–Hilton the two agree and composition is commutative. The scalar action is the
transport along `ε ↦ cε`, and `(c + d)ε` factors through the coordinate pair `(cε, dε)`,
which is what makes the action additive in the scalar.

Part (2) is the unwinding of definitions: `j : x ⟶ x₀` is cocartesian, so the dual-number
pushforwards of `x` and of `x₀` agree up to a unique isomorphism lying over the identity of
the dual-number ring, and conjugation by it is the comparison.

## Main results

* `Deformation.exists_naturalLocalizedAutomorphismTangentVectorSpace`: **Stacks 06JV (1)**.
* `Deformation.existsUnique_localizedTangentAutomorphismLinearEquiv`: **Stacks 06JV (2)**.

## Main definitions

* `Deformation.naturalLocalizedTangentAddCommGroup`,
  `Deformation.naturalLocalizedTangentModule`: the chosen vector-space structure, with
  `Deformation.naturalLocalizedTangentModule_spec` recording its two defining properties.
* `Deformation.canonicalLocalizedTangentAutomorphismLinearEquiv`: the pinned comparison of
  part (2).
* `Deformation.squareZeroAlgFunctor`, `Deformation.squareZeroAlgRed`: the finite-dimensional
  square-zero extensions of the residue field, as algebras under a fixed object of `𝒞_Λ`,
  and their reduction to the residue field.
* `Deformation.squareZeroUnder`, `Deformation.squareZeroUnderMap`,
  `Deformation.squareZeroUnderRed`: the same extensions, the coordinate maps and the
  reduction, read under the base of `x`, which is the shape
  `Deformation.ChosenPushforwardsAt` and Tag 06JT's automorphism functor take.

## Implementation notes

The vector-space structure is produced as an existence statement and then selected, because
addition and the scalar action are pinned only through the representative-level
identification `Deformation.localizedTangentEquivKernel` of the tangent space with the group
of infinitesimal automorphisms; transporting the structure along that equivalence is what
makes the two pinning clauses hold.

`isPullback_of_carrier` reduces a pullback square in `𝒞_Λ` to the underlying square of sets,
using Tag 06GH's concrete fibre product; it is the only place where the ring-theoretic shape
of `k[ε] ×_k k[ε]` is used.

## References

* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
-/

@[expose] public section

namespace Deformation

open CategoryTheory IsLocalRing CategoryTheory.Limits

universe u v w u₁ v₁

/-! ### The rank-one and rank-two square-zero coordinates -/

section Line

variable (k : Type w) [Field k]

/-- The rank-one module over the residue field, in the carrier universe of the dual
numbers. -/
private noncomputable abbrev tgtLine : FGModuleCat.{max v w} k := FGModuleCat.of k (ULift.{v} k)

/-- The rank-two module over the residue field. -/
private noncomputable abbrev tgtPlane : FGModuleCat.{max v w} k :=
  FGModuleCat.of k (ULift.{v} k × ULift.{v} k)

/-- The zero module over the residue field. -/
private noncomputable abbrev tgtZero : FGModuleCat.{max v w} k :=
  FGModuleCat.of k PUnit.{max v w + 1}

/-- First coordinate. -/
private noncomputable abbrev lineFst : tgtPlane.{v, w} k ⟶ tgtLine.{v, w} k :=
  FGModuleCat.ofHom (LinearMap.fst k (ULift.{v} k) (ULift.{v} k))

/-- Second coordinate. -/
private noncomputable abbrev lineSnd : tgtPlane.{v, w} k ⟶ tgtLine.{v, w} k :=
  FGModuleCat.ofHom (LinearMap.snd k (ULift.{v} k) (ULift.{v} k))

/-- Sum of the two coordinates. -/
private noncomputable abbrev lineAdd : tgtPlane.{v, w} k ⟶ tgtLine.{v, w} k :=
  FGModuleCat.ofHom (LinearMap.coprod (LinearMap.id (R := k) (M := ULift.{v} k)) LinearMap.id)

/-- First inclusion. -/
private noncomputable abbrev lineInl : tgtLine.{v, w} k ⟶ tgtPlane.{v, w} k :=
  FGModuleCat.ofHom (LinearMap.inl k (ULift.{v} k) (ULift.{v} k))

/-- Second inclusion. -/
private noncomputable abbrev lineInr : tgtLine.{v, w} k ⟶ tgtPlane.{v, w} k :=
  FGModuleCat.ofHom (LinearMap.inr k (ULift.{v} k) (ULift.{v} k))

/-- Scaling of the infinitesimal coordinate. -/
private noncomputable abbrev lineScale (c : k) : tgtLine.{v, w} k ⟶ tgtLine.{v, w} k :=
  FGModuleCat.ofHom (c • LinearMap.id : ULift.{v} k →ₗ[k] ULift.{v} k)

/-- The pair of two scalings. -/
private noncomputable abbrev linePair (c d : k) : tgtLine.{v, w} k ⟶ tgtPlane.{v, w} k :=
  FGModuleCat.ofHom (LinearMap.prod (c • LinearMap.id : ULift.{v} k →ₗ[k] ULift.{v} k)
    (d • LinearMap.id : ULift.{v} k →ₗ[k] ULift.{v} k))

private theorem lineInl_fst : lineInl.{v, w} k ≫ lineFst k = 𝟙 _ := by
  apply FGModuleCat.hom_ext; exact LinearMap.ext fun _ => rfl

private theorem lineInl_snd : lineInl.{v, w} k ≫ lineSnd k = 0 := by
  apply FGModuleCat.hom_ext; exact LinearMap.ext fun _ => rfl

private theorem lineInl_add : lineInl.{v, w} k ≫ lineAdd k = 𝟙 _ := by
  apply FGModuleCat.hom_ext; exact LinearMap.ext fun t => by change t + 0 = t; simp

private theorem lineInr_fst : lineInr.{v, w} k ≫ lineFst k = 0 := by
  apply FGModuleCat.hom_ext; exact LinearMap.ext fun _ => rfl

private theorem lineInr_snd : lineInr.{v, w} k ≫ lineSnd k = 𝟙 _ := by
  apply FGModuleCat.hom_ext; exact LinearMap.ext fun _ => rfl

private theorem lineInr_add : lineInr.{v, w} k ≫ lineAdd k = 𝟙 _ := by
  apply FGModuleCat.hom_ext; exact LinearMap.ext fun t => by change 0 + t = t; simp

private theorem linePair_fst (c d : k) : linePair.{v, w} k c d ≫ lineFst k = lineScale k c := by
  apply FGModuleCat.hom_ext; exact LinearMap.ext fun _ => rfl

private theorem linePair_snd (c d : k) : linePair.{v, w} k c d ≫ lineSnd k = lineScale k d := by
  apply FGModuleCat.hom_ext; exact LinearMap.ext fun _ => rfl

private theorem linePair_add (c d : k) :
    linePair.{v, w} k c d ≫ lineAdd k = lineScale k (c + d) := by
  apply FGModuleCat.hom_ext
  exact LinearMap.ext fun t => by change c • t + d • t = (c + d) • t; rw [add_smul]

private theorem lineScale_one : lineScale.{v, w} k 1 = 𝟙 _ := by
  apply FGModuleCat.hom_ext; exact LinearMap.ext fun t => by change (1 : k) • t = t; simp

private theorem lineScale_comp (c d : k) :
    lineScale.{v, w} k d ≫ lineScale k c = lineScale k (c * d) := by
  apply FGModuleCat.hom_ext
  exact LinearMap.ext fun t => by change c • d • t = (c * d) • t; rw [smul_smul]

private theorem lineScale_zero : lineScale.{v, w} k 0 = 0 := by
  apply FGModuleCat.hom_ext; exact LinearMap.ext fun t => by change (0 : k) • t = 0; simp

end Line

/-! ### Square-zero extensions as algebras under the base -/

section Under

local instance mopI {k : Type w} [Field k] (V : FGModuleCat.{max v w} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

local instance csI {k : Type w} [Field k] (V : FGModuleCat.{max v w} k) :
    IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The finite-dimensional square-zero extensions of `k`, as algebras under `A`. -/
public noncomputable def squareZeroAlgFunctor (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) :
    FGModuleCat.{max v w} k ⥤ Under A :=
  letI := residueAlgebra A
  squareZeroExtensionArtinian ↥A k ⋙ algebrasUnder A

/-- Reduction of a square-zero extension to the residue field, as algebras under `A`. -/
public noncomputable def squareZeroAlgRed (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (M : FGModuleCat.{max v w} k) :
    (squareZeroAlgFunctor.{u, v, w} A).obj M ⟶
      (letI := residueAlgebra A
       (algebrasUnder A).obj (residueFieldObject.{max v w, v, w} ↥A k)) :=
  letI := residueAlgebra A
  (algebrasUnder A).map (residueMorphism ((squareZeroExtensionArtinian ↥A k).obj M))

/-- Reduction is compatible with every linear map of coordinate modules. -/
public theorem squareZeroAlgFunctor_map_red (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    {M N : FGModuleCat.{max v w} k} (f : M ⟶ N) :
    (squareZeroAlgFunctor.{u, v, w} A).map f ≫ squareZeroAlgRed A N = squareZeroAlgRed A M := by
  let _ := residueAlgebra A
  change (algebrasUnder A).map _ ≫ (algebrasUnder A).map _ = (algebrasUnder A).map _
  rw [← Functor.map_comp]
  exact congrArg (algebrasUnder A).map (hom_residueFieldObject_ext _ _)

/-- The first coordinate of a square-zero extension is unchanged by a linear map of
coordinate modules. -/
public theorem squareZeroAlgFunctor_map_fst (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    {M N : FGModuleCat.{max v w} k} (f : M ⟶ N) (b : TrivSqZeroExt k ↥M) :
    TrivSqZeroExt.fst (((squareZeroAlgFunctor.{u, v, w} A).map f).right.hom b) =
      TrivSqZeroExt.fst b := by
  change TrivSqZeroExt.fst (TrivSqZeroExt.map (ModuleCat.Hom.hom f.hom) b) = _
  exact TrivSqZeroExt.fst_map _ _

/-- The second coordinate of a square-zero extension transforms by the given linear map. -/
public theorem squareZeroAlgFunctor_map_snd (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    {M N : FGModuleCat.{max v w} k} (f : M ⟶ N) (b : TrivSqZeroExt k ↥M) :
    TrivSqZeroExt.snd (((squareZeroAlgFunctor.{u, v, w} A).map f).right.hom b) =
      (ModuleCat.Hom.hom f.hom) (TrivSqZeroExt.snd b) := by
  change TrivSqZeroExt.snd (TrivSqZeroExt.map (ModuleCat.Hom.hom f.hom) b) = _
  exact TrivSqZeroExt.snd_map _ _

/-- The underlying map of a transport along an equality of objects is surjective. -/
public theorem surjective_hom_eqToHom {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (h : A = B) :
    Function.Surjective (eqToHom h).hom := by
  subst h; exact fun b => ⟨b, rfl⟩

/-- A commuting square in `𝒞_Λ` over a surjection is a pullback square as soon as its
underlying square of sets is: the two projections are jointly injective, and every
compatible pair of elements lies in their joint image. -/
public theorem isPullback_of_carrier
    {P A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (q₁ : P ⟶ A₁) (q₂ : P ⟶ A₂) (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hcomm : q₁ ≫ f₁ = q₂ ≫ f₂)
    (hsurj : Function.Surjective f₁.hom ∨ Function.Surjective f₂.hom)
    (hinj : ∀ z z' : P, q₁.hom z = q₁.hom z' → q₂.hom z = q₂.hom z' → z = z')
    (hsur : ∀ (a : A₁) (b : A₂), f₁.hom a = f₂.hom b →
      ∃ z : P, q₁.hom z = a ∧ q₂.hom z = b) :
    IsPullback q₁ q₂ f₁ f₂ := by
  classical
  have hpb := ArtinianLocalAlgCat.isPullback_of_surjective f₁ f₂ hsurj
  set e := hpb.lift q₁ q₂ hcomm with hedef
  have he₁ : e ≫ ArtinianLocalAlgCat.pullbackFst_of_surjective f₁ f₂ hsurj = q₁ :=
    hpb.lift_fst q₁ q₂ hcomm
  have he₂ : e ≫ ArtinianLocalAlgCat.pullbackSnd_of_surjective f₁ f₂ hsurj = q₂ :=
    hpb.lift_snd q₁ q₂ hcomm
  have hv₁ : ∀ z : P, (show ↥(AlgHom.pullback f₁.hom f₂.hom) from e.hom z).val.1 =
      q₁.hom z := by
    intro z
    refine Eq.trans ?_ (congrArg (fun g : P ⟶ A₁ => g.hom z) he₁)
    change _ = (ArtinianLocalAlgCat.pullbackFst_of_surjective f₁ f₂ hsurj).hom (e.hom z)
    rw [ArtinianLocalAlgCat.pullbackFst_of_surjective_hom]
    rfl
  have hv₂ : ∀ z : P, (show ↥(AlgHom.pullback f₁.hom f₂.hom) from e.hom z).val.2 =
      q₂.hom z := by
    intro z
    refine Eq.trans ?_ (congrArg (fun g : P ⟶ A₂ => g.hom z) he₂)
    change _ = (ArtinianLocalAlgCat.pullbackSnd_of_surjective f₁ f₂ hsurj).hom (e.hom z)
    rw [ArtinianLocalAlgCat.pullbackSnd_of_surjective_hom]
    rfl
  have hbij : Function.Bijective e.hom := by
    refine ⟨fun z z' hzz => hinj z z' ?_ ?_, fun y => ?_⟩
    · rw [← hv₁ z, ← hv₁ z', hzz]
    · rw [← hv₂ z, ← hv₂ z', hzz]
    · obtain ⟨z, hz₁, hz₂⟩ := hsur
        (show ↥(AlgHom.pullback f₁.hom f₂.hom) from y).val.1
        (show ↥(AlgHom.pullback f₁.hom f₂.hom) from y).val.2
        (show ↥(AlgHom.pullback f₁.hom f₂.hom) from y).2
      exact ⟨z, Subtype.ext (Prod.ext ((hv₁ z).trans hz₁) ((hv₂ z).trans hz₂))⟩
  have _ : IsIso e := ArtinianLocalAlgCat.isIso_of_bijective_hom e hbij
  refine hpb.of_iso' (asIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa using he₁
  · simpa using he₂
  · simp
  · simp

/-- The two coordinates exhibit the rank-two square-zero extension as the fibre product of
two copies of the dual numbers over the residue field. -/
private theorem isPullback_tgtPlane (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) :
    IsPullback ((squareZeroAlgFunctor.{u, v, w} A).map (lineFst.{v, w} k)).right
      ((squareZeroAlgFunctor.{u, v, w} A).map (lineSnd.{v, w} k)).right
      (squareZeroAlgRed.{u, v, w} A (tgtLine.{v, w} k)).right
      (squareZeroAlgRed.{u, v, w} A (tgtLine.{v, w} k)).right := by
  refine isPullback_of_carrier _ _ _ _ ?_ (Or.inl ?_) ?_ ?_
  · exact (congrArg Under.Hom.right
      (squareZeroAlgFunctor_map_red.{u, v, w} A (lineFst.{v, w} k))).trans
      (congrArg Under.Hom.right
        (squareZeroAlgFunctor_map_red.{u, v, w} A (lineSnd.{v, w} k))).symm
  · exact fun c => ⟨TrivSqZeroExt.inl c.down, rfl⟩
  · intro z z' h1 h2
    refine TrivSqZeroExt.ext ?_ (Prod.ext ?_ ?_)
    · exact ((squareZeroAlgFunctor_map_fst.{u, v, w} A (lineFst.{v, w} k) z).symm.trans
        (congrArg TrivSqZeroExt.fst h1)).trans
        (squareZeroAlgFunctor_map_fst.{u, v, w} A (lineFst.{v, w} k) z')
    · exact ((squareZeroAlgFunctor_map_snd.{u, v, w} A (lineFst.{v, w} k) z).symm.trans
        (congrArg TrivSqZeroExt.snd h1)).trans
        (squareZeroAlgFunctor_map_snd.{u, v, w} A (lineFst.{v, w} k) z')
    · exact ((squareZeroAlgFunctor_map_snd.{u, v, w} A (lineSnd.{v, w} k) z).symm.trans
        (congrArg TrivSqZeroExt.snd h2)).trans
        (squareZeroAlgFunctor_map_snd.{u, v, w} A (lineSnd.{v, w} k) z')
  · intro a b hab
    have hfst : TrivSqZeroExt.fst a = TrivSqZeroExt.fst b :=
      congrArg ULift.down (hab : ULift.up (TrivSqZeroExt.fst a) = ULift.up (TrivSqZeroExt.fst b))
    obtain ⟨z, hz1, hz2⟩ :
        ∃ z : ↥((squareZeroAlgFunctor.{u, v, w} A).obj (tgtPlane.{v, w} k)).right,
        TrivSqZeroExt.fst z = TrivSqZeroExt.fst a ∧
          TrivSqZeroExt.snd z = (TrivSqZeroExt.snd a, TrivSqZeroExt.snd b) :=
      ⟨((TrivSqZeroExt.fst a, (TrivSqZeroExt.snd a, TrivSqZeroExt.snd b)) :
        TrivSqZeroExt k (ULift.{v} k × ULift.{v} k)), rfl, rfl⟩
    refine ⟨z, TrivSqZeroExt.ext ?_ ?_, TrivSqZeroExt.ext ?_ ?_⟩
    · exact (squareZeroAlgFunctor_map_fst.{u, v, w} A (lineFst.{v, w} k) z).trans hz1
    · exact (squareZeroAlgFunctor_map_snd.{u, v, w} A (lineFst.{v, w} k) z).trans
        (congrArg (fun m => (ModuleCat.Hom.hom (lineFst.{v, w} k).hom) m) hz2)
    · exact ((squareZeroAlgFunctor_map_fst.{u, v, w} A (lineSnd.{v, w} k) z).trans hz1).trans hfst
    · exact (squareZeroAlgFunctor_map_snd.{u, v, w} A (lineSnd.{v, w} k) z).trans
        (congrArg (fun m => (ModuleCat.Hom.hom (lineSnd.{v, w} k).hom) m) hz2)

/-- The reduction of the residue-field object itself is an isomorphism, so the residue field
is the square-zero extension by the zero module. -/
public theorem isIso_squareZeroAlgRed_zero (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) :
    IsIso ((squareZeroAlgRed.{u, v, w} A (FGModuleCat.of k PUnit.{max v w + 1})).right) := by
  refine ArtinianLocalAlgCat.isIso_of_bijective_hom _
    ⟨fun z z' hzz => ?_, fun c => ⟨TrivSqZeroExt.inl c.down, rfl⟩⟩
  refine TrivSqZeroExt.ext (congrArg ULift.down hzz) (Subsingleton.elim _ _)

end Under

/-! ### Membership in the kernel of a transport -/

section Transport

universe u₂ v₂

variable {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]
  {p : F ⥤ C} {x : F} (P : ChosenPushforwardsAt p x)

/-- **Membership in the kernel of a transport, over an arbitrary base category.** An
automorphism of a chosen pushforward dies under transport along `f` exactly when it commutes
with the canonical arrow between the two chosen pushforwards. -/
public theorem mem_ker_transportAutHom_iff {A B : Under (p.obj x)}
    (f : A ⟶ B) (a : Aut (P.obj A)) :
    a ∈ MonoidHom.ker (P.transportAutHom f) ↔ a.hom.val ≫ P.map f = P.map f := by
  constructor
  · intro ha
    have h' : P.transportHom f a = 𝟙 (P.obj B).1 :=
      congrArg (fun b : Aut (P.obj B) => b.hom.val) (MonoidHom.mem_ker.mp ha)
    calc a.hom.val ≫ P.map f = P.map f ≫ P.transportHom f a :=
          (P.map_transportHom f a).symm
      _ = P.map f ≫ 𝟙 (P.obj B).1 := by rw [h']
      _ = P.map f := Category.comp_id _
  · intro ha
    refine MonoidHom.mem_ker.mpr ?_
    apply Aut.ext
    apply Functor.Fiber.hom_ext
    change P.transportHom f a = 𝟙 (P.obj B).1
    let _ := P.map_cocartesian f
    let _ := P.transportHom_isHomLift f a
    let _ : p.IsHomLift (𝟙 B.right) (𝟙 (P.obj B).1) :=
      CategoryTheory.IsHomLift.id (P.obj B).2
    apply Functor.IsStronglyCocartesian.ext p f.right (P.map f) (𝟙 B.right)
    rw [P.map_transportHom f a, ha, Category.comp_id]

end Transport

/-! ### Pushforwards along the square-zero coordinates -/

section Pushforward

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F]

/-- The square-zero extension by `M`, as an object under the base of `x`. -/
public noncomputable def squareZeroUnder
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (x : F)
    (M : FGModuleCat.{max v w} k) : Under (p.obj x) :=
  (squareZeroAlgFunctor.{u, v, w} (p.obj x)).obj M

/-- A linear map of coordinate modules, as an arrow under the base of `x`. -/
public noncomputable def squareZeroUnderMap
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (x : F)
    {M N : FGModuleCat.{max v w} k} (f : M ⟶ N) :
    squareZeroUnder p x M ⟶ squareZeroUnder p x N :=
  (squareZeroAlgFunctor.{u, v, w} (p.obj x)).map f

/-- Reduction of the square-zero extension by `M` to the residue field, as an arrow under the
base of `x`. -/
public noncomputable def squareZeroUnderRed
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (x : F)
    (M : FGModuleCat.{max v w} k) :
    squareZeroUnder p x M ⟶ specialFibreUnder (p := p) (x := x) :=
  squareZeroAlgRed.{u, v, w} (p.obj x) M

variable {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} {x : F}
  (P : ChosenPushforwardsAt p x)

/-- Transport of a fibre automorphism is characterized by the commuting square it makes with
the canonical arrow between the two pushforwards. -/
public theorem transportAut_eq_iff {A B : Under (p.obj x)} (f : A ⟶ B)
    (γ : Aut (P.obj A)) (δ : Aut (P.obj B)) :
    P.transportAut f γ = δ ↔ γ.hom.val ≫ P.map f = P.map f ≫ δ.hom.val := by
  constructor
  · intro h
    have h' : P.transportHom f γ = δ.hom.val :=
      congrArg (fun a : Aut (P.obj B) => a.hom.val) h
    rw [← h']
    exact (P.map_transportHom f γ).symm
  · intro h
    apply Aut.ext
    apply Functor.Fiber.hom_ext
    change P.transportHom f γ = δ.hom.val
    let _ := P.map_cocartesian f
    let _ := P.transportHom_isHomLift f γ
    let _ : p.IsHomLift (𝟙 B.right) δ.hom.val := δ.hom.2
    apply Functor.IsStronglyCocartesian.ext p f.right (P.map f) (𝟙 B.right)
    rw [P.map_transportHom f γ, h]

/-- A fibre automorphism lies over the identity of the base. -/
public theorem p_map_aut {A : Under (p.obj x)} (α : Aut (P.obj A)) :
    p.map α.hom.val = 𝟙 (p.obj (P.obj A).1) := by
  let _ : p.IsHomLift (𝟙 A.right) α.hom.val := α.hom.2
  rw [IsHomLift.fac' p (𝟙 A.right) α.hom.val]
  simp

/-- The base of the canonical arrow between two chosen pushforwards. -/
public theorem p_map_P_map {A B : Under (p.obj x)} (f : A ⟶ B) :
    p.map (P.map f) =
      eqToHom (P.obj A).2 ≫ f.right ≫ eqToHom (P.obj B).2.symm :=
  IsHomLift.fac' p f.right (P.map f)

/-- The two coordinate projections of the plane pushforward agree after reduction. -/
private theorem planeCone_condition :
    P.map (squareZeroUnderMap p x (lineFst.{v, w} k)) ≫
        P.map (squareZeroUnderRed p x (tgtLine.{v, w} k)) =
      P.map (squareZeroUnderMap p x (lineSnd.{v, w} k)) ≫
        P.map (squareZeroUnderRed p x (tgtLine.{v, w} k)) := by
  rw [← P.map_comp, ← P.map_comp]
  exact congrArg P.map ((squareZeroAlgFunctor_map_red.{u, v, w} (p.obj x) (lineFst.{v, w} k)).trans
    (squareZeroAlgFunctor_map_red.{u, v, w} (p.obj x) (lineSnd.{v, w} k)).symm)

/-- The two coordinates exhibit the plane as the fibre product, read under the base of `x`. -/
private theorem isPullback_planeUnder :
    IsPullback (squareZeroUnderMap p x (lineFst.{v, w} k)).right
      (squareZeroUnderMap p x (lineSnd.{v, w} k)).right
      (squareZeroUnderRed p x (tgtLine.{v, w} k)).right
      (squareZeroUnderRed p x (tgtLine.{v, w} k)).right :=
  isPullback_tgtPlane.{u, v, w} (p.obj x)

/-- The image under `p` of the square of pushforwards is a pullback square. -/
private theorem isPullback_pushforward_base :
    IsPullback (p.map (P.map (squareZeroUnderMap p x (lineFst.{v, w} k))))
      (p.map (P.map (squareZeroUnderMap p x (lineSnd.{v, w} k))))
      (p.map (P.map (squareZeroUnderRed p x (tgtLine.{v, w} k))))
      (p.map (P.map (squareZeroUnderRed p x (tgtLine.{v, w} k)))) := by
  refine (isPullback_planeUnder (p := p) (x := x)).of_iso
    (eqToIso (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))).2.symm)
    (eqToIso (P.obj (squareZeroUnder p x (tgtLine.{v, w} k))).2.symm)
    (eqToIso (P.obj (squareZeroUnder p x (tgtLine.{v, w} k))).2.symm)
    (eqToIso (P.obj (specialFibreUnder (p := p) (x := x))).2.symm) ?_ ?_ ?_ ?_
  · rw [p_map_P_map P (squareZeroUnderMap p x (lineFst.{v, w} k))]; simp
  · rw [p_map_P_map P (squareZeroUnderMap p x (lineSnd.{v, w} k))]; simp
  · rw [p_map_P_map P (squareZeroUnderRed p x (tgtLine.{v, w} k))]; simp
  · rw [p_map_P_map P (squareZeroUnderRed p x (tgtLine.{v, w} k))]; simp

/-- Under (RS), the square of chosen pushforwards over the two coordinates is a pullback
square. -/
private theorem isLimit_planeCone (hp : SatisfiesRS p) :
    Nonempty (IsLimit (PullbackCone.mk
      (P.map (squareZeroUnderMap p x (lineFst.{v, w} k)))
      (P.map (squareZeroUnderMap p x (lineSnd.{v, w} k))) (planeCone_condition P))) := by
  refine isLimit_of_map_isLimit hp _ _ _ ?_ ⟨?_⟩
  · rw [p_map_P_map P (squareZeroUnderRed p x (tgtLine.{v, w} k))]
    exact surjective_hom_comp _ _ (surjective_hom_eqToHom _)
      (surjective_hom_comp _ _ (fun c => ⟨TrivSqZeroExt.inl c.down, rfl⟩)
        (surjective_hom_eqToHom _))
  · exact IsLimit.ofIsoLimit (isPullback_pushforward_base P).isLimit
      (PullbackCone.ext (Iso.refl _) (Category.id_comp _).symm (Category.id_comp _).symm)

/-- The unique automorphism of the plane pushforward whose two coordinate transports are
prescribed. This is the Rim-Schlessinger bijection used to add infinitesimal
automorphisms. -/
private theorem existsUnique_planeAut (hp : SatisfiesRS p)
    (α β : Aut (P.obj (squareZeroUnder p x (tgtLine.{v, w} k))))
    (hα : α.hom.val ≫ P.map (squareZeroUnderRed p x (tgtLine.{v, w} k)) =
      P.map (squareZeroUnderRed p x (tgtLine.{v, w} k)))
    (hβ : β.hom.val ≫ P.map (squareZeroUnderRed p x (tgtLine.{v, w} k)) =
      P.map (squareZeroUnderRed p x (tgtLine.{v, w} k))) :
    ∃! γ : Aut (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))),
      P.transportAut (squareZeroUnderMap p x (lineFst.{v, w} k)) γ = α ∧
        P.transportAut (squareZeroUnderMap p x (lineSnd.{v, w} k)) γ = β := by
  classical
  obtain ⟨hlim⟩ := isLimit_planeCone P hp
  have huniq : ∀ h h' : (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))).1 ⟶
        (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))).1,
      h ≫ P.map (squareZeroUnderMap p x (lineFst.{v, w} k)) =
        h' ≫ P.map (squareZeroUnderMap p x (lineFst.{v, w} k)) →
      h ≫ P.map (squareZeroUnderMap p x (lineSnd.{v, w} k)) =
        h' ≫ P.map (squareZeroUnderMap p x (lineSnd.{v, w} k)) → h = h' :=
    fun h h' e1 e2 => PullbackCone.IsLimit.hom_ext hlim e1 e2
  have hbase : ∀ g : (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))).1 ⟶
        (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))).1,
      p.map g ≫ p.map (P.map (squareZeroUnderMap p x (lineFst.{v, w} k))) =
        p.map (P.map (squareZeroUnderMap p x (lineFst.{v, w} k))) →
      p.map g ≫ p.map (P.map (squareZeroUnderMap p x (lineSnd.{v, w} k))) =
        p.map (P.map (squareZeroUnderMap p x (lineSnd.{v, w} k))) →
      p.IsHomLift (𝟙 (squareZeroUnder p x (tgtPlane.{v, w} k)).right) g := by
    intro g h1 h2
    have hid : p.map g = 𝟙 (p.obj (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))).1) := by
      refine PullbackCone.IsLimit.hom_ext (isPullback_pushforward_base P).isLimit ?_ ?_
      · exact h1.trans (Category.id_comp _).symm
      · exact h2.trans (Category.id_comp _).symm
    refine IsHomLift.of_fac' p (𝟙 (squareZeroUnder p x (tgtPlane.{v, w} k)).right) g
      (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))).2
      (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))).2 ?_
    rw [hid]
    simp
  have hlift : ∀ (f : tgtPlane.{v, w} k ⟶ tgtLine.{v, w} k)
      (c : Aut (P.obj (squareZeroUnder p x (tgtLine.{v, w} k))))
      (g : (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))).1 ⟶
        (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))).1),
      g ≫ P.map (squareZeroUnderMap p x f) = P.map (squareZeroUnderMap p x f) ≫ c.hom.val →
      p.map g ≫ p.map (P.map (squareZeroUnderMap p x f)) =
        p.map (P.map (squareZeroUnderMap p x f)) := by
    intro f c g h
    rw [← p.map_comp, h, p.map_comp, p_map_aut P c, Category.comp_id]
  have build : ∀ a b : Aut (P.obj (squareZeroUnder p x (tgtLine.{v, w} k))),
      a.hom.val ≫ P.map (squareZeroUnderRed p x (tgtLine.{v, w} k)) =
        P.map (squareZeroUnderRed p x (tgtLine.{v, w} k)) →
      b.hom.val ≫ P.map (squareZeroUnderRed p x (tgtLine.{v, w} k)) =
        P.map (squareZeroUnderRed p x (tgtLine.{v, w} k)) →
      ∃ g : (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))).1 ⟶
          (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))).1,
        p.IsHomLift (𝟙 (squareZeroUnder p x (tgtPlane.{v, w} k)).right) g ∧
        g ≫ P.map (squareZeroUnderMap p x (lineFst.{v, w} k)) =
          P.map (squareZeroUnderMap p x (lineFst.{v, w} k)) ≫ a.hom.val ∧
        g ≫ P.map (squareZeroUnderMap p x (lineSnd.{v, w} k)) =
          P.map (squareZeroUnderMap p x (lineSnd.{v, w} k)) ≫ b.hom.val := by
    intro a b ha hb
    have hcond : (P.map (squareZeroUnderMap p x (lineFst.{v, w} k)) ≫ a.hom.val) ≫
          P.map (squareZeroUnderRed p x (tgtLine.{v, w} k)) =
        (P.map (squareZeroUnderMap p x (lineSnd.{v, w} k)) ≫ b.hom.val) ≫
          P.map (squareZeroUnderRed p x (tgtLine.{v, w} k)) := by
      rw [Category.assoc, ha, Category.assoc, hb]
      exact planeCone_condition P
    obtain ⟨g, hl1, hl2⟩ : ∃ g : (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))).1 ⟶
          (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))).1,
        g ≫ P.map (squareZeroUnderMap p x (lineFst.{v, w} k)) =
            P.map (squareZeroUnderMap p x (lineFst.{v, w} k)) ≫ a.hom.val ∧
          g ≫ P.map (squareZeroUnderMap p x (lineSnd.{v, w} k)) =
            P.map (squareZeroUnderMap p x (lineSnd.{v, w} k)) ≫ b.hom.val :=
      ⟨PullbackCone.IsLimit.lift hlim _ _ hcond,
        PullbackCone.IsLimit.lift_fst hlim _ _ hcond,
        PullbackCone.IsLimit.lift_snd hlim _ _ hcond⟩
    exact ⟨g, hbase g (hlift _ a _ hl1) (hlift _ b _ hl2), hl1, hl2⟩
  have hinv : ∀ a : Aut (P.obj (squareZeroUnder p x (tgtLine.{v, w} k))),
      a.hom.val ≫ P.map (squareZeroUnderRed p x (tgtLine.{v, w} k)) =
        P.map (squareZeroUnderRed p x (tgtLine.{v, w} k)) →
      a.symm.hom.val ≫ P.map (squareZeroUnderRed p x (tgtLine.{v, w} k)) =
        P.map (squareZeroUnderRed p x (tgtLine.{v, w} k)) := fun a ha =>
    (mem_ker_transportAutHom_iff P _ a⁻¹).mp
      (inv_mem ((mem_ker_transportAutHom_iff P _ a).mpr ha))
  -- two compatible pairs of lifts are inverse to each other
  have hmul : ∀ (a b : Aut (P.obj (squareZeroUnder p x (tgtLine.{v, w} k))))
      (g g' : (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))).1 ⟶
        (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))).1),
      g ≫ P.map (squareZeroUnderMap p x (lineFst.{v, w} k)) =
        P.map (squareZeroUnderMap p x (lineFst.{v, w} k)) ≫ a.hom.val →
      g ≫ P.map (squareZeroUnderMap p x (lineSnd.{v, w} k)) =
        P.map (squareZeroUnderMap p x (lineSnd.{v, w} k)) ≫ b.hom.val →
      g' ≫ P.map (squareZeroUnderMap p x (lineFst.{v, w} k)) =
        P.map (squareZeroUnderMap p x (lineFst.{v, w} k)) ≫ a.symm.hom.val →
      g' ≫ P.map (squareZeroUnderMap p x (lineSnd.{v, w} k)) =
        P.map (squareZeroUnderMap p x (lineSnd.{v, w} k)) ≫ b.symm.hom.val →
      g ≫ g' = 𝟙 (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))).1 := by
    intro a b g g' h1 h2 h1' h2'
    have ha : a.hom.val ≫ a.symm.hom.val = 𝟙 (P.obj (squareZeroUnder p x (tgtLine.{v, w} k))).1 :=
      congrArg Subtype.val a.hom_inv_id
    have hb : b.hom.val ≫ b.symm.hom.val = 𝟙 (P.obj (squareZeroUnder p x (tgtLine.{v, w} k))).1 :=
      congrArg Subtype.val b.hom_inv_id
    refine huniq _ _ ?_ ?_
    · rw [Category.assoc, h1', ← Category.assoc, h1, Category.assoc, ha, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, h2', ← Category.assoc, h2, Category.assoc, hb, Category.comp_id,
        Category.id_comp]
  obtain ⟨g, hgl, hg1, hg2⟩ := build α β hα hβ
  obtain ⟨g', hgl', hg1', hg2'⟩ := build α.symm β.symm (hinv α hα) (hinv β hβ)
  have hgg := hmul α β g g' hg1 hg2 hg1' hg2'
  have hgg' := hmul α.symm β.symm g' g hg1' hg2' hg1 hg2
  refine ⟨⟨⟨g, hgl⟩, ⟨g', hgl'⟩, Functor.Fiber.hom_ext hgg, Functor.Fiber.hom_ext hgg'⟩,
    ⟨(transportAut_eq_iff P _ _ α).mpr hg1, (transportAut_eq_iff P _ _ β).mpr hg2⟩, ?_⟩
  intro γ' hγ'
  apply Aut.ext
  apply Functor.Fiber.hom_ext
  change γ'.hom.val = g
  refine huniq _ _ ?_ ?_
  · exact ((transportAut_eq_iff P _ γ' α).mp hγ'.1).trans hg1.symm
  · exact ((transportAut_eq_iff P _ γ' β).mp hγ'.2).trans hg2.symm

/-! ### The infinitesimal automorphisms form a vector space -/

/-- Composition of coordinate maps, read under the base of `x`. -/
public theorem squareZeroUnderMap_comp {M N Q : FGModuleCat.{max v w} k} (f : M ⟶ N)
    (g : N ⟶ Q) :
    squareZeroUnderMap p x (f ≫ g) = squareZeroUnderMap p x f ≫ squareZeroUnderMap p x g :=
  (squareZeroAlgFunctor.{u, v, w} (p.obj x)).map_comp f g

/-- The identity coordinate map, read under the base of `x`. -/
public theorem squareZeroUnderMap_id (M : FGModuleCat.{max v w} k) :
    squareZeroUnderMap p x (𝟙 M) = 𝟙 (squareZeroUnder p x M) :=
  (squareZeroAlgFunctor.{u, v, w} (p.obj x)).map_id M

/-- Reduction is compatible with every coordinate map, read under the base of `x`. -/
public theorem squareZeroUnderMap_red {M N : FGModuleCat.{max v w} k} (f : M ⟶ N) :
    squareZeroUnderMap p x f ≫ squareZeroUnderRed p x N = squareZeroUnderRed p x M :=
  squareZeroAlgFunctor_map_red.{u, v, w} (p.obj x) f

/-- Reduction from the square-zero extension by the zero module is an isomorphism. -/
public theorem isIso_squareZeroUnderRed_zero :
    IsIso (squareZeroUnderRed p x (FGModuleCat.of k PUnit.{max v w + 1})) := by
  let _ : IsIso ((Under.forget (p.obj x)).map
      (squareZeroUnderRed p x (FGModuleCat.of k PUnit.{max v w + 1}))) :=
    isIso_squareZeroAlgRed_zero.{u, v, w} (p.obj x)
  exact isIso_of_reflects_iso
    (squareZeroUnderRed p x (FGModuleCat.of k PUnit.{max v w + 1})) (Under.forget (p.obj x))

/-- Transport along a coordinate map, then reduction, is the reduction. -/
private theorem transportAut_red_map {M N : FGModuleCat.{max v w} k} (f : M ⟶ N)
    (a : Aut (P.obj (squareZeroUnder p x M))) :
    P.transportAut (squareZeroUnderRed p x N) (P.transportAut (squareZeroUnderMap p x f) a) =
      P.transportAut (squareZeroUnderRed p x M) a := by
  rw [← P.transportAut_comp, squareZeroUnderMap_red]

/-- Transporting along two coordinate maps in turn is transporting along their composite. -/
private theorem transportAut_map_map {M N Q : FGModuleCat.{max v w} k} (f : M ⟶ N) (g : N ⟶ Q)
    (a : Aut (P.obj (squareZeroUnder p x M))) :
    P.transportAut (squareZeroUnderMap p x g) (P.transportAut (squareZeroUnderMap p x f) a) =
      P.transportAut (squareZeroUnderMap p x (f ≫ g)) a := by
  rw [squareZeroUnderMap_comp, P.transportAut_comp]

/-- Transport along a map is multiplicative. -/
private theorem transportAut_mul {A B : Under (p.obj x)} (f : A ⟶ B) (a b : Aut (P.obj A)) :
    P.transportAut f (a * b) = P.transportAut f a * P.transportAut f b :=
  map_mul (P.transportAutHom f) a b

/-- An infinitesimal automorphism is killed by the zero endomorphism of the coordinate. -/
private theorem transportAut_lineZero (a : Aut (P.obj (squareZeroUnder p x (tgtLine.{v, w} k))))
    (ha : P.transportAut (squareZeroUnderRed p x (tgtLine.{v, w} k)) a = 1) :
    P.transportAut (squareZeroUnderMap p x (0 : tgtLine.{v, w} k ⟶ tgtLine.{v, w} k)) a = 1 := by
  let _ : IsIso (squareZeroUnderRed p x (tgtZero.{v, w} k)) :=
    isIso_squareZeroUnderRed_zero (p := p) (x := x) (k := k)
  have h1 : P.transportAut (squareZeroUnderRed p x (tgtZero.{v, w} k))
      (P.transportAut
        (squareZeroUnderMap p x (0 : tgtLine.{v, w} k ⟶ tgtZero.{v, w} k)) a) = 1 := by
    rw [transportAut_red_map]
    exact ha
  have h2 :
      P.transportAut (squareZeroUnderMap p x (0 : tgtLine.{v, w} k ⟶ tgtZero.{v, w} k)) a =
        1 := by
    have h3 := congrArg (P.transportAut (inv (squareZeroUnderRed p x (tgtZero.{v, w} k)))) h1
    rw [← P.transportAut_comp, IsIso.hom_inv_id, P.transportAut_id] at h3
    refine h3.trans ?_
    exact map_one (P.transportAutHom (inv (squareZeroUnderRed p x (tgtZero.{v, w} k))))
  have hz : (0 : tgtLine.{v, w} k ⟶ tgtLine.{v, w} k) =
      (0 : tgtLine.{v, w} k ⟶ tgtZero.{v, w} k) ≫ (0 : tgtZero.{v, w} k ⟶ tgtLine.{v, w} k) :=
    (zero_comp).symm
  rw [hz, squareZeroUnderMap_comp, P.transportAut_comp, h2]
  exact map_one
    (P.transportAutHom (squareZeroUnderMap p x (0 : tgtZero.{v, w} k ⟶ tgtLine.{v, w} k)))

/-- The scalar action preserves the kernel. -/
private theorem scale_mem_ker (c : k)
    (a : infinitesimalAutomorphismKernel P (squareZeroUnderRed p x (tgtLine.{v, w} k))) :
    P.transportAutHom (squareZeroUnderMap p x (lineScale.{v, w} k c)) a.1 ∈
      MonoidHom.ker (P.transportAutHom (squareZeroUnderRed p x (tgtLine.{v, w} k))) := by
  refine MonoidHom.mem_ker.mpr ?_
  change P.transportAut (squareZeroUnderRed p x (tgtLine.{v, w} k))
    (P.transportAut (squareZeroUnderMap p x (lineScale.{v, w} k c)) a.1) = 1
  rw [transportAut_red_map]
  exact MonoidHom.mem_ker.mp a.2

/-- The Rim-Schlessinger vector-space structure, in coordinate form. -/
private theorem kernel_vectorSpace_aux (hp : SatisfiesRS p) :
    ∃ G : AddCommGroup (infinitesimalAutomorphismKernel P
        (squareZeroUnderRed p x (tgtLine.{v, w} k))),
      letI := G
      ∃ _ : Module k (infinitesimalAutomorphismKernel P
          (squareZeroUnderRed p x (tgtLine.{v, w} k))),
        (∀ a b : infinitesimalAutomorphismKernel P (squareZeroUnderRed p x (tgtLine.{v, w} k)),
            (a + b).1 = a.1 * b.1) ∧
          ∀ (c : k) (a : infinitesimalAutomorphismKernel P
              (squareZeroUnderRed p x (tgtLine.{v, w} k))),
            (c • a).1 = P.transportAutHom (squareZeroUnderMap p x (lineScale.{v, w} k c)) a.1 := by
  classical
  -- the Rim-Schlessinger comparison, as a choice of plane automorphism
  have key : ∀ a b : infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (tgtLine.{v, w} k)),
      ∃! γ : Aut (P.obj (squareZeroUnder p x (tgtPlane.{v, w} k))),
        P.transportAut (squareZeroUnderMap p x (lineFst.{v, w} k)) γ = a.1 ∧
          P.transportAut (squareZeroUnderMap p x (lineSnd.{v, w} k)) γ = b.1 := fun a b =>
    existsUnique_planeAut P hp a.1 b.1 ((mem_ker_transportAutHom_iff P _ a.1).mp a.2)
      ((mem_ker_transportAutHom_iff P _ b.1).mp b.2)
  choose Γ hΓ using key
  -- the sum of two infinitesimal automorphisms
  have hsum_mem : ∀ a b : infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (tgtLine.{v, w} k)),
      P.transportAut (squareZeroUnderMap p x (lineAdd.{v, w} k)) (Γ a b) ∈
        MonoidHom.ker (P.transportAutHom (squareZeroUnderRed p x (tgtLine.{v, w} k))) := by
    intro a b
    refine MonoidHom.mem_ker.mpr ?_
    change P.transportAut (squareZeroUnderRed p x (tgtLine.{v, w} k))
      (P.transportAut (squareZeroUnderMap p x (lineAdd.{v, w} k)) (Γ a b)) = 1
    rw [transportAut_red_map]
    have h2 : P.transportAut (squareZeroUnderRed p x (tgtLine.{v, w} k))
        (P.transportAut (squareZeroUnderMap p x (lineFst.{v, w} k)) (Γ a b)) = 1 := by
      rw [(hΓ a b).1.1]; exact MonoidHom.mem_ker.mp a.2
    rwa [transportAut_red_map] at h2
  -- additivity of the comparison
  have hΓmul : ∀ a b a' b' : infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (tgtLine.{v, w} k)),
      Γ (a * a') (b * b') = Γ a b * Γ a' b' := by
    intro a b a' b'
    refine ((hΓ (a * a') (b * b')).2 _ ⟨?_, ?_⟩).symm
    · rw [transportAut_mul, (hΓ a b).1.1, (hΓ a' b').1.1]
      rfl
    · rw [transportAut_mul, (hΓ a b).1.2, (hΓ a' b').1.2]
      rfl
  -- unit laws for the comparison
  have hΓone_right : ∀ a : infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (tgtLine.{v, w} k)),
      Γ a 1 = P.transportAut (squareZeroUnderMap p x (lineInl.{v, w} k)) a.1 := by
    intro a
    refine ((hΓ a 1).2 _ ⟨?_, ?_⟩).symm
    · rw [transportAut_map_map, lineInl_fst, squareZeroUnderMap_id,
        P.transportAut_id]
    · rw [transportAut_map_map, lineInl_snd]
      exact transportAut_lineZero P a.1 (MonoidHom.mem_ker.mp a.2)
  have hΓone_left : ∀ b : infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (tgtLine.{v, w} k)),
      Γ 1 b = P.transportAut (squareZeroUnderMap p x (lineInr.{v, w} k)) b.1 := by
    intro b
    refine ((hΓ 1 b).2 _ ⟨?_, ?_⟩).symm
    · rw [transportAut_map_map, lineInr_fst]
      exact transportAut_lineZero P b.1 (MonoidHom.mem_ker.mp b.2)
    · rw [transportAut_map_map, lineInr_snd, squareZeroUnderMap_id,
        P.transportAut_id]
  have hsum_one_right : ∀ a : infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (tgtLine.{v, w} k)),
      P.transportAut (squareZeroUnderMap p x (lineAdd.{v, w} k)) (Γ a 1) = a.1 := by
    intro a
    rw [hΓone_right a, transportAut_map_map, lineInl_add,
      squareZeroUnderMap_id, P.transportAut_id]
  have hsum_one_left : ∀ b : infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (tgtLine.{v, w} k)),
      P.transportAut (squareZeroUnderMap p x (lineAdd.{v, w} k)) (Γ 1 b) = b.1 := by
    intro b
    rw [hΓone_left b, transportAut_map_map, lineInr_add,
      squareZeroUnderMap_id, P.transportAut_id]
  -- the Eckmann-Hilton step: the sum is the composition, which is therefore commutative
  have hsum_mul : ∀ a b : infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (tgtLine.{v, w} k)),
      P.transportAut (squareZeroUnderMap p x (lineAdd.{v, w} k)) (Γ a b) = a.1 * b.1 := by
    intro a b
    have h : Γ a b = Γ a 1 * Γ 1 b := by
      have := hΓmul a 1 1 b
      rwa [mul_one, one_mul] at this
    rw [h, transportAut_mul, hsum_one_right a, hsum_one_left b]
  have hcomm : ∀ a b : infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (tgtLine.{v, w} k)), a.1 * b.1 = b.1 * a.1 := by
    intro a b
    have h : Γ a b = Γ 1 b * Γ a 1 := by
      have := hΓmul 1 b a 1
      rwa [one_mul, mul_one] at this
    have h2 : P.transportAut (squareZeroUnderMap p x (lineAdd.{v, w} k)) (Γ a b) = b.1 * a.1 := by
      rw [h, transportAut_mul, hsum_one_left b, hsum_one_right a]
    exact (hsum_mul a b).symm.trans h2
  -- the scalar action
  have hpair : ∀ (c d : k) (a : infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (tgtLine.{v, w} k))),
      Γ ⟨P.transportAutHom (squareZeroUnderMap p x (lineScale.{v, w} k c)) a.1,
          scale_mem_ker P c a⟩
        ⟨P.transportAutHom (squareZeroUnderMap p x (lineScale.{v, w} k d)) a.1,
          scale_mem_ker P d a⟩ =
      P.transportAut (squareZeroUnderMap p x (linePair.{v, w} k c d)) a.1 := by
    intro c d a
    refine ((hΓ _ _).2 _ ⟨?_, ?_⟩).symm
    · rw [transportAut_map_map, linePair_fst]
      rfl
    · rw [transportAut_map_map, linePair_snd]
      rfl
  let CG : CommGroup (infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (tgtLine.{v, w} k))) :=
    { (inferInstance : Group (infinitesimalAutomorphismKernel P
        (squareZeroUnderRed p x (tgtLine.{v, w} k)))) with
      mul_comm := fun a b => Subtype.ext (hcomm a b) }
  let G : AddCommGroup (infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (tgtLine.{v, w} k))) :=
    Equiv.addCommGroup (Additive.ofMul (α := infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (tgtLine.{v, w} k))))
  have hadd : ∀ a b : infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (tgtLine.{v, w} k)), (a + b).1 = a.1 * b.1 := fun a b => rfl
  refine ⟨G, ?_⟩
  let SM : SMul k (infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (tgtLine.{v, w} k))) :=
    ⟨fun c a => ⟨P.transportAutHom (squareZeroUnderMap p x (lineScale.{v, w} k c)) a.1,
      scale_mem_ker P c a⟩⟩
  have hsmul : ∀ (c : k) (a : infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (tgtLine.{v, w} k))),
      (c • a).1 = P.transportAutHom (squareZeroUnderMap p x (lineScale.{v, w} k c)) a.1 :=
    fun c a => rfl
  let MA : MulAction k (infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (tgtLine.{v, w} k))) :=
    { one_smul := fun a => Subtype.ext (by
        rw [hsmul, lineScale_one, squareZeroUnderMap_id]
        exact P.transportAut_id _ _)
      mul_smul := fun c d a => Subtype.ext (by
        rw [hsmul, hsmul, hsmul]
        change P.transportAut (squareZeroUnderMap p x (lineScale.{v, w} k (c * d))) a.1 = _
        rw [← lineScale_comp, squareZeroUnderMap_comp, P.transportAut_comp]
        rfl) }
  let DMA : DistribMulAction k (infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (tgtLine.{v, w} k))) :=
    { smul_zero := fun c => Subtype.ext (by
        rw [hsmul]
        exact map_one (P.transportAutHom (squareZeroUnderMap p x (lineScale.{v, w} k c))))
      smul_add := fun c a b => Subtype.ext (by
        rw [hsmul, hadd, hadd, hsmul, hsmul]
        exact map_mul (P.transportAutHom (squareZeroUnderMap p x (lineScale.{v, w} k c))) _ _) }
  refine ⟨{ add_smul := fun c d a => Subtype.ext ?_, zero_smul := fun a => Subtype.ext ?_ },
    hadd, hsmul⟩
  · rw [hsmul, hadd, hsmul, hsmul]
    have h := hsum_mul ⟨P.transportAutHom (squareZeroUnderMap p x (lineScale.{v, w} k c)) a.1,
      scale_mem_ker P c a⟩ ⟨P.transportAutHom (squareZeroUnderMap p x (lineScale.{v, w} k d)) a.1,
      scale_mem_ker P d a⟩
    rw [hpair c d a, transportAut_map_map, linePair_add] at h
    exact h
  · rw [hsmul]
    change P.transportAut (squareZeroUnderMap p x (lineScale.{v, w} k 0)) a.1 = _
    rw [lineScale_zero]
    exact transportAut_lineZero P a.1 (MonoidHom.mem_ker.mp a.2)

/-- **The Rim-Schlessinger vector-space structure.** On the infinitesimal automorphisms of a
chosen pushforward, composition is commutative, and it is the addition of a `k`-vector space
whose scalar action is induced by scaling the infinitesimal coordinate. -/
private theorem kernel_vectorSpace (hp : SatisfiesRS p) :
    ∃ G : AddCommGroup (infinitesimalAutomorphismKernel P
        (tangentReduction (p := p) (x := x))),
      letI := G
      ∃ _ : Module k (infinitesimalAutomorphismKernel P
          (tangentReduction (p := p) (x := x))),
        (∀ a b : infinitesimalAutomorphismKernel P (tangentReduction (p := p) (x := x)),
            (a + b).1 = a.1 * b.1) ∧
          ∀ (c : k) (a : infinitesimalAutomorphismKernel P
              (tangentReduction (p := p) (x := x))),
            (c • a).1 = P.transportAutHom (tangentScaling (p := p) (x := x) c) a.1 :=
  kernel_vectorSpace_aux P hp

end Pushforward

/-! ### The tangent space of the automorphism functor -/

section Statements

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F]
  {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
  {x : F} (P : ChosenPushforwardsAt p x)

/-- **Stacks Project, Tag 06JV (1).** On the tangent space at the identity of the
automorphism functor of `x`, addition is composition of automorphisms and scalar
multiplication is induced by the canonical scaling of the dual-number coordinate; in
particular composition there is commutative. -/
@[stacks 06JV "part (1)",
  stacks 06JX "Inf_{x_0}(F) as the tangent space, with addition composition",
  sga "7 VI 2.6(c)" "Aut(1_ε) k-structure"]
public theorem exists_naturalLocalizedAutomorphismTangentVectorSpace
    (hp : SatisfiesRS p) :
    ∃ V : AddCommGroup (localizedAutomorphismFunctorTangent P),
      letI := V
      ∃ M : Module k (localizedAutomorphismFunctorTangent P),
        letI := M
        (∀ a b, localizedTangentEquivKernel P (a + b) =
          localizedTangentEquivKernel P a * localizedTangentEquivKernel P b) ∧
        (∀ (c : k) a, (localizedTangentEquivKernel P (c • a)).1 =
          P.transportAutHom (tangentScaling c) (localizedTangentEquivKernel P a).1) := by
  classical
  obtain ⟨G, M, hadd, hsmulK⟩ := kernel_vectorSpace P hp
  let _ := G
  let _ := M
  let E := localizedTangentEquivKernel P
  let VT : AddCommGroup (localizedAutomorphismFunctorTangent P) := Equiv.addCommGroup E
  have hEadd : ∀ a b : localizedAutomorphismFunctorTangent P, E (a + b) = E a + E b :=
    fun a b => E.apply_symm_apply _
  have hEzero : E 0 = 0 := E.apply_symm_apply _
  refine ⟨VT, ?_⟩
  let SMT : SMul k (localizedAutomorphismFunctorTangent P) :=
    ⟨fun c a => E.symm (c • E a)⟩
  have hEsmul : ∀ (c : k) (a : localizedAutomorphismFunctorTangent P),
      E (c • a) = c • E a := fun c a => E.apply_symm_apply _
  let MAT : MulAction k (localizedAutomorphismFunctorTangent P) :=
    { one_smul := fun a => E.injective (by simp only [hEsmul, one_smul])
      mul_smul := fun c d a => E.injective (by simp only [hEsmul, mul_smul]) }
  let DMAT : DistribMulAction k (localizedAutomorphismFunctorTangent P) :=
    { smul_zero := fun c => E.injective (by simp only [hEsmul, hEzero, smul_zero])
      smul_add := fun c a b => E.injective (by simp only [hEsmul, hEadd, smul_add]) }
  refine ⟨{ add_smul := fun c d a => E.injective (by simp only [hEsmul, hEadd, add_smul])
            zero_smul := fun a => E.injective (by simp only [hEsmul, hEzero, zero_smul]) },
    fun a b => (hEadd a b).trans (Subtype.ext (hadd (E a) (E b))),
    fun c a => (congrArg Subtype.val (hEsmul c a)).trans (hsmulK c (E a))⟩

/-- The natural additive group on the source tangent space. -/
@[instance_reducible]
public noncomputable def naturalLocalizedTangentAddCommGroup (hp : SatisfiesRS p) :
    AddCommGroup (localizedAutomorphismFunctorTangent P) :=
  Classical.choose (exists_naturalLocalizedAutomorphismTangentVectorSpace P hp)

/-- The natural scalar action on the source tangent space. -/
@[instance_reducible]
public noncomputable def naturalLocalizedTangentModule (hp : SatisfiesRS p) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    Module k (localizedAutomorphismFunctorTangent P) :=
  Classical.choose (Classical.choose_spec
    (exists_naturalLocalizedAutomorphismTangentVectorSpace P hp))

/-- The selected tangent structure has composition as addition and the canonical
scaling action. -/
public theorem naturalLocalizedTangentModule_spec (hp : SatisfiesRS p) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    (∀ a b, localizedTangentEquivKernel P (a + b) =
      localizedTangentEquivKernel P a * localizedTangentEquivKernel P b) ∧
    (∀ (c : k) a, (localizedTangentEquivKernel P (c • a)).1 =
      P.transportAutHom (tangentScaling c) (localizedTangentEquivKernel P a).1) :=
  Classical.choose_spec (Classical.choose_spec
    (exists_naturalLocalizedAutomorphismTangentVectorSpace P hp))

end Statements

/-! ### Comparison with the special fibre -/

section Compare

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A morphism of `𝒞_Λ` built from a ring homomorphism compatible with both structures. -/
public def homOfRingHom {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : ↥A →+* ↥B)
    (hcomm : ∀ t : Λ, f (algebraMap Λ ↥A t) = algebraMap Λ ↥B t)
    (hres : ∀ a : ↥A, B.residueEquiv (residue ↥B (f a)) = A.residueEquiv (residue ↥A a)) :
    A ⟶ B where
  hom := { toRingHom := f, commutes' := hcomm }
  isLocal := by
    refine ⟨fun a ha => ?_⟩
    have hne := (residue_ne_zero_iff_isUnit (f a)).mpr ha
    apply (residue_ne_zero_iff_isUnit a).mp
    intro hz
    apply hne
    apply B.residueEquiv.injective
    rw [hres a, hz, map_zero, map_zero]
  residue_comm := hres

variable {F : Type u₁} [Category.{v₁} F]
  {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

/-- The dual numbers over two different bases have the same carrier; this is the
identity comparison between them. -/
private noncomputable def dualCompare (x y : F) :
    (dualNumbersUnder (p := p) (x := x)).right ⟶ (dualNumbersUnder (p := p) (x := y)).right :=
  homOfRingHom (RingHom.id _)
    (fun t => (congrArg TrivSqZeroExt.inl ((p.obj x).residueEquiv.commutes t)).trans
      (congrArg TrivSqZeroExt.inl ((p.obj y).residueEquiv.commutes t)).symm)
    (fun _ => rfl)

/-- The residue-field objects over two different bases have the same carrier; this is the
identity comparison between them. -/
private noncomputable def specialCompare (x y : F) :
    (specialFibreUnder (p := p) (x := x)).right ⟶
      (specialFibreUnder (p := p) (x := y)).right :=
  homOfRingHom (RingHom.id _)
    (fun t => (congrArg ULift.up ((p.obj x).residueEquiv.commutes t)).trans
      (congrArg ULift.up ((p.obj y).residueEquiv.commutes t)).symm)
    (fun _ => rfl)

private theorem dualCompare_apply (x y : F)
    (t : ↥(dualNumbersUnder (p := p) (x := x)).right) :
    (dualCompare (p := p) x y).hom t = t := rfl

private theorem isIso_dualCompare (x y : F) : IsIso (dualCompare (p := p) x y) :=
  ArtinianLocalAlgCat.isIso_of_bijective_hom _ Function.bijective_id

private theorem isIso_specialCompare (x y : F) : IsIso (specialCompare (p := p) x y) :=
  ArtinianLocalAlgCat.isIso_of_bijective_hom _ Function.bijective_id

private theorem dualCompare_red (x y : F) :
    dualCompare (p := p) x y ≫ (tangentReduction (p := p) (x := y)).right =
      (tangentReduction (p := p) (x := x)).right ≫ specialCompare (p := p) x y :=
  ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun _ => rfl)

private theorem dualCompare_scale (x y : F) (c : k) :
    (tangentScaling (p := p) (x := x) c).right ≫ dualCompare (p := p) x y =
      dualCompare (p := p) x y ≫ (tangentScaling (p := p) (x := y) c).right :=
  ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun _ => rfl)

variable (hp : SatisfiesRS p) {x x₀ : F}
  (j : x ⟶ x₀)

-- The locked statement of Tag 06JV (2) carries the hypothesis that the base of `x₀` is the
-- residue field; the route below needs only `j` and the residue compatibility that every
-- morphism of `𝒞_Λ` already carries, so the hypothesis is never used. It is therefore an
-- explicit binder of this one theorem, named `_hbase`, rather than a section variable: the
-- hypothesis stays in the statement in the same position, and nothing about it has to be
-- asserted to the linters.
/-- **Stacks Project, Tag 06JV (2).** Pushforward to the special fibre canonically
identifies the tangent spaces at the identity of the two automorphism functors. The
comparison is conjugation by the unique isomorphism of dual-number pushforwards lying over
the identity of the dual-number ring. -/
@[stacks 06JV "part (2)"]
public theorem existsUnique_localizedTangentAutomorphismLinearEquiv
    (_hbase : p.obj x₀ = residueFieldObject.{u, v, w} Λ k)
    (P : ChosenPushforwardsAt p x)
    (Q : ChosenPushforwardsAt p x₀) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    letI := naturalLocalizedTangentAddCommGroup Q hp
    letI := naturalLocalizedTangentModule Q hp
    let U₀ := specialFibreUnder (p := p) (x := x)
    let Uε := dualNumbersUnder (p := p) (x := x)
    let V₀ := specialFibreUnder (p := p) (x := x₀)
    let Vε := dualNumbersUnder (p := p) (x := x₀)
    ∃! E : localizedAutomorphismFunctorTangent P ≃ₗ[k]
        localizedAutomorphismFunctorTangent Q,
      ∃ (H₀ : (P.obj U₀).1 ≅ (Q.obj V₀).1)
          (Hε : (P.obj Uε).1 ≅ (Q.obj Vε).1),
        (P.inclusion U₀ ≫ H₀.hom = j ≫ Q.inclusion V₀) ∧
        (P.inclusion Uε ≫ Hε.hom = j ≫ Q.inclusion Vε) ∧
        (∀ t : Uε.right,
          (eqToHom (P.obj Uε).2.symm ≫ p.map Hε.hom ≫
            eqToHom (Q.obj Vε).2).hom t = t) ∧
        (∀ a, (localizedTangentEquivKernel P a).1.hom.val ≫ Hε.hom =
          Hε.hom ≫ (localizedTangentEquivKernel Q (E a)).1.hom.val) := by
  classical
  dsimp only
  let mE := dualCompare (p := p) x x₀
  let mZ := specialCompare (p := p) x x₀
  let _ := P.inclusion_cocartesian (dualNumbersUnder (p := p) (x := x))
  let _ := P.inclusion_cocartesian (specialFibreUnder (p := p) (x := x))
  let _ := Q.inclusion_cocartesian (dualNumbersUnder (p := p) (x := x₀))
  let _ := Q.inclusion_cocartesian (specialFibreUnder (p := p) (x := x₀))
  let _ : p.IsHomLift (p.map j) j := IsHomLift.map p j
  let _ : p.IsHomLift (p.map j ≫ (dualNumbersUnder (p := p) (x := x₀)).hom)
      (j ≫ Q.inclusion (dualNumbersUnder (p := p) (x := x₀))) :=
    IsHomLift.comp p (p.map j) (dualNumbersUnder (p := p) (x := x₀)).hom j
      (Q.inclusion (dualNumbersUnder (p := p) (x := x₀)))
  let _ : p.IsHomLift (p.map j ≫ (specialFibreUnder (p := p) (x := x₀)).hom)
      (j ≫ Q.inclusion (specialFibreUnder (p := p) (x := x₀))) :=
    IsHomLift.comp p (p.map j) (specialFibreUnder (p := p) (x := x₀)).hom j
      (Q.inclusion (specialFibreUnder (p := p) (x := x₀)))
  have hfacE : p.map j ≫ (dualNumbersUnder (p := p) (x := x₀)).hom =
      (dualNumbersUnder (p := p) (x := x)).hom ≫ mE :=
    ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun t =>
      congrArg TrivSqZeroExt.inl ((p.map j).residue_comm t))
  have hfacZ : p.map j ≫ (specialFibreUnder (p := p) (x := x₀)).hom =
      (specialFibreUnder (p := p) (x := x)).hom ≫ mZ :=
    ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun t =>
      congrArg ULift.up ((p.map j).residue_comm t))
  let HE := Functor.IsStronglyCocartesian.map p (dualNumbersUnder (p := p) (x := x)).hom
    (P.inclusion (dualNumbersUnder (p := p) (x := x))) hfacE
    (j ≫ Q.inclusion (dualNumbersUnder (p := p) (x := x₀)))
  let HZ := Functor.IsStronglyCocartesian.map p (specialFibreUnder (p := p) (x := x)).hom
    (P.inclusion (specialFibreUnder (p := p) (x := x))) hfacZ
    (j ≫ Q.inclusion (specialFibreUnder (p := p) (x := x₀)))
  have hHEfac : P.inclusion (dualNumbersUnder (p := p) (x := x)) ≫ HE =
      j ≫ Q.inclusion (dualNumbersUnder (p := p) (x := x₀)) :=
    Functor.IsStronglyCocartesian.fac p (dualNumbersUnder (p := p) (x := x)).hom
      (P.inclusion (dualNumbersUnder (p := p) (x := x))) hfacE
      (j ≫ Q.inclusion (dualNumbersUnder (p := p) (x := x₀)))
  have hHZfac : P.inclusion (specialFibreUnder (p := p) (x := x)) ≫ HZ =
      j ≫ Q.inclusion (specialFibreUnder (p := p) (x := x₀)) :=
    Functor.IsStronglyCocartesian.fac p (specialFibreUnder (p := p) (x := x)).hom
      (P.inclusion (specialFibreUnder (p := p) (x := x))) hfacZ
      (j ≫ Q.inclusion (specialFibreUnder (p := p) (x := x₀)))
  let _ : IsIso mE := isIso_dualCompare x x₀
  let _ : IsIso mZ := isIso_specialCompare x x₀
  let _ : p.IsStronglyCocartesian mE HE :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp.1 mE HE inferInstance
  let _ : p.IsStronglyCocartesian mZ HZ :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp.1 mZ HZ inferInstance
  let _ : IsIso HE := Functor.IsStronglyCocartesian.isIso_of_base_isIso p mE HE
  let _ : IsIso HZ := Functor.IsStronglyCocartesian.isIso_of_base_isIso p mZ HZ
  -- the comparison is compatible with reduction
  have hredcomp : P.map (tangentReduction (p := p) (x := x)) ≫ HZ =
      HE ≫ Q.map (tangentReduction (p := p) (x := x₀)) := by
    let _ : p.IsHomLift ((tangentReduction (p := p) (x := x)).right ≫ mZ)
        (P.map (tangentReduction (p := p) (x := x)) ≫ HZ) :=
      IsHomLift.comp p (tangentReduction (p := p) (x := x)).right mZ
        (P.map (tangentReduction (p := p) (x := x))) HZ
    let _ : p.IsHomLift ((tangentReduction (p := p) (x := x)).right ≫ mZ)
        (HE ≫ Q.map (tangentReduction (p := p) (x := x₀))) := by
      rw [← dualCompare_red (p := p) x x₀]
      exact IsHomLift.comp p mE (tangentReduction (p := p) (x := x₀)).right HE
        (Q.map (tangentReduction (p := p) (x := x₀)))
    refine Functor.IsStronglyCocartesian.ext p (dualNumbersUnder (p := p) (x := x)).hom
      (P.inclusion (dualNumbersUnder (p := p) (x := x)))
      ((tangentReduction (p := p) (x := x)).right ≫ mZ) ?_
    rw [← Category.assoc, P.inclusion_map, hHZfac, ← Category.assoc, hHEfac, Category.assoc,
      Q.inclusion_map]
  -- the comparison is compatible with scaling
  have hscalecomp : ∀ c : k, P.map (tangentScaling (p := p) (x := x) c) ≫ HE =
      HE ≫ Q.map (tangentScaling (p := p) (x := x₀) c) := by
    intro c
    let _ : p.IsHomLift ((tangentScaling (p := p) (x := x) c).right ≫ mE)
        (P.map (tangentScaling (p := p) (x := x) c) ≫ HE) :=
      IsHomLift.comp p (tangentScaling (p := p) (x := x) c).right mE
        (P.map (tangentScaling (p := p) (x := x) c)) HE
    let _ : p.IsHomLift ((tangentScaling (p := p) (x := x) c).right ≫ mE)
        (HE ≫ Q.map (tangentScaling (p := p) (x := x₀) c)) := by
      rw [dualCompare_scale (p := p) x x₀ c]
      exact IsHomLift.comp p mE (tangentScaling (p := p) (x := x₀) c).right HE
        (Q.map (tangentScaling (p := p) (x := x₀) c))
    refine Functor.IsStronglyCocartesian.ext p (dualNumbersUnder (p := p) (x := x)).hom
      (P.inclusion (dualNumbersUnder (p := p) (x := x)))
      ((tangentScaling (p := p) (x := x) c).right ≫ mE) ?_
    rw [← Category.assoc, P.inclusion_map, hHEfac, ← Category.assoc, hHEfac, Category.assoc,
      Q.inclusion_map]
  -- explicit inverses, so that no opaque `inv` appears
  obtain ⟨HEi, hHE1, hHE2⟩ :
      ∃ g : (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1 ⟶
        (P.obj (dualNumbersUnder (p := p) (x := x))).1,
      HE ≫ g = 𝟙 (P.obj (dualNumbersUnder (p := p) (x := x))).1 ∧
        g ≫ HE = 𝟙 (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1 :=
    ⟨inv HE, IsIso.hom_inv_id HE, IsIso.inv_hom_id HE⟩
  obtain ⟨HZi, hHZ1, hHZ2⟩ : ∃ g : (Q.obj (specialFibreUnder (p := p) (x := x₀))).1 ⟶
        (P.obj (specialFibreUnder (p := p) (x := x))).1,
      HZ ≫ g = 𝟙 (P.obj (specialFibreUnder (p := p) (x := x))).1 ∧
        g ≫ HZ = 𝟙 (Q.obj (specialFibreUnder (p := p) (x := x₀))).1 :=
    ⟨inv HZ, IsIso.hom_inv_id HZ, IsIso.inv_hom_id HZ⟩
  -- conjugation by the comparison isomorphism
  have hconjlift :
      ∀ g : (P.obj (dualNumbersUnder (p := p) (x := x))).1 ⟶
        (P.obj (dualNumbersUnder (p := p) (x := x))).1,
      p.IsHomLift (𝟙 (dualNumbersUnder (p := p) (x := x)).right) g →
      p.IsHomLift (𝟙 (dualNumbersUnder (p := p) (x := x₀)).right) (HEi ≫ g ≫ HE) := by
    intro g hg
    let _ := hg
    refine IsHomLift.of_fac' p (𝟙 (dualNumbersUnder (p := p) (x := x₀)).right) (HEi ≫ g ≫ HE)
      (Q.obj (dualNumbersUnder (p := p) (x := x₀))).2
      (Q.obj (dualNumbersUnder (p := p) (x := x₀))).2 ?_
    have hpg : p.map g = 𝟙 (p.obj (P.obj (dualNumbersUnder (p := p) (x := x))).1) := by
      rw [IsHomLift.fac' p (𝟙 (dualNumbersUnder (p := p) (x := x)).right) g]
      simp
    have h : p.map (HEi ≫ g ≫ HE) = 𝟙 (p.obj (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1) := by
      rw [p.map_comp, p.map_comp, hpg, Category.id_comp, ← p.map_comp, hHE2, p.map_id]
    rw [h]
    simp
  have hconjliftQ :
      ∀ g : (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1 ⟶
        (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1,
      p.IsHomLift (𝟙 (dualNumbersUnder (p := p) (x := x₀)).right) g →
      p.IsHomLift (𝟙 (dualNumbersUnder (p := p) (x := x)).right) (HE ≫ g ≫ HEi) := by
    intro g hg
    let _ := hg
    refine IsHomLift.of_fac' p (𝟙 (dualNumbersUnder (p := p) (x := x)).right) (HE ≫ g ≫ HEi)
      (P.obj (dualNumbersUnder (p := p) (x := x))).2
      (P.obj (dualNumbersUnder (p := p) (x := x))).2 ?_
    have hpg : p.map g = 𝟙 (p.obj (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1) := by
      rw [IsHomLift.fac' p (𝟙 (dualNumbersUnder (p := p) (x := x₀)).right) g]
      simp
    have h : p.map (HE ≫ g ≫ HEi) = 𝟙 (p.obj (P.obj (dualNumbersUnder (p := p) (x := x))).1) := by
      rw [p.map_comp, p.map_comp, hpg, Category.id_comp, ← p.map_comp, hHE1, p.map_id]
    rw [h]
    simp
  have hcancelP : ∀ f g : (P.obj (dualNumbersUnder (p := p) (x := x))).1 ⟶
      (P.obj (dualNumbersUnder (p := p) (x := x))).1,
      (HEi ≫ f ≫ HE) ≫ (HEi ≫ g ≫ HE) = HEi ≫ (f ≫ g) ≫ HE := by
    intro f g
    calc (HEi ≫ f ≫ HE) ≫ (HEi ≫ g ≫ HE)
        = HEi ≫ f ≫ (HE ≫ HEi) ≫ g ≫ HE := by simp only [Category.assoc]
      _ = HEi ≫ f ≫ 𝟙 (P.obj (dualNumbersUnder (p := p) (x := x))).1 ≫ g ≫ HE := by rw [hHE1]
      _ = HEi ≫ (f ≫ g) ≫ HE := by simp only [Category.id_comp, Category.assoc]
  have hcancelQ : ∀ f g : (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1 ⟶
      (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1,
      (HE ≫ f ≫ HEi) ≫ (HE ≫ g ≫ HEi) = HE ≫ (f ≫ g) ≫ HEi := by
    intro f g
    calc (HE ≫ f ≫ HEi) ≫ (HE ≫ g ≫ HEi)
        = HE ≫ f ≫ (HEi ≫ HE) ≫ g ≫ HEi := by simp only [Category.assoc]
      _ = HE ≫ f ≫ 𝟙 (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1 ≫ g ≫ HEi := by rw [hHE2]
      _ = HE ≫ (f ≫ g) ≫ HEi := by simp only [Category.id_comp, Category.assoc]
  have hidP : HEi ≫ 𝟙 (P.obj (dualNumbersUnder (p := p) (x := x))).1 ≫ HE =
      𝟙 (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1 := by
    rw [Category.id_comp, hHE2]
  have hidQ : HE ≫ 𝟙 (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1 ≫ HEi =
      𝟙 (P.obj (dualNumbersUnder (p := p) (x := x))).1 := by
    rw [Category.id_comp, hHE1]
  have hPQP : ∀ f : (P.obj (dualNumbersUnder (p := p) (x := x))).1 ⟶
        (P.obj (dualNumbersUnder (p := p) (x := x))).1,
      HE ≫ (HEi ≫ f ≫ HE) ≫ HEi = f := by
    intro f
    calc HE ≫ (HEi ≫ f ≫ HE) ≫ HEi
        = (HE ≫ HEi) ≫ f ≫ HE ≫ HEi := by simp only [Category.assoc]
      _ = 𝟙 (P.obj (dualNumbersUnder (p := p) (x := x))).1 ≫ f ≫
            𝟙 (P.obj (dualNumbersUnder (p := p) (x := x))).1 := by rw [hHE1]
      _ = f := by simp only [Category.id_comp, Category.comp_id]
  have hQPQ : ∀ g : (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1 ⟶
        (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1,
      HEi ≫ (HE ≫ g ≫ HEi) ≫ HE = g := by
    intro g
    calc HEi ≫ (HE ≫ g ≫ HEi) ≫ HE
        = (HEi ≫ HE) ≫ g ≫ HEi ≫ HE := by simp only [Category.assoc]
      _ = 𝟙 (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1 ≫ g ≫
            𝟙 (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1 := by rw [hHE2]
      _ = g := by simp only [Category.id_comp, Category.comp_id]
  let Φ : Aut (P.obj (dualNumbersUnder (p := p) (x := x))) →
      Aut (Q.obj (dualNumbersUnder (p := p) (x := x₀))) := fun α =>
    { hom := ⟨HEi ≫ α.hom.val ≫ HE, hconjlift α.hom.val α.hom.2⟩
      inv := ⟨HEi ≫ α.inv.val ≫ HE, hconjlift α.inv.val α.inv.2⟩
      hom_inv_id := Functor.Fiber.hom_ext (by
        change (HEi ≫ α.hom.val ≫ HE) ≫ (HEi ≫ α.inv.val ≫ HE) =
          𝟙 (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1
        have h : α.hom.val ≫ α.inv.val = 𝟙 (P.obj (dualNumbersUnder (p := p) (x := x))).1 :=
          congrArg Subtype.val α.hom_inv_id
        rw [hcancelP, h, hidP])
      inv_hom_id := Functor.Fiber.hom_ext (by
        change (HEi ≫ α.inv.val ≫ HE) ≫ (HEi ≫ α.hom.val ≫ HE) =
          𝟙 (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1
        have h : α.inv.val ≫ α.hom.val = 𝟙 (P.obj (dualNumbersUnder (p := p) (x := x))).1 :=
          congrArg Subtype.val α.inv_hom_id
        rw [hcancelP, h, hidP]) }
  let Ψ : Aut (Q.obj (dualNumbersUnder (p := p) (x := x₀))) →
      Aut (P.obj (dualNumbersUnder (p := p) (x := x))) := fun β =>
    { hom := ⟨HE ≫ β.hom.val ≫ HEi, hconjliftQ β.hom.val β.hom.2⟩
      inv := ⟨HE ≫ β.inv.val ≫ HEi, hconjliftQ β.inv.val β.inv.2⟩
      hom_inv_id := Functor.Fiber.hom_ext (by
        change (HE ≫ β.hom.val ≫ HEi) ≫ (HE ≫ β.inv.val ≫ HEi) =
          𝟙 (P.obj (dualNumbersUnder (p := p) (x := x))).1
        have h : β.hom.val ≫ β.inv.val = 𝟙 (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1 :=
          congrArg Subtype.val β.hom_inv_id
        rw [hcancelQ, h, hidQ])
      inv_hom_id := Functor.Fiber.hom_ext (by
        change (HE ≫ β.inv.val ≫ HEi) ≫ (HE ≫ β.hom.val ≫ HEi) =
          𝟙 (P.obj (dualNumbersUnder (p := p) (x := x))).1
        have h : β.inv.val ≫ β.hom.val = 𝟙 (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1 :=
          congrArg Subtype.val β.inv_hom_id
        rw [hcancelQ, h, hidQ]) }
  have hΨΦ : ∀ α, Ψ (Φ α) = α := by
    intro α
    apply Iso.ext
    apply Functor.Fiber.hom_ext
    change HE ≫ (HEi ≫ α.hom.val ≫ HE) ≫ HEi = α.hom.val
    exact hPQP α.hom.val
  have hΦΨ : ∀ β, Φ (Ψ β) = β := by
    intro β
    apply Iso.ext
    apply Functor.Fiber.hom_ext
    change HEi ≫ (HE ≫ β.hom.val ≫ HEi) ≫ HE = β.hom.val
    exact hQPQ β.hom.val
  have hΦmul : ∀ α β, Φ (α * β) = Φ α * Φ β := by
    intro α β
    apply Iso.ext
    apply Functor.Fiber.hom_ext
    change HEi ≫ (β.hom.val ≫ α.hom.val) ≫ HE =
      (HEi ≫ β.hom.val ≫ HE) ≫ (HEi ≫ α.hom.val ≫ HE)
    exact (hcancelP β.hom.val α.hom.val).symm
  -- the comparison identities, in inverse form
  have hredcomp' : HEi ≫ P.map (tangentReduction (p := p) (x := x)) =
      Q.map (tangentReduction (p := p) (x := x₀)) ≫ HZi := by
    calc HEi ≫ P.map (tangentReduction (p := p) (x := x))
        = HEi ≫ P.map (tangentReduction (p := p) (x := x)) ≫ HZ ≫ HZi := by
            rw [hHZ1, Category.comp_id]
      _ = HEi ≫ (P.map (tangentReduction (p := p) (x := x)) ≫ HZ) ≫ HZi := by
            simp only [Category.assoc]
      _ = HEi ≫ (HE ≫ Q.map (tangentReduction (p := p) (x := x₀))) ≫ HZi := by rw [hredcomp]
      _ = (HEi ≫ HE) ≫ Q.map (tangentReduction (p := p) (x := x₀)) ≫ HZi := by
            simp only [Category.assoc]
      _ = Q.map (tangentReduction (p := p) (x := x₀)) ≫ HZi := by rw [hHE2, Category.id_comp]
  have hscalecomp' : ∀ c : k, HEi ≫ P.map (tangentScaling (p := p) (x := x) c) =
      Q.map (tangentScaling (p := p) (x := x₀) c) ≫ HEi := by
    intro c
    calc HEi ≫ P.map (tangentScaling (p := p) (x := x) c)
        = HEi ≫ P.map (tangentScaling (p := p) (x := x) c) ≫ HE ≫ HEi := by
          rw [hHE1, Category.comp_id]
      _ = HEi ≫ (P.map (tangentScaling (p := p) (x := x) c) ≫ HE) ≫ HEi := by
          simp only [Category.assoc]
      _ = HEi ≫ (HE ≫ Q.map (tangentScaling (p := p) (x := x₀) c)) ≫ HEi := by
          rw [hscalecomp c]
      _ = (HEi ≫ HE) ≫ Q.map (tangentScaling (p := p) (x := x₀) c) ≫ HEi := by
          simp only [Category.assoc]
      _ = Q.map (tangentScaling (p := p) (x := x₀) c) ≫ HEi := by
          rw [hHE2, Category.id_comp]
  -- conjugation preserves the kernels
  have hΦker : ∀ α, α ∈ MonoidHom.ker (P.transportAutHom (tangentReduction (p := p) (x := x))) →
      Φ α ∈ MonoidHom.ker (Q.transportAutHom (tangentReduction (p := p) (x := x₀))) := by
    intro α hα
    have hα' := (mem_ker_transportAutHom_iff P (tangentReduction (p := p) (x := x)) α).mp hα
    refine (mem_ker_transportAutHom_iff Q (tangentReduction (p := p) (x := x₀)) (Φ α)).mpr ?_
    change (HEi ≫ α.hom.val ≫ HE) ≫ Q.map (tangentReduction (p := p) (x := x₀)) =
      Q.map (tangentReduction (p := p) (x := x₀))
    calc (HEi ≫ α.hom.val ≫ HE) ≫ Q.map (tangentReduction (p := p) (x := x₀))
        = HEi ≫ α.hom.val ≫ HE ≫ Q.map (tangentReduction (p := p) (x := x₀)) := by
            simp only [Category.assoc]
      _ = HEi ≫ α.hom.val ≫ P.map (tangentReduction (p := p) (x := x)) ≫ HZ := by rw [← hredcomp]
      _ = HEi ≫ (α.hom.val ≫ P.map (tangentReduction (p := p) (x := x))) ≫ HZ := by
            simp only [Category.assoc]
      _ = HEi ≫ P.map (tangentReduction (p := p) (x := x)) ≫ HZ := by rw [hα']
      _ = (HEi ≫ P.map (tangentReduction (p := p) (x := x))) ≫ HZ := by simp only [Category.assoc]
      _ = (Q.map (tangentReduction (p := p) (x := x₀)) ≫ HZi) ≫ HZ := by rw [hredcomp']
      _ = Q.map (tangentReduction (p := p) (x := x₀)) := by
            rw [Category.assoc, hHZ2, Category.comp_id]
  have hΨker : ∀ β, β ∈ MonoidHom.ker (Q.transportAutHom (tangentReduction (p := p) (x := x₀))) →
      Ψ β ∈ MonoidHom.ker (P.transportAutHom (tangentReduction (p := p) (x := x))) := by
    intro β hβ
    have hβ' := (mem_ker_transportAutHom_iff Q (tangentReduction (p := p) (x := x₀)) β).mp hβ
    refine (mem_ker_transportAutHom_iff P (tangentReduction (p := p) (x := x)) (Ψ β)).mpr ?_
    change (HE ≫ β.hom.val ≫ HEi) ≫ P.map (tangentReduction (p := p) (x := x)) =
      P.map (tangentReduction (p := p) (x := x))
    calc (HE ≫ β.hom.val ≫ HEi) ≫ P.map (tangentReduction (p := p) (x := x))
        = HE ≫ β.hom.val ≫ HEi ≫ P.map (tangentReduction (p := p) (x := x)) := by
            simp only [Category.assoc]
      _ = HE ≫ β.hom.val ≫ Q.map (tangentReduction (p := p) (x := x₀)) ≫ HZi := by rw [hredcomp']
      _ = HE ≫ (β.hom.val ≫ Q.map (tangentReduction (p := p) (x := x₀))) ≫ HZi := by
            simp only [Category.assoc]
      _ = HE ≫ Q.map (tangentReduction (p := p) (x := x₀)) ≫ HZi := by rw [hβ']
      _ = (HE ≫ Q.map (tangentReduction (p := p) (x := x₀))) ≫ HZi := by simp only [Category.assoc]
      _ = (P.map (tangentReduction (p := p) (x := x)) ≫ HZ) ≫ HZi := by rw [hredcomp]
      _ = P.map (tangentReduction (p := p) (x := x)) := by
            rw [Category.assoc, hHZ1, Category.comp_id]
  -- conjugation is compatible with the scalar action
  have hΦscale : ∀ (c : k) (α : Aut (P.obj (dualNumbersUnder (p := p) (x := x)))),
      Q.transportAut (tangentScaling (p := p) (x := x₀) c) (Φ α) =
        Φ (P.transportAut (tangentScaling (p := p) (x := x) c) α) := by
    intro c α
    refine (transportAut_eq_iff Q (tangentScaling (p := p) (x := x₀) c) (Φ α) _).mpr ?_
    change (HEi ≫ α.hom.val ≫ HE) ≫ Q.map (tangentScaling (p := p) (x := x₀) c) =
      Q.map (tangentScaling (p := p) (x := x₀) c) ≫
        HEi ≫ (P.transportAut (tangentScaling (p := p) (x := x) c) α).hom.val ≫ HE
    calc (HEi ≫ α.hom.val ≫ HE) ≫ Q.map (tangentScaling (p := p) (x := x₀) c)
        = HEi ≫ α.hom.val ≫ HE ≫ Q.map (tangentScaling (p := p) (x := x₀) c) := by
          simp only [Category.assoc]
      _ = HEi ≫ α.hom.val ≫ P.map (tangentScaling (p := p) (x := x) c) ≫ HE := by
          rw [← hscalecomp c]
      _ = HEi ≫ (α.hom.val ≫ P.map (tangentScaling (p := p) (x := x) c)) ≫ HE := by
          simp only [Category.assoc]
      _ = HEi ≫ (P.map (tangentScaling (p := p) (x := x) c) ≫
            (P.transportAut (tangentScaling (p := p) (x := x) c) α).hom.val) ≫ HE := by
          have h : P.map (tangentScaling (p := p) (x := x) c) ≫
              (P.transportAut (tangentScaling (p := p) (x := x) c) α).hom.val =
              α.hom.val ≫ P.map (tangentScaling (p := p) (x := x) c) :=
            P.map_transportHom (tangentScaling (p := p) (x := x) c) α
          rw [h]
      _ = (HEi ≫ P.map (tangentScaling (p := p) (x := x) c)) ≫
            (P.transportAut (tangentScaling (p := p) (x := x) c) α).hom.val ≫ HE := by
          simp only [Category.assoc]
      _ = (Q.map (tangentScaling (p := p) (x := x₀) c) ≫ HEi) ≫
            (P.transportAut (tangentScaling (p := p) (x := x) c) α).hom.val ≫ HE := by
          rw [hscalecomp' c]
      _ = Q.map (tangentScaling (p := p) (x := x₀) c) ≫
            HEi ≫ (P.transportAut (tangentScaling (p := p) (x := x) c) α).hom.val ≫ HE := by
          simp only [Category.assoc]
  -- the induced equivalence of tangent spaces
  let EPk := localizedTangentEquivKernel P
  let EQk := localizedTangentEquivKernel Q
  let eK : infinitesimalAutomorphismKernel P (tangentReduction (p := p) (x := x)) ≃
      infinitesimalAutomorphismKernel Q (tangentReduction (p := p) (x := x₀)) :=
    { toFun := fun a => ⟨Φ a.1, hΦker a.1 a.2⟩
      invFun := fun b => ⟨Ψ b.1, hΨker b.1 b.2⟩
      left_inv := fun a => Subtype.ext (hΨΦ a.1)
      right_inv := fun b => Subtype.ext (hΦΨ b.1) }
  have heKmul : ∀ α β, eK (α * β) = eK α * eK β := fun α β => Subtype.ext (hΦmul α.1 β.1)
  let _ : AddCommGroup (localizedAutomorphismFunctorTangent P) :=
    naturalLocalizedTangentAddCommGroup P hp
  let _ : Module k (localizedAutomorphismFunctorTangent P) :=
    naturalLocalizedTangentModule P hp
  let _ : AddCommGroup (localizedAutomorphismFunctorTangent Q) :=
    naturalLocalizedTangentAddCommGroup Q hp
  let _ : Module k (localizedAutomorphismFunctorTangent Q) :=
    naturalLocalizedTangentModule Q hp
  obtain ⟨hPadd, hPsmul⟩ := naturalLocalizedTangentModule_spec P hp
  obtain ⟨hQadd, hQsmul⟩ := naturalLocalizedTangentModule_spec Q hp
  let E0 : localizedAutomorphismFunctorTangent P ≃ localizedAutomorphismFunctorTangent Q :=
    EPk.trans (eK.trans EQk.symm)
  have hE0 : ∀ a, EQk (E0 a) = eK (EPk a) := fun a => EQk.apply_symm_apply _
  have hadd : ∀ a b, E0 (a + b) = E0 a + E0 b := by
    intro a b
    refine EQk.injective ?_
    calc EQk (E0 (a + b)) = eK (EPk (a + b)) := hE0 (a + b)
      _ = eK (EPk a * EPk b) := congrArg eK (hPadd a b)
      _ = eK (EPk a) * eK (EPk b) := heKmul _ _
      _ = EQk (E0 a) * EQk (E0 b) := by rw [hE0 a, hE0 b]
      _ = EQk (E0 a + E0 b) := (hQadd (E0 a) (E0 b)).symm
  have hsmul : ∀ (c : k) a, E0 (c • a) = c • E0 a := by
    intro c a
    refine EQk.injective (Subtype.ext ?_)
    calc (EQk (E0 (c • a))).1 = (eK (EPk (c • a))).1 := congrArg Subtype.val (hE0 (c • a))
      _ = Φ (EPk (c • a)).1 := rfl
      _ = Φ (P.transportAutHom (tangentScaling (p := p) (x := x) c) (EPk a).1) :=
          congrArg Φ (hPsmul c a)
      _ = Q.transportAutHom (tangentScaling (p := p) (x := x₀) c) (Φ (EPk a).1) := by
          have h := hΦscale c (EPk a).1
          exact h.symm
      _ = Q.transportAutHom (tangentScaling (p := p) (x := x₀) c) (EQk (E0 a)).1 := by
          rw [hE0 a]
          rfl
      _ = (EQk (c • E0 a)).1 := (hQsmul c (E0 a)).symm
  have hcond4 : ∀ a, (EPk a).1.hom.val ≫ HE = HE ≫ (EQk (E0 a)).1.hom.val := by
    intro a
    rw [hE0 a]
    change (EPk a).1.hom.val ≫ HE = HE ≫ HEi ≫ (EPk a).1.hom.val ≫ HE
    rw [← Category.assoc, hHE1, Category.id_comp]
  let EL : localizedAutomorphismFunctorTangent P ≃ₗ[k]
      localizedAutomorphismFunctorTangent Q :=
    { toFun := E0
      map_add' := hadd
      map_smul' := hsmul
      invFun := E0.symm
      left_inv := E0.left_inv
      right_inv := E0.right_inv }
  refine ⟨EL, ⟨⟨HZ, HZi, hHZ1, hHZ2⟩, ⟨HE, HEi, hHE1, hHE2⟩, hHZfac, hHEfac, ?_, hcond4⟩, ?_⟩
  · intro t
    have hm : eqToHom (P.obj (dualNumbersUnder (p := p) (x := x))).2.symm ≫ p.map HE ≫
        eqToHom (Q.obj (dualNumbersUnder (p := p) (x := x₀))).2 = mE := by
      rw [IsHomLift.fac' p mE HE]
      simp
    rw [hm]
    exact dualCompare_apply x x₀ t
  · intro E' hE'
    obtain ⟨H₀', Hε', h1', h2', h3', h4'⟩ := hE'
    have hmE' : eqToHom (P.obj (dualNumbersUnder (p := p) (x := x))).2.symm ≫ p.map Hε'.hom ≫
        eqToHom (Q.obj (dualNumbersUnder (p := p) (x := x₀))).2 = mE :=
      ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun t =>
        (h3' t).trans (dualCompare_apply x x₀ t).symm)
    have hlift' : p.IsHomLift mE Hε'.hom := by
      refine IsHomLift.of_fac' p mE Hε'.hom (P.obj (dualNumbersUnder (p := p) (x := x))).2
        (Q.obj (dualNumbersUnder (p := p) (x := x₀))).2 ?_
      rw [← hmE']
      simp
    let _ := hlift'
    have hHε' : Hε'.hom = HE :=
      Functor.IsStronglyCocartesian.map_uniq p (dualNumbersUnder (p := p) (x := x)).hom
        (P.inclusion (dualNumbersUnder (p := p) (x := x))) hfacE
        (j ≫ Q.inclusion (dualNumbersUnder (p := p) (x := x₀))) Hε'.hom h2'
    refine LinearEquiv.ext fun a => ?_
    have h4 : (EPk a).1.hom.val ≫ HE = HE ≫ (EQk (E' a)).1.hom.val := by
      rw [← hHε']
      exact h4' a
    have hval : (EQk (E' a)).1.hom.val = (EQk (E0 a)).1.hom.val := by
      calc (EQk (E' a)).1.hom.val
          = 𝟙 (Q.obj (dualNumbersUnder (p := p) (x := x₀))).1 ≫ (EQk (E' a)).1.hom.val :=
            (Category.id_comp _).symm
        _ = (HEi ≫ HE) ≫ (EQk (E' a)).1.hom.val := by rw [hHE2]
        _ = HEi ≫ HE ≫ (EQk (E' a)).1.hom.val := Category.assoc _ _ _
        _ = HEi ≫ HE ≫ (EQk (E0 a)).1.hom.val := by rw [← h4, hcond4 a]
        _ = (HEi ≫ HE) ≫ (EQk (E0 a)).1.hom.val := (Category.assoc _ _ _).symm
        _ = (EQk (E0 a)).1.hom.val := by rw [hHE2, Category.id_comp]
    exact EQk.injective
      (Subtype.ext (Iso.ext (Functor.Fiber.hom_ext hval)))

variable (hbase : p.obj x₀ = residueFieldObject.{u, v, w} Λ k)
  (P : ChosenPushforwardsAt p x)
  (Q : ChosenPushforwardsAt p x₀)

/-- The pinned canonical linear comparison after pushforward to the special fibre. -/
public noncomputable def canonicalLocalizedTangentAutomorphismLinearEquiv :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    letI := naturalLocalizedTangentAddCommGroup Q hp
    letI := naturalLocalizedTangentModule Q hp
    localizedAutomorphismFunctorTangent P ≃ₗ[k]
      localizedAutomorphismFunctorTangent Q :=
  Classical.choose
    (existsUnique_localizedTangentAutomorphismLinearEquiv hp j hbase P Q)

end Compare

end Deformation

end
