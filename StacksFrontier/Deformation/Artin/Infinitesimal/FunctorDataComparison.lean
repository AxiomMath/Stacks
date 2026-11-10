module

public import StacksFrontier.Deformation.Artin.Infinitesimal.DeformationSpaceComparison
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.SpecialFibreThin
public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison

/-!
# The deformation spaces of a field-valued point, for any tangent and `Inf` functor

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, let `k` be a
field whose spectrum lies in the site, and let `x₀` be an object of `𝒳` over `Spec k`. Stacks
0D18 identifies the tangent space and the infinitesimal automorphisms of the deformation
category `𝓕_{𝒳,k,x₀}` with the values at the rank-one vector space of the functors `T_{x₀}` and
`Inf_{x₀}` of Stacks 07Y9. This file proves both identifications for *any* `k`-linear functors
`T` and `I` on the site modules whose underlying sets are the classes of lifts of `x₀`,
respectively the infinitesimal automorphisms of its trivial deformations, compatibly with the
transition maps, under the sole assumption that `𝓕_{𝒳,k,x₀}` is a deformation category. In
particular neither (RS*) nor a finiteness condition on `k` over `S` enters.

The tangent space is compared through the natural bijection of deformation classes over
`k[V]` with lift classes. For the infinitesimal automorphisms the deformation category is read
in the form of Stacks 06IA: the infinitesimal automorphisms of the pushforwards of a point `y`
of its special fibre to the square-zero extensions `k ⊕ V`. These pushforwards are compared
with the trivial deformations of `x₀` by the universal property of cocartesian arrows, and
conjugation by the comparison arrows identifies the two automorphism groups, naturally in `V`.

## Main definitions

* `Deformation.squareZeroUnderRightHom` — the identification of the square-zero extension
  `k ⊕ V` read under an object of `𝒞_Λ` with the one read directly in `𝒞_Λ`.
* `Deformation.squareZeroPushforwardComparison`, `Deformation.squareZeroPushforwardConj` — the
  comparison of chosen pushforwards with a compatible family of pushforwards, and conjugation
  of fibre automorphisms by it.

## Main results

* `Deformation.isLinearMap_of_naturality` — a natural family of maps between the values of two
  additive linear module-valued functors is linear.
* `Deformation.exists_infinitesimalAutomorphismModuleFunctor_equiv` — the infinitesimal
  automorphisms of chosen pushforwards are the fibre endomorphisms of any compatible family of
  pushforwards, naturally.
* `Deformation.Artin.tangentSpace_deformationCategory_linearEquiv_of_tangentFunctorData`,
  `Deformation.Artin.finiteDimensional_tangentFunctorData_of_artinianTangentSpace` — the
  tangent space of `𝓕_{𝒳,k,x₀}` is `T(k)`.
* `Deformation.Artin.nonempty_linearEquiv_infinitesimalAutomorphismLinearLift`,
  `Deformation.Artin.finiteDimensional_infinitesimalAutomorphismFunctorData_of_linearLift`,
  `Deformation.Artin.finiteDimensional_infinitesimalAutomorphismFunctorData` — the
  infinitesimal automorphisms of `𝓕_{𝒳,k,x₀}` are `I(k)`.

## Implementation notes

Both sides of each comparison carry the `k`-linear structure of a linear lift of a set-valued
functor on finite-dimensional vector spaces (Stacks 06I6). Rather than comparing the two
constructions, the comparison uses that a family of maps between the values of two additive
`k`-linear functors which is natural for the underlying sets is automatically linear: addition
is the codiagonal of a biproduct and scalar multiplication is the action of the scalar
endomorphisms. A natural bijection of the underlying set-valued functors is therefore a
natural linear equivalence, as in Stacks 06I7, and the identifications are its components.

The square-zero extension `k ⊕ V` occurs in two presentations: as an algebra under the base of
the point `y`, which is the form the chosen pushforwards use, and as an object of `𝒞_Λ`, which
is the form the trivial deformations use. They have the same underlying ring, and
`Deformation.squareZeroUnderRightHom` is the identity of that ring.

## References

* [Stacks Project, Tag 0D18](https://stacks.math.columbia.edu/tag/0D18)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
* [Stacks Project, Tag 06I6](https://stacks.math.columbia.edu/tag/06I6)
* [Stacks Project, Tag 06I7](https://stacks.math.columbia.edu/tag/06I7)
* [Stacks Project, Tag 06IA](https://stacks.math.columbia.edu/tag/06IA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w u₁ u₂ v₁

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.BasedCategory.ofFunctor
  Deformation.Artin.predeformationCategory

namespace Deformation

/-! ### Natural maps between linear functors are linear -/

section Linear

variable {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
  [HasBinaryBiproducts C]

/-- A family of maps between the values of two additive `R`-linear module-valued functors which
is natural for the underlying set-valued functors is `R`-linear: addition is recovered from the
two projections and the codiagonal of a biproduct, and scalar multiplication from the scalar
endomorphisms of the source. -/
theorem isLinearMap_of_naturality (F : C ⥤ ModuleCat.{u₁} R) (G : C ⥤ ModuleCat.{u₂} R)
    [F.Additive] [F.Linear R] [G.Additive] [G.Linear R] (φ : ∀ X, F.obj X → G.obj X)
    (hφ : ∀ {X Y : C} (f : X ⟶ Y) (a : F.obj X), φ Y (F.map f a) = G.map f (φ X a))
    (X : C) : IsLinearMap R (φ X) := by
  have hadd : ∀ {M N : ModuleCat.{u₂} R} (f g : M ⟶ N) (t : M), (f + g) t = f t + g t :=
    fun _ _ _ => rfl
  have hadd' : ∀ {M N : ModuleCat.{u₁} R} (f g : M ⟶ N) (t : M), (f + g) t = f t + g t :=
    fun _ _ _ => rfl
  have hsmul : ∀ {M : ModuleCat.{u₂} R} (r : R) (t : M), (r • 𝟙 M) t = r • t :=
    fun _ _ => rfl
  have hsmul' : ∀ {M : ModuleCat.{u₁} R} (r : R) (t : M), (r • 𝟙 M) t = r • t :=
    fun _ _ => rfl
  constructor
  · intro a b
    let z : F.obj (X ⊞ X) := F.map biprod.inl a + F.map biprod.inr b
    have h₁ : F.map biprod.fst z = a := by
      simp only [z, map_add, ← ModuleCat.comp_apply, ← F.map_comp, biprod.inl_fst,
        biprod.inr_fst, F.map_id, F.map_zero, ModuleCat.id_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply, add_zero]
    have h₂ : F.map biprod.snd z = b := by
      simp only [z, map_add, ← ModuleCat.comp_apply, ← F.map_comp, biprod.inl_snd,
        biprod.inr_snd, F.map_id, F.map_zero, ModuleCat.id_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply, zero_add]
    have hs : F.map (biprod.fst + biprod.snd) z = a + b := by
      rw [F.map_add, hadd', h₁, h₂]
    rw [← hs, hφ, G.map_add, hadd, ← hφ, ← hφ, h₁, h₂]
  · intro r a
    have hs : F.map (r • 𝟙 X) a = r • a := by
      rw [F.map_smul, F.map_id, hsmul']
    rw [← hs, hφ, G.map_smul, G.map_id, hsmul]

/-- A natural bijection from the underlying set-valued functor of a linear lift to the values of an
additive linear functor is a linear equivalence at every object, given by that bijection. -/
private theorem exists_linearEquiv_of_natural_equiv {H : C ⥤ Type u₁} (L : LinearFunctorLift R H)
    (G : C ⥤ ModuleCat.{u₂} R) [G.Additive] [G.Linear R] (e : ∀ X, H.obj X ≃ G.obj X)
    (he : ∀ {X Y : C} (f : X ⟶ Y) (a : H.obj X), e Y (H.map f a) = G.map f (e X a)) (X : C) :
    ∃ E : L.functor.obj X ≃ₗ[R] G.obj X,
      ∀ t, E t = e X (cast (congrArg (fun K : C ⥤ Type u₁ => K.obj X) L.forget_comp) t) := by
  let φ : ∀ X, L.functor.obj X → G.obj X := fun X t =>
    e X (cast (congrArg (fun K : C ⥤ Type u₁ => K.obj X) L.forget_comp) t)
  refine ⟨LinearEquiv.ofBijective (IsLinearMap.mk' (φ X)
    (isLinearMap_of_naturality L.functor G φ (fun f a => ?_) X))
    ((Equiv.cast (congrArg (fun K : C ⥤ Type u₁ => K.obj X) L.forget_comp)).trans (e X)).bijective,
    fun _ => rfl⟩
  exact (congrArg (e _) (cast_functor_map L.forget_comp f a)).trans (he f _)

end Linear

/-! ### Two presentations of the trivial square-zero extensions -/

section SquareZero

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The trivial square-zero extension `k ⊕ V`, read as an algebra under an object `A` of `𝒞_Λ`,
is the trivial square-zero extension read directly in `𝒞_Λ`: the identity of `k ⊕ V` respects
the two `Λ`-algebra structures, because the residue identification of `A` is `Λ`-linear. -/
def squareZeroUnderRightHom (A : ArtinianLocalAlgCat.{u, u, u} Λ k) (V : FGModuleCat.{u} k) :
    ((squareZeroAlgFunctor.{u, u, u} A).obj V).right ⟶
      (artinianSquareZeroExtensionFunctor Λ k).obj V where
  hom :=
    { toRingHom := RingHom.id _
      commutes' := fun r => TrivSqZeroExt.ext (A.residueEquiv.commutes r) rfl }
  isLocal := ⟨fun _ ha => ha⟩
  residue_comm := fun _ => rfl

/-- The comparison of the two presentations of `k ⊕ V` is an isomorphism. -/
theorem isIso_squareZeroUnderRightHom (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (V : FGModuleCat.{u} k) : IsIso (squareZeroUnderRightHom A V) :=
  ArtinianLocalAlgCat.isIso_of_bijective_hom _ Function.bijective_id

/-- The comparison of the two presentations of `k ⊕ V` is natural in `V`. -/
theorem squareZeroUnderRightHom_naturality (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    ((squareZeroAlgFunctor.{u, u, u} A).map f).right ≫ squareZeroUnderRightHom A W =
      squareZeroUnderRightHom A V ≫ (artinianSquareZeroExtensionFunctor Λ k).map f := by
  ext z
  rfl

/-- Over the residue field, the structure map of the square-zero extension by the zero module,
followed by the comparison of presentations, is bijective. -/
theorem bijective_squareZeroUnder_zero_hom (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : A = residueFieldObject.{u, u, u} Λ k) :
    Function.Bijective (((squareZeroAlgFunctor.{u, u, u} A).obj
      (FGModuleCat.of k PUnit.{u + 1})).hom ≫
        squareZeroUnderRightHom A (FGModuleCat.of k PUnit.{u + 1})).hom := by
  subst hA
  refine ⟨fun a b hab => ?_, fun z => ⟨ULift.up z.fst, ?_⟩⟩
  · have h := congrArg TrivSqZeroExt.fst hab
    change (residueFieldObject.{u, u, u} Λ k).residueEquiv (IsLocalRing.residue _ a) =
      (residueFieldObject.{u, u, u} Λ k).residueEquiv (IsLocalRing.residue _ b) at h
    rw [residueFieldObject_residue, residueFieldObject_residue] at h
    exact ULift.ext h
  · refine TrivSqZeroExt.ext ?_ (Subsingleton.elim (α := PUnit.{u + 1}) _ _)
    exact residueFieldObject_residue.{u, u, u} Λ k (ULift.up.{u} z.fst)

end SquareZero

/-! ### Morphisms out of the special fibre of a predeformation category -/

section SpecialFibre

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {q : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

/-- In a predeformation category, every object over the residue field maps to every object over
an isomorphic base, over any given isomorphism: push the target back to the special fibre, which
is equivalent to a point. -/
theorem exists_isHomLift_of_isIso (hq : IsPredeformationCategory.{u, v, w} q) {a b : F}
    {R S : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (g : R ⟶ S) [IsIso g]
    (ha : q.obj a = R) (hR : R = residueFieldObject.{u, v, w} Λ k) (hb : q.obj b = S) :
    ∃ φ : a ⟶ b, q.IsHomLift g φ := by
  subst ha hb
  obtain ⟨b', c, hc⟩ := exists_pushforward hq.cofibered (inv g) b rfl
  have hb' : q.obj b' = q.obj a := IsHomLift.codomain_eq q (inv g) c
  obtain ⟨-, hu⟩ := (CategoryTheory.equiv_punit_iff_unique _).mp hq.specialFiber
  obtain ⟨m⟩ := hu (Functor.Fiber.mk hR) (Functor.Fiber.mk (hb'.trans hR))
  let m₀ : a ⟶ b' := Functor.Fiber.fiberInclusion.map m.default
  have hm : q.IsHomLift (𝟙 (residueFieldObject.{u, v, w} Λ k)) m₀ := m.default.2
  have hmc : q.map c = inv g ≫ eqToHom hb'.symm := by
    rw [IsHomLift.fac' q (inv g) c]
    simp
  have : IsIso (q.map c) := by rw [hmc]; infer_instance
  have : IsIso c := isIso_of_isCofiberedInGroupoids_of_map_isIso hq.cofibered c
  have hmap : q.map (m₀ ≫ inv c) = g := by
    rw [Functor.map_comp, Functor.map_inv,
      IsHomLift.fac' q (𝟙 (residueFieldObject.{u, v, w} Λ k)) m₀]
    simp [hmc]
  exact ⟨_, hmap ▸ IsHomLift.map q _⟩

end SpecialFibre

/-! ### Infinitesimal automorphisms along a compatible family of pushforwards -/

section PushforwardComparison

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {q : F ⥤ ArtinianLocalAlgCat.{u, u, u} Λ k}
  (hcof : IsCofiberedInGroupoids q) {y : F} (P : ChosenPushforwardsAt q y)
  (Z : ∀ V : FGModuleCat.{u} k, q.Fiber ((artinianSquareZeroExtensionFunctor Λ k).obj V))
  (τ : ∀ {V W : FGModuleCat.{u} k} (_ : V ⟶ W), (Z V).1 ⟶ (Z W).1)
  (hτ : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W),
    q.IsHomLift ((artinianSquareZeroExtensionFunctor Λ k).map f) (τ f))
  (ι : ∀ V : FGModuleCat.{u} k, y ⟶ (Z V).1)
  (hι : ∀ V : FGModuleCat.{u} k, q.IsHomLift (((squareZeroAlgFunctor.{u, u, u} (q.obj y)).obj
    V).hom ≫ squareZeroUnderRightHom (q.obj y) V) (ι V))
  (hιτ : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W), ι V ≫ τ f = ι W)

/-- The comparison of the chosen pushforward of `y` to `k ⊕ V` with the given one, determined by
the universal property of the chosen pushforward. -/
def squareZeroPushforwardComparison (V : FGModuleCat.{u} k) :
    (P.obj ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).obj V)).1 ⟶ (Z V).1 :=
  haveI := P.inclusion_cocartesian ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).obj V)
  haveI := hι V
  Functor.IsStronglyCocartesian.map q ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).obj V).hom
    (P.inclusion _) (g := squareZeroUnderRightHom (q.obj y) V)
    (f' := ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).obj V).hom ≫
      squareZeroUnderRightHom (q.obj y) V) rfl (ι V)

/-- The comparison arrow lies over the identification of the two presentations of `k ⊕ V`. -/
theorem squareZeroPushforwardComparison_isHomLift (V : FGModuleCat.{u} k) :
    q.IsHomLift (squareZeroUnderRightHom (q.obj y) V)
      (squareZeroPushforwardComparison P Z ι hι V) := by
  have := P.inclusion_cocartesian ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).obj V)
  have := hι V
  exact Functor.IsStronglyCocartesian.map_isHomLift q
    ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).obj V).hom (P.inclusion _)
    (g := squareZeroUnderRightHom (q.obj y) V) rfl (ι V)

/-- The comparison arrow carries the chosen arrow out of `y` to the given one. -/
theorem inclusion_squareZeroPushforwardComparison (V : FGModuleCat.{u} k) :
    P.inclusion _ ≫ squareZeroPushforwardComparison P Z ι hι V = ι V := by
  have := P.inclusion_cocartesian ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).obj V)
  have := hι V
  exact Functor.IsStronglyCocartesian.fac q
    ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).obj V).hom (P.inclusion _)
    (g := squareZeroUnderRightHom (q.obj y) V) rfl (ι V)

include hcof in
/-- The comparison arrow is an isomorphism: it lies over one, and every arrow of a category
cofibered in groupoids is cocartesian. -/
theorem isIso_squareZeroPushforwardComparison (V : FGModuleCat.{u} k) :
    IsIso (squareZeroPushforwardComparison P Z ι hι V) := by
  have := squareZeroPushforwardComparison_isHomLift P Z ι hι V
  have := isIso_squareZeroUnderRightHom (q.obj y) V
  have := isStronglyCocartesian_of_isCofiberedInGroupoids hcof _ _
    (squareZeroPushforwardComparison_isHomLift P Z ι hι V)
  exact Functor.IsStronglyCocartesian.isIso_of_base_isIso q
    (squareZeroUnderRightHom (q.obj y) V) _

include hτ hιτ in
/-- The comparison arrows are natural in `V`. -/
theorem squareZeroPushforwardComparison_naturality {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    squareZeroPushforwardComparison P Z ι hι V ≫ τ f =
      P.map ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).map f) ≫
        squareZeroPushforwardComparison P Z ι hι W := by
  have := P.inclusion_cocartesian ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).obj V)
  have := squareZeroPushforwardComparison_isHomLift P Z ι hι V
  have := squareZeroPushforwardComparison_isHomLift P Z ι hι W
  have := hτ f
  have : q.IsHomLift (squareZeroUnderRightHom (q.obj y) V ≫
      (artinianSquareZeroExtensionFunctor Λ k).map f)
      (P.map ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).map f) ≫
        squareZeroPushforwardComparison P Z ι hι W) := by
    rw [← squareZeroUnderRightHom_naturality]
    infer_instance
  refine Functor.IsStronglyCocartesian.ext q
    ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).obj V).hom (P.inclusion _)
    (squareZeroUnderRightHom (q.obj y) V ≫ (artinianSquareZeroExtensionFunctor Λ k).map f) ?_
  rw [← Category.assoc, inclusion_squareZeroPushforwardComparison, hιτ, ← Category.assoc,
    P.inclusion_map, inclusion_squareZeroPushforwardComparison]

/-- Conjugation of a fibre automorphism of the chosen pushforward by the comparison arrow. -/
def squareZeroPushforwardConj (V : FGModuleCat.{u} k)
    (a : Aut (P.obj ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).obj V))) : Z V ⟶ Z V :=
  haveI := isIso_squareZeroPushforwardComparison hcof P Z ι hι V
  ⟨inv (squareZeroPushforwardComparison P Z ι hι V) ≫ a.asIso.hom.1 ≫
    squareZeroPushforwardComparison P Z ι hι V, by
    have := squareZeroPushforwardComparison_isHomLift P Z ι hι V
    have := isIso_squareZeroUnderRightHom (q.obj y) V
    have : q.IsHomLift (asIso (squareZeroUnderRightHom (q.obj y) V)).hom
        (asIso (squareZeroPushforwardComparison P Z ι hι V)).hom :=
      squareZeroPushforwardComparison_isHomLift P Z ι hι V
    have : q.IsHomLift (inv (squareZeroUnderRightHom (q.obj y) V))
        (inv (squareZeroPushforwardComparison P Z ι hι V)) :=
      IsHomLift.inv_lift_inv q (asIso (squareZeroUnderRightHom (q.obj y) V))
        (asIso (squareZeroPushforwardComparison P Z ι hι V))
    have : q.IsHomLift (𝟙 _) a.asIso.hom.1 := a.asIso.hom.2
    have h : q.IsHomLift (inv (squareZeroUnderRightHom (q.obj y) V) ≫ 𝟙 _ ≫
        squareZeroUnderRightHom (q.obj y) V)
        (inv (squareZeroPushforwardComparison P Z ι hι V) ≫ a.asIso.hom.1 ≫
          squareZeroPushforwardComparison P Z ι hι V) := inferInstance
    simpa using h⟩

include hcof hτ hι hιτ in
/-- **Infinitesimal automorphisms of chosen pushforwards are fibre endomorphisms of any compatible
family of pushforwards.** Let `y` be an object of a category cofibered in groupoids over `𝒞_Λ`
with a thin special fibre, `P` a choice of pushforwards of `y`, and `Z V` objects over `k ⊕ V`,
functorial in `V` along arrows `τ`, receiving arrows `ι V` from `y` over the structure maps of
the square-zero extensions and compatible with the `τ`. Then the infinitesimal automorphisms of
the chosen pushforward of `y` to `k ⊕ V` correspond to the endomorphisms of `Z V` in its fibre,
by conjugation with the comparison arrows, and this correspondence turns transport along a
linear map `V ⟶ W` into the transport along `τ`. -/
theorem exists_infinitesimalAutomorphismModuleFunctor_equiv
    (hthin : Quiver.IsThin (q.Fiber (residueFieldObject.{u, u, u} Λ k))) :
    ∃ Φ : ∀ V : FGModuleCat.{u} k,
        (infinitesimalAutomorphismModuleFunctor.{u, u, u} P).obj V ≃ (Z V ⟶ Z V),
      ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W)
        (a : (infinitesimalAutomorphismModuleFunctor.{u, u, u} P).obj V),
        τ f ≫ (Φ W ((infinitesimalAutomorphismModuleFunctor.{u, u, u} P).map f a)).1 =
          (Φ V a).1 ≫ τ f := by
  refine ⟨fun V => Equiv.ofBijective
    (fun a => squareZeroPushforwardConj hcof P Z ι hι V a.1) ⟨?_, ?_⟩, ?_⟩
  · intro a b hab
    have := isIso_squareZeroPushforwardComparison hcof P Z ι hι V
    have h := congrArg (fun t : Z V ⟶ Z V => t.1) hab
    simp only [squareZeroPushforwardConj, cancel_epi, cancel_mono] at h
    exact Subtype.ext (Aut.ext (Iso.ext (Functor.Fiber.hom_ext h)))
  · intro θ
    have := isIso_squareZeroPushforwardComparison hcof P Z ι hι V
    have := isIso_squareZeroUnderRightHom (q.obj y) V
    have : IsIso θ.1 := isIso_of_isHomLift_id hcof θ.1 θ.2
    have := squareZeroPushforwardComparison_isHomLift P Z ι hι V
    have : q.IsHomLift (𝟙 _) θ.1 := θ.2
    let κ := squareZeroPushforwardComparison P Z ι hι V
    let t := κ ≫ θ.1 ≫ inv κ
    have ht : q.IsHomLift (𝟙 ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).obj V).right) t := by
      have h : q.IsHomLift (squareZeroUnderRightHom (q.obj y) V ≫
          𝟙 ((artinianSquareZeroExtensionFunctor Λ k).obj V) ≫
          inv (squareZeroUnderRightHom (q.obj y) V)) t := inferInstance
      simpa using h
    have ht' : q.IsHomLift (𝟙 ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).obj V).right)
        (inv t) := by
      infer_instance
    let a : Aut (P.obj ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).obj V)) :=
      .of { hom := ⟨t, ht⟩
            inv := ⟨inv t, ht'⟩
            hom_inv_id := Functor.Fiber.hom_ext (IsIso.hom_inv_id t)
            inv_hom_id := Functor.Fiber.hom_ext (IsIso.inv_hom_id t) }
    have hmem : a ∈ MonoidHom.ker (P.transportAutHom
        (squareZeroUnderRed.{u, u, u} q y V)) := by
      rw [ker_transportAutHom_squareZeroUnderRed_eq_top hcof P hthin V]
      exact Subgroup.mem_top a
    refine ⟨⟨a, hmem⟩, Functor.Fiber.hom_ext ?_⟩
    change inv κ ≫ (κ ≫ θ.1 ≫ inv κ) ≫ κ = θ.1
    simp
  · intro V W f a
    have := isIso_squareZeroPushforwardComparison hcof P Z ι hι V
    have := isIso_squareZeroPushforwardComparison hcof P Z ι hι W
    have hn := squareZeroPushforwardComparison_naturality P Z τ hτ ι hι hιτ f
    have hτ' : τ f = inv (squareZeroPushforwardComparison P Z ι hι V) ≫
        P.map ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).map f) ≫
          squareZeroPushforwardComparison P Z ι hι W := by
      rw [← hn, IsIso.inv_hom_id_assoc]
    have ht : P.map ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).map f) ≫
        (P.transportAut ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).map f) a.1).asIso.hom.1 =
          a.1.asIso.hom.1 ≫ P.map ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).map f) :=
      P.map_transportHom _ _
    change τ f ≫ inv (squareZeroPushforwardComparison P Z ι hι W) ≫
        (P.transportAut ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).map f) a.1).asIso.hom.1 ≫
          squareZeroPushforwardComparison P Z ι hι W =
      (inv (squareZeroPushforwardComparison P Z ι hι V) ≫ a.1.asIso.hom.1 ≫
        squareZeroPushforwardComparison P Z ι hι V) ≫ τ f
    have h₃ : (inv (squareZeroPushforwardComparison P Z ι hι V) ≫ a.1.asIso.hom.1 ≫
        squareZeroPushforwardComparison P Z ι hι V) ≫ τ f =
          inv (squareZeroPushforwardComparison P Z ι hι V) ≫ a.1.asIso.hom.1 ≫
            P.map ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).map f) ≫
              squareZeroPushforwardComparison P Z ι hι W :=
      (Category.assoc _ _ _).trans (congrArg
        (fun m => inv (squareZeroPushforwardComparison P Z ι hι V) ≫ m)
        ((Category.assoc _ _ _).trans (congrArg (fun m => a.1.asIso.hom.1 ≫ m) hn)))
    have h₂ : P.map ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).map f) ≫
        (P.transportAut ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).map f) a.1).asIso.hom.1 ≫
          squareZeroPushforwardComparison P Z ι hι W =
        a.1.asIso.hom.1 ≫ P.map ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).map f) ≫
          squareZeroPushforwardComparison P Z ι hι W :=
      ((Category.assoc _ _ _).symm.trans (congrArg
        (fun m => m ≫ squareZeroPushforwardComparison P Z ι hι W) ht)).trans
          (Category.assoc _ _ _)
    have h₁ : τ f ≫ inv (squareZeroPushforwardComparison P Z ι hι W) ≫
        (P.transportAut ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).map f) a.1).asIso.hom.1 ≫
          squareZeroPushforwardComparison P Z ι hι W =
        inv (squareZeroPushforwardComparison P Z ι hι V) ≫
          P.map ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).map f) ≫
            (P.transportAut ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).map f) a.1).asIso.hom.1 ≫
              squareZeroPushforwardComparison P Z ι hι W := by
      rw [hτ']
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact h₁.trans ((congrArg (fun m => inv (squareZeroPushforwardComparison P Z ι hι V) ≫ m)
      h₂).trans h₃.symm)

end PushforwardComparison

section CompatibleArrows

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {q : F ⥤ ArtinianLocalAlgCat.{u, u, u} Λ k}

/-- In a predeformation category, an object `y` over the residue field maps compatibly to every
functorial family `Z V` of objects over the trivial square-zero extensions `k ⊕ V`, over the
structure maps `k ⟶ k ⊕ V`: map `y` to `Z 0`, which lies over an isomorphic copy of `k`, and
compose with the transition arrows out of `Z 0`. -/
theorem exists_compatible_arrows_squareZero (hq : IsPredeformationCategory.{u, u, u} q) {y : F}
    (hy : q.obj y = residueFieldObject.{u, u, u} Λ k)
    (Z : ∀ V : FGModuleCat.{u} k, q.Fiber ((artinianSquareZeroExtensionFunctor Λ k).obj V))
    (τ : ∀ {V W : FGModuleCat.{u} k} (_ : V ⟶ W), (Z V).1 ⟶ (Z W).1)
    (hτ : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W),
      q.IsHomLift ((artinianSquareZeroExtensionFunctor Λ k).map f) (τ f))
    (hτcomp : ∀ {V W Y : FGModuleCat.{u} k} (f : V ⟶ W) (g : W ⟶ Y), τ (f ≫ g) = τ f ≫ τ g) :
    ∃ ι : ∀ V : FGModuleCat.{u} k, y ⟶ (Z V).1,
      (∀ V : FGModuleCat.{u} k, q.IsHomLift (((squareZeroAlgFunctor.{u, u, u} (q.obj y)).obj
        V).hom ≫ squareZeroUnderRightHom (q.obj y) V) (ι V)) ∧
      ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W), ι V ≫ τ f = ι W := by
  let V₀ := FGModuleCat.of k PUnit.{u + 1}
  let g₀ := ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).obj V₀).hom ≫
    squareZeroUnderRightHom (q.obj y) V₀
  have : IsIso g₀ :=
    ArtinianLocalAlgCat.isIso_of_bijective_hom _ (bijective_squareZeroUnder_zero_hom _ hy)
  obtain ⟨ι₀, hι₀⟩ := exists_isHomLift_of_isIso hq g₀ rfl hy (Z V₀).2
  refine ⟨fun V => ι₀ ≫ τ (0 : V₀ ⟶ V), fun V => ?_, fun {V W} f => ?_⟩
  · have := hι₀
    have := hτ (0 : V₀ ⟶ V)
    have h : q.IsHomLift (g₀ ≫ (artinianSquareZeroExtensionFunctor Λ k).map (0 : V₀ ⟶ V))
      (ι₀ ≫ τ (0 : V₀ ⟶ V)) := inferInstance
    have hb : g₀ ≫ (artinianSquareZeroExtensionFunctor Λ k).map (0 : V₀ ⟶ V) =
        ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).obj V).hom ≫
          squareZeroUnderRightHom (q.obj y) V := by
      rw [Category.assoc, ← squareZeroUnderRightHom_naturality, ← Category.assoc,
        Under.w ((squareZeroAlgFunctor.{u, u, u} (q.obj y)).map (0 : V₀ ⟶ V))]
    rwa [hb] at h
  · change (ι₀ ≫ τ (0 : V₀ ⟶ V)) ≫ τ f = ι₀ ≫ τ (0 : V₀ ⟶ W)
    rw [Category.assoc, ← hτcomp, zero_comp]

end CompatibleArrows

end Deformation

namespace Deformation.Artin

open AlgebraicGeometry

section TangentComparison

attribute [local instance] PredeformationConstruction.category

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (iΛ : Spec (.of Λ) ⟶ S) (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (x₀ : X)
  (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hx : p.obj x₀ = algebraOver k B S hS toS hk)

include hp in
/-- **Stacks Project, Tag 0D18, tangent spaces, for any tangent functor.** Let `T` be an
`A`-linear functor on the site modules whose values are identified with the classes of lifts of
`x₀`, compatibly with pullback, and suppose that the predeformation category `𝓕_{𝒳,k,x₀}` is a
deformation category. Then the tangent space of `𝓕_{𝒳,k,x₀}` is the value of `T` at the
rank-one vector space, by a `k`-linear equivalence carrying the class of a deformation to the
class of the corresponding lift. Neither (RS*) nor a finiteness condition on `k` is assumed. -/
public theorem tangentSpace_deformationCategory_linearEquiv_of_tangentFunctorData
    (T : TangentFunctorData k B S hS toS hk p x₀ hx)
    (hD : IsDeformationCategory.{u, u, u}
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    let D := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
    let 𝓕 := BasedCategory.ofFunctor D.projection
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨tangentConditionS2.{u, u, u} hD⟩
    let M : SiteModule k B := (fgSiteModule B hk).obj (FGModuleCat.of k k)
    ∃ e : artinianTangentSpace Λ k (isomorphismClasses 𝓕 hD.predeformation.cofibered) ≃ₗ[k]
        T.functor.obj M,
      ∀ z : D.projection.Fiber ((artinianSquareZeroExtensionFunctor Λ k).obj
          (FGModuleCat.of k k)),
        ∃ y : (Under.post p).Fiber
            (Under.mk (eqToHom hx ≫ squareZeroArrow k B S hS toS hk M)),
          T.liftEquiv M (e (classOf 𝓕 hD.predeformation.cofibered z)) = Quotient.mk _ y ∧
            ∃ (η : y.1.right ≅ (D.objects z.1).point)
              (hbase : p.obj y.1.right = p.obj (D.objects z.1).point),
              p.map η.hom = eqToHom hbase ∧
                y.1.hom ≫ η.hom = (D.objects z.1).arrow := by
  intro D 𝓕 M
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
  let : Fact (SchlessingerConditionS2 (Functor.Elements.π
    (isomorphismClasses 𝓕 hD.predeformation.cofibered))) :=
    ⟨tangentConditionS2.{u, u, u} (𝓕 := 𝓕) hD⟩
  obtain ⟨c, hc₁, hc₂⟩ := exists_deformationClassEquiv_squareZeroLiftClasses B S hS iΛ toS hk p
    hp x₀ hx₀ hx hD.predeformation.cofibered
  let L := associatedTangentSpaceModuleStructureUnlifted 𝓕 hD.predeformation
    (tangentConditionS2.{u, u, u} (𝓕 := 𝓕) hD)
  have : (fgSiteModule B hk).Additive := ⟨rfl⟩
  have : (fgSiteModule B hk).Linear k := ⟨by intros; rfl⟩
  refine (exists_linearEquiv_of_natural_equiv L (fgSiteModule B hk ⋙ T.functor)
    (fun V => (c V).trans (T.liftEquiv _).symm) (fun f a => ?_) (FGModuleCat.of k k)).elim
    fun E hE => ?_
  · apply (T.liftEquiv _).injective
    have hnat := T.liftEquiv_natural ((fgSiteModule B hk).map f)
      ((c _).trans (T.liftEquiv _).symm a)
    rw [Equiv.trans_apply, Equiv.apply_symm_apply] at hnat
    exact (Equiv.apply_symm_apply _ _).trans (hc₂ f a _ hnat)
  refine ⟨(eqRecModuleDataLinearEquiv (associatedTangentSpaceModuleStructure_carrierUnlifted _
    hD.predeformation (tangentConditionS2.{u, u, u} (𝓕 := 𝓕) hD)) ⟨_, _⟩).symm.trans E, fun z => ?_⟩
  obtain ⟨y, hy, hrest⟩ := hc₁ (FGModuleCat.of k k) z
  refine ⟨y, ?_, hrest⟩
  change T.liftEquiv M (E (cast _ (classOf 𝓕 hD.predeformation.cofibered z))) = _
  rw [hE, Equiv.trans_apply, Equiv.apply_symm_apply]
  have hcc : ∀ {α β : Type (max (u + 1) v w)} (h : α = β) (h' : β = α) (t : α),
      cast h' (cast h t) = t := by
    intro α β h h' t
    subst h
    rfl
  exact (congrArg (c (FGModuleCat.of k k)) (hcc _ _ _)).trans hy

include hp in
/-- **The tangent space of `𝓕_{𝒳,k,x₀}` controls the tangent functor.** If the tangent space
of the deformation category of `x₀` is finite-dimensional, so is the value at the rank-one
vector space of any tangent functor of `x₀`. -/
public theorem finiteDimensional_tangentFunctorData_of_artinianTangentSpace
    (T : TangentFunctorData k B S hS toS hk p x₀ hx)
    (hD : IsDeformationCategory.{u, u, u}
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection).p) :=
      ⟨hD.predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (BasedCategory.ofFunctor
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
          hD.predeformation.cofibered))) := ⟨tangentConditionS2.{u, u, u} hD⟩
    FiniteDimensional k (artinianTangentSpace Λ k (isomorphismClasses (BasedCategory.ofFunctor
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
          hD.predeformation.cofibered)) →
      FiniteDimensional k (T.functor.obj ((fgSiteModule B hk).obj (FGModuleCat.of k k))) := by
  intro hfin
  let : Fact (IsPredeformationCategory (BasedCategory.ofFunctor
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection).p) :=
    ⟨hD.predeformation⟩
  let : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (BasedCategory.ofFunctor
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
          hD.predeformation.cofibered))) := ⟨tangentConditionS2.{u, u, u} hD⟩
  obtain ⟨e, -⟩ := tangentSpace_deformationCategory_linearEquiv_of_tangentFunctorData B S hS iΛ
    toS hk p hp x₀ hx₀ hx T hD
  exact e.finiteDimensional

end TangentComparison

section InfinitesimalComparison

attribute [local instance] PredeformationConstruction.category

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (iΛ : Spec (.of Λ) ⟶ S) (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (x₀ : X)
  (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hx : p.obj x₀ = algebraOver k B S hS toS hk)

include hp in
/-- **Stacks Project, Tag 0D18, infinitesimal automorphisms, for any `Inf` functor.** Let `I` be
a `k`-linear functor on the site modules whose values are identified with the infinitesimal
automorphisms of the trivial deformations of `x₀`, naturally, and suppose that the
predeformation category `𝓕_{𝒳,k,x₀}` is a deformation category. For any object `y` of its
special fibre and any choice `P` of pushforwards of `y`, the canonical linear lift of the
infinitesimal automorphisms of the pushforwards of `y` to the square-zero extensions `k ⊕ V`
(Stacks 06IA) is `k`-linearly identified with `I` at every finite-dimensional `V`. Neither (RS*)
nor a finiteness condition on `k` is assumed. -/
public theorem nonempty_linearEquiv_infinitesimalAutomorphismLinearLift
    (I : InfinitesimalAutomorphismFunctorData k B S hS toS hk p x₀ hx hp)
    (hD : IsDeformationCategory.{u, u, u}
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
    (y : (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).carrier)
    (hy : (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection.obj y =
      residueFieldObject.{u, u, u} Λ k)
    (P : ChosenPushforwardsAt
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection y)
    (V : FGModuleCat.{u} k) :
    Nonempty (((infinitesimalAutomorphismLinearLift.{u, u, u} P hD.satisfiesRS).functor.obj V :
        ModuleCat k) ≃ₗ[k] I.functor.obj ((fgSiteModule B hk).obj V)) := by
  obtain ⟨Z, τ, ψ, hτ, hτcomp, hψ⟩ :=
    exists_trivialDeformationFunctor_infinitesimalAutomorphisms B S hS iΛ toS hk p hp x₀ hx₀ hx
  obtain ⟨ι, hι, hιτ⟩ := exists_compatible_arrows_squareZero hD.predeformation hy Z
    (fun f => τ f) hτ hτcomp
  obtain ⟨Φ, hΦ⟩ := exists_infinitesimalAutomorphismModuleFunctor_equiv
    hD.predeformation.cofibered P Z (fun f => τ f) hτ ι hι hιτ
    (isThin_specialFiber hD.predeformation)
  let L := infinitesimalAutomorphismLinearLift.{u, u, u} P hD.satisfiesRS
  have : (fgSiteModule B hk).Additive := ⟨rfl⟩
  have : (fgSiteModule B hk).Linear k := ⟨by intros; rfl⟩
  refine (exists_linearEquiv_of_natural_equiv L (fgSiteModule B hk ⋙ I.functor)
    (fun V => (Φ V).trans ((ψ V).trans (I.autEquiv _).symm)) (fun f a => ?_) V).elim
    fun E _ => ⟨E⟩
  apply (I.autEquiv _).injective
  refine ((I.autEquiv _).apply_symm_apply _).trans ?_
  refine (hψ f _ _ (hΦ f _)).trans ?_
  refine (congrArg _ ((I.autEquiv _).apply_symm_apply _).symm).trans ?_
  exact (I.autEquiv_natural _ _).symm

include hp in
/-- **The infinitesimal automorphisms of `𝓕_{𝒳,k,x₀}` control the `Inf` functor.** If, at one
object of the special fibre of the deformation category of `x₀` and one choice of its
pushforwards, the infinitesimal automorphisms over the dual numbers form a finite-dimensional
vector space, then so does the value at the rank-one vector space of any `Inf` functor of
`x₀`. -/
public theorem finiteDimensional_infinitesimalAutomorphismFunctorData_of_linearLift
    (I : InfinitesimalAutomorphismFunctorData k B S hS toS hk p x₀ hx hp)
    (hD : IsDeformationCategory.{u, u, u}
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
    (y : (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).carrier)
    (hy : (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection.obj y =
      residueFieldObject.{u, u, u} Λ k)
    (P : ChosenPushforwardsAt
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection y)
    (hfin : FiniteDimensional k ↥((infinitesimalAutomorphismLinearLift.{u, u, u} P
      hD.satisfiesRS).functor.obj (FGModuleCat.of k (ULift.{u} k)))) :
    FiniteDimensional k (I.functor.obj ((fgSiteModule B hk).obj (FGModuleCat.of k k))) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_infinitesimalAutomorphismLinearLift B S hS iΛ toS hk p hp
    x₀ hx₀ hx I hD y hy P (FGModuleCat.of k (ULift.{u} k))
  have := hfin
  have := e.finiteDimensional
  exact (I.functor.mapIso ((fgSiteModule B hk).mapIso
    fgModuleCatULiftSelfIso)).toLinearEquiv.finiteDimensional

include hp in
/-- **The infinitesimal automorphisms of `𝓕_{𝒳,k,x₀}` control the `Inf` functor**, in the form
in which finite-dimensionality is available for every object of the special fibre and every
choice of its pushforwards. -/
public theorem finiteDimensional_infinitesimalAutomorphismFunctorData
    (I : InfinitesimalAutomorphismFunctorData k B S hS toS hk p x₀ hx hp)
    (hD : IsDeformationCategory.{u, u, u}
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
    (hfin : ∀ y, (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection.obj
        y = residueFieldObject.{u, u, u} Λ k →
      ∀ P : ChosenPushforwardsAt
          (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection y,
        FiniteDimensional k ↥((infinitesimalAutomorphismLinearLift.{u, u, u} P
          hD.satisfiesRS).functor.obj (FGModuleCat.of k (ULift.{u} k)))) :
    FiniteDimensional k (I.functor.obj ((fgSiteModule B hk).obj (FGModuleCat.of k k))) := by
  obtain ⟨E⟩ := hD.predeformation.specialFiber
  let y := E.inverse.obj ⟨PUnit.unit⟩
  let hcof := hD.predeformation.cofibered
  let P : ChosenPushforwardsAt
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection y.1 :=
    ChosenPushforwardsAt.ofCofiberedInGroupoids hcof
      (fun A => ⟨pushforwardObj hcof A.hom y.1 rfl, pushforwardObj_eq hcof A.hom y.1 rfl⟩)
      (fun A => chosenPushforwardMap hcof A.hom y.1 rfl)
      (fun A => chosenPushforwardMap_lift hcof A.hom y.1 rfl)
  exact finiteDimensional_infinitesimalAutomorphismFunctorData_of_linearLift B S hS iΛ toS hk p
    hp x₀ hx₀ hx I hD y.1 y.2 P (hfin y.1 y.2 P)

end InfinitesimalComparison

end Deformation.Artin
