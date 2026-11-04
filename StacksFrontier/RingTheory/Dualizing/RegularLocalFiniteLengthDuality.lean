module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Perfect.Duality
public import StacksFrontier.Homology.Perfect.Regular
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.HomShift.DerivedShift
public import StacksFrontier.RingTheory.Dualizing.FiniteLengthMatlisDuality
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.RingTheory.Dualizing.RegularLocalNormalizedShift
public import StacksFrontier.RingTheory.Dualizing.ScalarTransportComparisons
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension

/-!
# Duality for finite-length modules over a regular local ring

Let `(A, 𝔪, κ)` be a regular local ring of dimension `d`, let `N` be an `A`-module of finite
length and let `N'` be a Matlis dual of `N`, that is a module isomorphic to `Hom_A(N, E)` for an
injective hull `E` of `κ`. Then

`Hom_{D(A)}(N, K) = H⁰(K ⊗^L_A N'[-d])`

functorially in `K`. This is the duality at a point to which [stacks 0G02] reduces its statement
about a coherent sheaf supported at a closed point of a regular scheme of finite type over a
field, the ring `A` being the local ring of the scheme at that point.

The proof follows the source. A finite module over a regular ring is perfect ([stacks 066Z]), so
perfect duality ([stacks 07VI]) gives `Hom_{D(A)}(N, K) = H⁰(K ⊗^L_A RHom_A(N, A))` functorially
in `K`; and `RHom_A(N, A) = N'[-d]` by Matlis duality against a normalized dualizing complex
([stacks 0A7Q]), the regular module shifted by the dimension being such a complex because a
regular local ring is Gorenstein ([stacks 0AWX]).

## Main results

* `StacksDraft.Perfect.isPerfect_single_of_finite_regularLocal` — a finite module over a regular
  local ring is a perfect object of the derived category.
* `StacksDraft.Perfect.isPerfect_inverse_derivedScalarEquivalence` — perfectness travels back
  along the scalar transport to the derived category of modules over the lifted ring.
* `Dualizing.nonempty_derivedHom_single_iso_matlisDual_shift` — `RHom_A(N, ω) ≅ N'[-d]` for a
  finite-length module `N` and a target whose shift by `d` is a normalized dualizing complex.
* `Dualizing.exists_shift_derivedHom_single_self_iso_matlisDual` — `RHom_A(N, A) ≅ N'[-d]` over a
  regular local ring, for the normalizing shift `d` of the regular module.
* `Dualizing.exists_addEquiv_hom_homology_derivedTensor_matlisDual` — the duality itself:
  `Hom_{D(A)}(N, K) ≃+ H⁰(K ⊗^L_A N'[-d])` functorially in `K`, with `d = dim(A)`.

## Implementation notes

[stacks 07VI] is stated over `ULift A`, since Mathlib's monoidal category of modules forces the
ring and module universes to agree, while the dualizing-complex development uses the derived
tensor--Hom adjunction `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` on `D(A)` itself.
The two are compared by `StacksDraft.DerivedHom.derivedTensorULiftIso` and
`StacksDraft.DerivedHom.derivedHomULiftIso`, the transports of the one adjunction along the
scalar equivalence of derived categories; cohomology and morphism groups are carried across by
`StacksDraft.DerivedHom.scalarHomologyAddEquiv` and
`StacksDraft.DerivedHom.equivalenceHomAddEquiv`. All statements here are therefore phrased for
`A`-modules, with the derived tensor product and derived Hom of that adjunction.

The functoriality in `K` is phrased as [stacks 07VI] phrases its own degree-zero clause: a family
of additive isomorphisms together with the naturality square, rather than an isomorphism of
functors, because the two sides live in different universes.

The hypotheses follow the source: the Matlis dual `N'` and its defining isomorphism are
arguments, as in "choose a coherent module `F'` whose stalk is Matlis dual to `F_x`", rather than
chosen from an existence statement. The module universe is the universe of the ring, as in
[stacks 0AWX], whose Gorenstein predicate is stated for `ModuleCat.{u} A`; the derived category is
the standard model, forced by `Dualizing.IsNormalizedDualizingComplex`.

## References

* [Stacks Project, Tag 0G02](https://stacks.math.columbia.edu/tag/0G02)
* [Stacks Project, Tag 066Z](https://stacks.math.columbia.edu/tag/066Z)
* [Stacks Project, Tag 07VI](https://stacks.math.columbia.edu/tag/07VI)
* [Stacks Project, Tag 0A7Q](https://stacks.math.columbia.edu/tag/0A7Q)
* [Stacks Project, Tag 0AWX](https://stacks.math.columbia.edu/tag/0AWX)
-/

@[expose] public noncomputable section

open CategoryTheory StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

universe u v

namespace StacksDraft.Perfect

/-- **A finite module over a regular local ring is perfect.** A regular local ring is a regular
ring, and over a regular ring the perfect modules are exactly the finite ones. -/
public theorem isPerfect_single_of_finite_regularLocal
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (N : ModuleCat.{max u v} A) [Module.Finite A N] :
    IsPerfect ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N) := by
  let : IsRegularRing A :=
    ((IsLocalRing.isRegularRing_tfae (R := A)).out 1 3).mp
      (inferInstance : IsRegularLocalRing A)
  exact ((isPerfectModule_iff_finite_and_isPerfect_iff_bounded_finiteCohomology.{u, v}
    (R := A)).1 N).2 inferInstance

/-- The identity map, as a semilinear equivalence from a module onto the same module with its
scalars restricted along the canonical isomorphism from the lifted ring. -/
private def identityRestrictScalarsULift (A : Type u) [CommRing A] (M : ModuleCat.{max u v} A) :
    LinearEquiv (R := A) (S := ULift.{v} A)
      (σ' := ↑(ULift.ringEquiv : ULift.{v} A ≃+* A))
      (↑(ULift.ringEquiv : ULift.{v} A ≃+* A).symm) M
      ((ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom).obj M) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Perfectness travels back along the scalar transport.** A bounded complex of finite
projective `A`-modules representing a perfect object becomes such a complex over the lifted
ring, the scalars being restricted along a ring isomorphism. -/
public theorem isPerfect_inverse_derivedScalarEquivalence (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{max u v} A)) (hK : IsPerfect K) :
    IsPerfect ((derivedScalarEquivalence.{u, v, max u v + 1} A).inverse.obj K) := by
  obtain ⟨P, a, b, ha, hb, hfin, hproj, ⟨j⟩⟩ := hK
  let F := (uliftModuleEquivalence.{u, max u v, v} A).inverse
  let := ha
  let := hb
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P, a, b, inferInstance,
    inferInstance, ?_, ?_, ⟨?_⟩⟩
  · intro n
    let := hfin n
    exact Module.Finite.of_surjective (identityRestrictScalarsULift.{u, v} A (P.X n)).toLinearMap
      (identityRestrictScalarsULift.{u, v} A (P.X n)).surjective
  · intro n
    let := hproj n
    exact Module.Projective.of_equiv (identityRestrictScalarsULift.{u, v} A (P.X n))
  · exact (derivedScalarEquivalence.{u, v, max u v + 1} A).inverse.mapIso j ≪≫
      F.mapDerivedCategoryFactors.app P

/-- **Perfect duality for a finite module over a regular local ring.** The derived dual
`RHom_A(N, A)` is perfect, biduality is an isomorphism, the canonical comparison
`K ⊗^L_A RHom_A(N, A) ⟶ RHom_A(N, K)` is an isomorphism functorially in `K`, and in degree zero
`H⁰(K ⊗^L_A RHom_A(N, A)) ≃+ Hom_{D(A)}(N, K)` functorially in `K`. -/
public theorem perfectDerivedDuality_single_of_finite_regularLocal
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (N : ModuleCat.{max u v} A) [Module.Finite A N] :
    PerfectDerivedDuality
      ((derivedScalarEquivalence.{u, v, max u v + 1} A).inverse.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N)) :=
  isPerfect_derivedDual_and_naturalIsos _
    (isPerfect_inverse_derivedScalarEquivalence.{u, v} A _
      (isPerfect_single_of_finite_regularLocal.{u, v} A N))

end StacksDraft.Perfect

namespace Dualizing

/-- **Derived Hom from a finite-length module is the shifted Matlis dual.** If `ω⟦d⟧` is a
normalized dualizing complex over a Noetherian local ring `A`, `N` has finite length and `N'` is
a Matlis dual of `N` with respect to an injective hull `E` of the residue field, then
`RHom_A(N, ω) ≅ N'[-d]`. -/
public theorem nonempty_derivedHom_single_iso_matlisDual_shift
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (ω : DerivedCategory (ModuleCat.{max v u} A)) (d : ℤ)
    (hω : IsNormalizedDualizingComplex.{u, v} (ω⟦d⟧))
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (N N' : ModuleCat.{max v u} A) (hN : IsFiniteLength A N)
    (hdual : Nonempty (N' ≅ ModuleCat.of A (N ⟶ E))) :
    Nonempty
      ((derivedHomAdjunctionOverRing A).hom.obj
          (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj N), ω) ≅
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj N')⟦-d⟧) := by
  obtain ⟨Φ⟩ := derivedHomFiniteLengthIsoMatlisDual.{u, v} A _ hω E i hi
  have e : (derivedHomAdjunctionOverRing A).hom.obj
        (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj N), ω⟦d⟧) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A (N ⟶ E)) :=
    Φ.app (Opposite.op (⟨N, hN⟩ : FiniteLengthModules.{u, v} A))
  have s := dualizingDerivedHomShift.{u, v} A ω d
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj N)
  exact ⟨((shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{max v u} A)) d (-d)
        (by omega)).app _).symm ≪≫
    (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (-d)).mapIso (s.symm ≪≫ e) ≪≫
    (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (-d)).mapIso
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).mapIso hdual.some).symm⟩

/-- **Over a regular local ring some shift of the regular module is a normalized dualizing
complex.** The regular module in degree zero is dualizing because a regular local ring is
Gorenstein, and a dualizing complex over a Noetherian local ring has a normalizing shift. -/
public theorem exists_isNormalizedDualizingComplex_shift_single_self
    (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    ∃ d : ℤ, IsNormalizedDualizingComplex.{u, 0}
      (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))⟦d⟧) := by
  obtain ⟨m, hm⟩ := exists_isNormalizedDualizingComplex_shift.{u, 0}
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
    (IsRegularLocalRing.isGorensteinLocalRing A)
  exact ⟨-m, hm⟩

/-- **Derived Hom from a finite-length module into the regular module, over a regular local
ring.** For the normalizing shift `d` of the regular module, derived Hom from a finite-length
module `N` into `A` is a Matlis dual of `N` placed in degree `d`: `RHom_A(N, A) ≅ N'[-d]`. -/
public theorem exists_shift_derivedHom_single_self_iso_matlisDual
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (E : ModuleCat.{u} A)
    (i : (ModuleCat.uliftFunctor.{0} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (N N' : ModuleCat.{u} A) (hN : IsFiniteLength A N)
    (hdual : Nonempty (N' ≅ ModuleCat.of A (N ⟶ E))) :
    ∃ d : ℤ, Nonempty
      ((derivedHomAdjunctionOverRing.{u, 0, u + 1} A).hom.obj
          (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N),
            (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ≅
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N')⟦-d⟧) := by
  obtain ⟨d, hd⟩ := exists_isNormalizedDualizingComplex_shift_single_self A
  exact ⟨d, nonempty_derivedHom_single_iso_matlisDual_shift.{u, 0} A _ d hd E i hi N N' hN hdual⟩

/-- The derived dual `RHom_A(X, A)` of an object of `D(A)`, computed through the scalar transport
to the derived category of modules over the lifted ring. -/
private abbrev dualOverRing (A : Type u) [CommRing A]
    (X : DerivedCategory (ModuleCat.{u} A)) : DerivedCategory (ModuleCat.{u} A) :=
  (derivedScalarEquivalence.{u, 0, u + 1} A).functor.obj
    (StacksDraft.Perfect.derivedDual
      ((derivedScalarEquivalence.{u, 0, u + 1} A).inverse.obj X))

/-- Composition with isomorphisms, as an additive bijection of morphism groups. -/
private def homIsoAddEquiv {C : Type*} [Category C] [Preadditive C] {X X' Y Y' : C}
    (α : X ≅ X') (β : Y ≅ Y') : (X ⟶ Y) ≃+ (X' ⟶ Y') where
  toFun g := α.inv ≫ g ≫ β.hom
  invFun g := α.hom ≫ g ≫ β.inv
  left_inv g := by simp
  right_inv g := by simp
  map_add' g h := by
    simp only [Preadditive.add_comp, Preadditive.comp_add]

/-- The value of the morphism-group bijection attached to a pair of isomorphisms. -/
private theorem homIsoAddEquiv_apply {C : Type*} [Category C] [Preadditive C]
    {X X' Y Y' : C} (α : X ≅ X') (β : Y ≅ Y') (g : X ⟶ Y) :
    homIsoAddEquiv α β g = α.inv ≫ g ≫ β.hom := rfl

/-- The additive bijection of underlying groups attached to an isomorphism of modules. -/
private def moduleIsoAddEquiv {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (α : M ≅ N) :
    (M : Type u) ≃+ (N : Type u) where
  toFun a := α.hom a
  invFun a := α.inv a
  left_inv a := ConcreteCategory.congr_hom α.hom_inv_id a
  right_inv a := ConcreteCategory.congr_hom α.inv_hom_id a
  map_add' a b := (α.hom).hom.map_add a b

/-- The value of the bijection of underlying groups attached to an isomorphism of modules. -/
private theorem moduleIsoAddEquiv_apply {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (α : M ≅ N)
    (a : M) : moduleIsoAddEquiv α a = α.hom a := rfl

/-- The derived tensor product `L ⊗^L_A D` by a fixed object presented as the scalar transport of
an object `W`, identified with the scalar transport of `L ⊗^L W` over the lifted ring. -/
private def tensorScalarIso (A : Type u) [CommRing A]
    (W : DerivedCategory (ModuleCat.{u} (ULift.{0} A)))
    (D : DerivedCategory (ModuleCat.{u} A))
    (ψ : (derivedScalarEquivalence.{u, 0, u + 1} A).functor.obj W ≅ D)
    (L : DerivedCategory (ModuleCat.{u} A)) :
    (derivedHomAdjunctionOverRing.{u, 0, u + 1} A).tensor.obj (L, D) ≅
      (derivedScalarEquivalence.{u, 0, u + 1} A).functor.obj
        ((derivedHomAdjunctionULift.{u, 0, u + 1} (R := A)).tensor.obj
          ((derivedScalarEquivalence.{u, 0, u + 1} A).inverse.obj L, W)) :=
  (derivedHomAdjunctionOverRing.{u, 0, u + 1} A).tensor.mapIso
      (((derivedScalarEquivalence.{u, 0, u + 1} A).counitIso.app L).symm.prod ψ.symm) ≪≫
    (derivedTensorULiftIso.{u, 0, u + 1} A).app
      ((derivedScalarEquivalence.{u, 0, u + 1} A).inverse.obj L, W)

/-- The identification of derived tensor products is natural in the first variable. -/
private theorem tensorScalarIso_naturality (A : Type u) [CommRing A]
    (W : DerivedCategory (ModuleCat.{u} (ULift.{0} A)))
    (D : DerivedCategory (ModuleCat.{u} A))
    (ψ : (derivedScalarEquivalence.{u, 0, u + 1} A).functor.obj W ≅ D)
    {L L' : DerivedCategory (ModuleCat.{u} A)} (f : L ⟶ L') :
    (derivedHomAdjunctionOverRing.{u, 0, u + 1} A).tensor.map (f, 𝟙 D) ≫
        (tensorScalarIso A W D ψ L').hom =
      (tensorScalarIso A W D ψ L).hom ≫
        (derivedScalarEquivalence.{u, 0, u + 1} A).functor.map
          ((derivedHomAdjunctionULift.{u, 0, u + 1} (R := A)).tensor.map
            ((derivedScalarEquivalence.{u, 0, u + 1} A).inverse.map f, 𝟙 W)) := by
  let E := derivedScalarEquivalence.{u, 0, u + 1} A
  have hprod : ((f, 𝟙 D) : (L, D) ⟶ (L', D)) ≫
        ((E.counitIso.app L').symm.prod ψ.symm).hom =
      ((E.counitIso.app L).symm.prod ψ.symm).hom ≫
        ((E.functor.map (E.inverse.map f), E.functor.map (𝟙 W)) :
          (E.functor.obj (E.inverse.obj L), E.functor.obj W) ⟶
            (E.functor.obj (E.inverse.obj L'), E.functor.obj W)) := by
    refine Prod.ext ?_ ?_
    · exact E.counitIso.inv.naturality f
    · simp [E]
  have hnat := (derivedTensorULiftIso.{u, 0, u + 1} A).hom.naturality
    ((E.inverse.map f, 𝟙 W) : (E.inverse.obj L, W) ⟶ (E.inverse.obj L', W))
  dsimp only [tensorScalarIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp, hprod, Functor.map_comp, Category.assoc]
  erw [hnat]
  rw [Category.assoc]
  rfl

/-- **Degree-zero perfect duality over the ring itself.** For a perfect object `X` of `D(A)` and
an object `D` isomorphic to its derived dual there are additive isomorphisms
`H⁰(L ⊗^L_A D) ≃+ Hom_{D(A)}(X, L)`, natural in `L`. -/
private theorem exists_addEquiv_homology_derivedTensor_dual (A : Type u) [CommRing A]
    (X : DerivedCategory (ModuleCat.{u} A)) (hX : StacksDraft.Perfect.IsPerfect X)
    (D : DerivedCategory (ModuleCat.{u} A)) (ψ : dualOverRing A X ≅ D) :
    ∃ e : ∀ L : DerivedCategory (ModuleCat.{u} A),
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
            ((derivedHomAdjunctionOverRing.{u, 0, u + 1} A).tensor.obj (L, D))) : Type u) ≃+
          (X ⟶ L),
      ∀ (L L' : DerivedCategory (ModuleCat.{u} A)) (f : L ⟶ L')
        (a : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          ((derivedHomAdjunctionOverRing.{u, 0, u + 1} A).tensor.obj (L, D))),
        e L' ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
            ((derivedHomAdjunctionOverRing.{u, 0, u + 1} A).tensor.map (f, 𝟙 D)) a) =
          e L a ≫ f := by
  set E := derivedScalarEquivalence.{u, 0, u + 1} A with hE
  set d' := derivedHomAdjunctionULift.{u, 0, u + 1} (R := A) with hd'
  set H0A := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 with hH0A
  set H0U := DerivedCategory.homologyFunctor (ModuleCat.{u} (ULift.{0} A)) 0 with hH0U
  set W := StacksDraft.Perfect.derivedDual (E.inverse.obj X) with hW
  obtain ⟨e, he⟩ := (StacksDraft.Perfect.isPerfect_derivedDual_and_naturalIsos
    (E.inverse.obj X)
    (StacksDraft.Perfect.isPerfect_inverse_derivedScalarEquivalence.{u, 0} A X
      hX)).exists_extZeroEquiv
  have he' : ∀ {M M' : DerivedCategory (ModuleCat.{u} (ULift.{0} A))} (g : M ⟶ M')
      (b : H0U.obj (d'.tensor.obj (M, W))),
      e M' (H0U.map (d'.tensor.map ((g, 𝟙 W) :
          ((M, W) : DerivedCategory (ModuleCat.{u} (ULift.{0} A)) ×
            DerivedCategory (ModuleCat.{u} (ULift.{0} A))) ⟶ (M', W))) b) = e M b ≫ g :=
    fun g b => he g b
  refine ⟨fun L =>
    (moduleIsoAddEquiv (H0A.mapIso (tensorScalarIso A W D ψ L))).trans
      ((scalarHomologyAddEquiv.{u, 0} A (d'.tensor.obj (E.inverse.obj L, W)) 0).trans
        ((e (E.inverse.obj L)).trans
          ((equivalenceHomAddEquiv E (E.inverse.obj X) (E.inverse.obj L)).trans
            (homIsoAddEquiv (E.counitIso.app X) (E.counitIso.app L))))), ?_⟩
  intro L L' f a
  have key : scalarHomologyAddEquiv.{u, 0} A (d'.tensor.obj (E.inverse.obj L', W)) 0
        (moduleIsoAddEquiv (H0A.mapIso (tensorScalarIso A W D ψ L'))
          (H0A.map ((derivedHomAdjunctionOverRing.{u, 0, u + 1} A).tensor.map (f, 𝟙 D)) a)) =
      H0U.map (d'.tensor.map ((E.inverse.map f, 𝟙 W) :
          ((E.inverse.obj L, W) : DerivedCategory (ModuleCat.{u} (ULift.{0} A)) ×
            DerivedCategory (ModuleCat.{u} (ULift.{0} A))) ⟶ (E.inverse.obj L', W)))
        (scalarHomologyAddEquiv.{u, 0} A (d'.tensor.obj (E.inverse.obj L, W)) 0
          (moduleIsoAddEquiv (H0A.mapIso (tensorScalarIso A W D ψ L)) a)) := by
    rw [moduleIsoAddEquiv_apply, moduleIsoAddEquiv_apply]
    change scalarHomologyAddEquiv.{u, 0} A (d'.tensor.obj (E.inverse.obj L', W)) 0
        (H0A.map (tensorScalarIso A W D ψ L').hom
          (H0A.map ((derivedHomAdjunctionOverRing.{u, 0, u + 1} A).tensor.map (f, 𝟙 D)) a)) = _
    rw [← Functor.map_comp_apply, tensorScalarIso_naturality A W D ψ f,
      Functor.map_comp_apply]
    exact scalarHomologyAddEquiv_naturality.{u, 0} A _ 0 _
  have hcounit : E.functor.map (E.inverse.map f) ≫ (E.counitIso.app L').hom =
      (E.counitIso.app L).hom ≫ f := E.counitIso.hom.naturality f
  simp only [AddEquiv.trans_apply]
  rw [key, he' (E.inverse.map f), equivalenceHomAddEquiv_comp, homIsoAddEquiv_apply,
    homIsoAddEquiv_apply]
  simp only [Category.assoc, hcounit]

/-- The derived dual of a finite-length module over a regular local ring is the shifted Matlis
dual: `RHom_A(N, A) ≅ N'[-d]`, for `d` the normalizing shift of the regular module. -/
private theorem nonempty_dualOverRing_single_iso_matlisDual (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (d : ℤ)
    (hω : IsNormalizedDualizingComplex.{u, 0}
      (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))⟦d⟧))
    (E : ModuleCat.{u} A)
    (i : (ModuleCat.uliftFunctor.{0} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (N N' : ModuleCat.{u} A) (hN : IsFiniteLength A N)
    (hdual : Nonempty (N' ≅ ModuleCat.of A (N ⟶ E))) :
    Nonempty (dualOverRing A ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N')⟦-d⟧) := by
  let 𝓔 := derivedScalarEquivalence.{u, 0, u + 1} A
  let X := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N
  let θ : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ≅
      𝓔.functor.obj (StacksDraft.Perfect.unitObject.{u, 0} (R := A)) :=
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
        (LinearEquiv.toModuleIso
          { toFun := ULift.down, invFun := ULift.up, left_inv := fun _ => rfl,
            right_inv := fun _ => rfl, map_add' := fun _ _ => rfl,
            map_smul' := fun _ _ => rfl })).symm ≪≫
      (((uliftModuleEquivalence.{u, u, 0} A).functor.mapDerivedCategorySingleFunctor 0).app
        (ModuleCat.of (ULift.{0} A) (ULift.{0} A))).symm ≪≫
      𝓔.functor.mapIso
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} (ULift.{0} A)) 0).app
          (ModuleCat.of (ULift.{0} A) (ULift.{0} A)))
  obtain ⟨μ⟩ := nonempty_derivedHom_single_iso_matlisDual_shift.{u, 0} A
    (𝓔.functor.obj (StacksDraft.Perfect.unitObject.{u, 0} (R := A))) d
    ((isNormalizedDualizingComplex_congr
      ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) d).mapIso θ)).mp hω)
    E i hi N N' hN hdual
  exact ⟨((derivedHomULiftIso.{u, 0, u + 1} A).app
      (Opposite.op (𝓔.inverse.obj X), StacksDraft.Perfect.unitObject.{u, 0} (R := A))).symm ≪≫
    (derivedHomAdjunctionOverRing.{u, 0, u + 1} A).hom.mapIso
      ((𝓔.counitIso.app X).op.symm.prod
        (Iso.refl (𝓔.functor.obj (StacksDraft.Perfect.unitObject.{u, 0} (R := A))))) ≪≫ μ⟩

/-- **Stacks 0G02**, the duality at the point to which the source reduces its statement. Let `A`
be a regular local ring of dimension `d`, let `N` be an `A`-module of finite length and let `N'`
be a Matlis dual of `N` with respect to an injective hull `E` of the residue field. Then
`Hom_{D(A)}(N, K) ≃+ H⁰(K ⊗^L_A N'[-d])`, functorially in `K`. -/
@[stacks 0G02 "duality at the point"]
public theorem exists_addEquiv_hom_homology_derivedTensor_matlisDual
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (E : ModuleCat.{u} A)
    (i : (ModuleCat.uliftFunctor.{0} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (N N' : ModuleCat.{u} A) (hN : IsFiniteLength A N)
    (hdual : Nonempty (N' ≅ ModuleCat.of A (N ⟶ E))) :
    ∃ d : ℕ, ringKrullDim A = (d : ℕ∞) ∧
      ∃ e : ∀ L : DerivedCategory (ModuleCat.{u} A),
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
              ((derivedHomAdjunctionOverRing.{u, 0, u + 1} A).tensor.obj
                (L, ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N')⟦-(d : ℤ)⟧)))
            : Type u) ≃+
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N ⟶ L),
        ∀ (L L' : DerivedCategory (ModuleCat.{u} A)) (f : L ⟶ L')
          (a : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
            ((derivedHomAdjunctionOverRing.{u, 0, u + 1} A).tensor.obj
              (L, ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N')⟦-(d : ℤ)⟧))),
          e L' ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
              ((derivedHomAdjunctionOverRing.{u, 0, u + 1} A).tensor.map
                (f, 𝟙 (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N')⟦-(d : ℤ)⟧)))
              a) = e L a ≫ f := by
  obtain ⟨d, hdim, hω⟩ :=
    exists_ringKrullDim_eq_and_isNormalizedDualizingComplex_single_self_shift A
  have hfin : Module.Finite A N := by
    have : IsNoetherian A ↑N := (isFiniteLength_iff_isNoetherian_isArtinian.mp hN).1
    infer_instance
  obtain ⟨ψ⟩ := nonempty_dualOverRing_single_iso_matlisDual A (d : ℤ) hω E i hi N N' hN hdual
  exact ⟨d, hdim, exists_addEquiv_homology_derivedTensor_dual A _
    (StacksDraft.Perfect.isPerfect_single_of_finite_regularLocal.{u, 0} A N) _ ψ⟩

end Dualizing

end
