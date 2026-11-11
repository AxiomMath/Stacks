module

public import StacksFrontier.CategoryTheory.ExactCategory.ExtensionClosed
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreeExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorShortExactIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Picard
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyTrivialInvertible.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import Mathlib.Topology.LocallyConstant.Algebra
import StacksCore.Tactic.StacksAttribute

/-!
# Rank and determinant of finite locally free modules on a ringed space

Let `(X, O_X)` be a ringed space and `Vect(X)` the category of finite locally free
`O_X`-modules. This file formalizes [Stacks, Tag 0B37]:

* `Vect(X)`, with the short exact sequences of `O_X`-modules whose terms are finite locally free,
  is an exact category; its admissible epimorphisms are the surjections whose kernel is finite
  locally free and its admissible monomorphisms are the kernels of those;
* `Vect(X)` has a set of isomorphism classes, and `K₀(Vect(X))` is the abelian group on the
  classes `[E]` subject to `[E] = [E'] + [E'']` for every short exact sequence;
* when all stalks `O_{X,x}` are nonzero, the rank `x ↦ rank_{O_{X,x}} E_x` is a locally constant
  function, additive in short exact sequences, so it defines a homomorphism
  `K₀(Vect(X)) → Map_cont(X, ℤ)`; the loci `X_i` where the rank is `i` are open and closed and
  partition `X`, and `E` is finite locally free of rank `i` on `X_i`;
* the determinant `det(E)` is an invertible module which is finite locally free of rank `1` and
  which is `⋀ⁱ(E|_{X_i})` on `X_i`, and `[E] ↦ det(E)` defines a homomorphism
  `det : K₀(Vect(X)) → Pic(X)`.

## Main definitions

* `Stacks.SheafOfModules.Vect`: the finite locally free modules, as a property of objects.
* `Stacks.SheafOfModules.vectRank`: the rank of a finite locally free module.
* `Stacks.SheafOfModules.rankHom`: the rank homomorphism `K₀(Vect(X)) → Map_cont(X, ℤ)`.
* `Stacks.SheafOfModules.determinant`: the determinant `det(E)`.
* `Stacks.SheafOfModules.detHom`: the homomorphism `det : K₀(Vect(X)) → Pic(X)`.

## Main results

* `Stacks.SheafOfModules.rank_and_determinant_of_vect`: **Tag 0B37**, all the assertions above
  together.

## Implementation notes

*The determinant.* `det(E)` is the determinant of [Stacks, Tag 0FJN], the annihilator of the
degree-one part inside the exterior algebra, for the chosen package of algebras
`SheafOfModules.algebras`. The source defines it instead by glueing the `⋀ⁱ(E|_{X_i})` over the
open and closed pieces `X_i`; the identification of the two is part of the statement
(`Stacks.SheafOfModules.nonempty_determinant_over_rankStratum_iso`), so nothing is lost. The
annihilator needs no choice of decomposition, which is why `det(E)`, its invertibility and the
homomorphism `det` need no hypothesis on the stalks of `O_X`, whereas the decomposition by rank
does. Invertibility is proved by exhibiting `det(E)` as free of rank one near every point
(`Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_one_determinant`): over an open where `E` is
free of rank `r`, the inclusions `det(E) ⟵ det(E)_r ⟶ ⋀ʳ E` are bijective on stalks, and
`⋀ʳ` of a free module of rank `r` is free on the `r`-element subsets of the basis.

*The admissible epimorphisms.* On a ringed space whose stalks need not be local rings, the kernel
of a surjection between finite locally free modules need not be finite locally free: on a
one-point space with ring `R`, a surjection `R³ → R` whose kernel is a stably free but non-free
projective module is a surjection of `Vect(X)` which is not the second map of any conflation.
So the admissible epimorphisms are exactly the surjections whose kernel lies in `Vect(X)`, which
is what is stated (`Stacks.ExactCategory.admissibleEpi_conflation_iff`); every admissible
epimorphism is in particular a surjection.

*`K₀`.* The generators of `K₀(Vect(X))` are the objects of `Vect(X)` themselves rather than
their isomorphism classes, as in `CategoryTheory.GrothendieckGroup`, so the set-theoretic remark
of the source is not needed to form it; it is nevertheless proved
(`Stacks.SheafOfModules.essentiallySmall_vect`). Isomorphic objects have the same class, since
`0 → 0 → E → E' → 0` is short exact for an isomorphism `E ≅ E'`.

## References

* [Stacks Project, Tag 0B37](https://stacks.math.columbia.edu/tag/0B37)
* [Stacks Project, Tag 05SF](https://stacks.math.columbia.edu/tag/05SF)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Tag 0B38](https://stacks.math.columbia.edu/tag/0B38)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite CategoryTheory.Sheaf
open Stacks.ExactCategory

universe v u₁ u

namespace Stacks.SheafOfModules

section Site

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A sheaf of modules which is free of rank `r` on the members of a covering is finite locally
free of rank `r`.** -/
theorem isFiniteLocallyFreeOfRank_of_coversTop {ι : Type u₁} {V : ι → C} (hV : J.CoversTop V)
    (M : _root_.SheafOfModules.{u} R) (r : ℕ)
    (e : ∀ k, ∃ I : Type u, Nonempty (I ≃ Fin r) ∧
      Nonempty (_root_.SheafOfModules.free (R := R.over (V k)) I ≅ M.over (V k))) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, v, u₁} M r := by
  choose I hI σ using e
  let q : _root_.SheafOfModules.LocalGeneratorsData.{u₁} M :=
    { I := ι, X := V, coversTop := hV
      generators := fun k =>
        { I := I k
          s := (M.over (V k)).freeHomEquiv (σ k).some.hom
          epi := by simp only [Equiv.symm_apply_apply]; exact IsIso.epi_of_iso _ } }
  have hπ : ∀ k, (q.generators k).π = (σ k).some.hom := fun k => Equiv.symm_apply_apply _ _
  refine ⟨q, ⟨fun k => ?_⟩, fun k => hI k⟩
  rw [hπ k]
  infer_instance

omit [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The free sheaf of modules on the empty type is a zero object. -/
theorem isZero_free_pempty [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    IsZero (_root_.SheafOfModules.free.{u} (R := R) PEmpty) :=
  (IsZero.iff_id_eq_zero _).mpr
    ((_root_.SheafOfModules.free (R := R) PEmpty).freeHomEquiv.injective
      (funext fun a => a.elim))

end Site

section RingedSpace

variable {X : TopCat.{u}} (Osharp : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- **`Vect(X)`**: the finite locally free sheaves of modules on the ringed space `(X, O_X)`, as
a property of objects of the category of `O_X`-modules. -/
abbrev Vect : ObjectProperty
    (_root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology X) Osharp)) :=
  fun E => AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E

instance : (Vect Osharp).IsClosedUnderIsomorphisms where
  of_iso e h := by
    have := h
    exact Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso e

instance : (Vect Osharp).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := by
    have := h₁
    have := h₃
    exact isFiniteLocallyFree_of_shortExact _ hS

instance : (Vect Osharp).ContainsZero where
  exists_zero := by
    let R := toRingCat (Opens.grothendieckTopology X) Osharp
    have hZ : IsZero (_root_.SheafOfModules.free (R := R) PEmpty) := isZero_free_pempty
    refine ⟨_, hZ, AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_coversTop
      (V := fun _ : PUnit.{u + 1} => (⊤ : Opens X))
      ((Opens.coversTop_iff X _).mpr (iSup_const)) _ fun _ =>
        ⟨PEmpty, inferInstance, ⟨IsZero.iso isZero_free_pempty
          ((_root_.SheafOfModules.overFunctor R ⊤).map_isZero hZ)⟩⟩⟩

/-- **`Vect(X)` has a set of isomorphism classes of objects.** A finite locally free module is
of finite type, and the modules of finite type on a ringed space are essentially small. -/
theorem essentiallySmall_vect : ObjectProperty.EssentiallySmall.{u} (Vect Osharp) :=
  (essentiallySmall_isFiniteType
    ({ carrier := X, presheaf := Osharp.obj, IsSheaf := Osharp.property } :
      AlgebraicGeometry.RingedSpace.{u})).of_le fun M hM => by
    exact @Stacks.FiniteLocallyFree.isFiniteType _ _ _ _ _ _ M hM

variable {Osharp}

/-! ### Ranks -/

/-- **The rank of a finite locally free module** on a ringed space whose stalks are nonzero, as
a locally constant `ℕ`-valued function. -/
noncomputable def vectRank (hO : LocallyFreeRank.StalksNontrivial X Osharp)
    (E : (Vect Osharp).FullSubcategory) : LocallyConstant X ℕ :=
  @finiteLocallyFreeRank X Osharp E.obj hO E.property

/-- The stalk of a sheaf of modules at a point of an open over which it is free on `I` is free on
`Fin (Nat.card I)`. -/
theorem nonempty_stalk_linearEquiv_of_iso
    (E : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology X) Osharp))
    {V : Opens X} (I : Type u) [Finite I] (e : _root_.SheafOfModules.free.{u} I ≅ E.over V)
    (y : X) (hy : y ∈ V) :
    Nonempty (↑(TopCat.Presheaf.stalk E.val.presheaf y)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj y)]
      (Fin (Nat.card I) →₀ ↑(TopCat.Presheaf.stalk Osharp.obj y))) :=
  TopWedge.nonempty_stalkLinearEquiv_finsupp_of_trivialization E (trivializationOfIso E I e)
    ‹_› y hy

/-- The stalk of a finite locally free module at a point is free of rank the rank there. -/
theorem nonempty_stalk_linearEquiv_vectRank (hO : LocallyFreeRank.StalksNontrivial X Osharp)
    (E : (Vect Osharp).FullSubcategory) (x : X) :
    Nonempty (↑(TopCat.Presheaf.stalk E.obj.val.presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      (Fin (vectRank hO E x) →₀ ↑(TopCat.Presheaf.stalk Osharp.obj x))) := by
  have := E.property
  obtain ⟨W, hxW, I, hI, ⟨e⟩⟩ := exists_free_iso_over E.obj x
  have hr : vectRank hO E x = Nat.card I :=
    @finiteLocallyFreeRank_eq_card_of_iso X Osharp E.obj hO E.property W I e x hxW
  rw [hr]
  exact nonempty_stalk_linearEquiv_of_iso E.obj I e x hxW

/-- **The rank of a finite locally free module at `x` is the rank of its stalk** over
`O_{X,x}`. -/
theorem finrank_stalk_eq_vectRank (hO : LocallyFreeRank.StalksNontrivial X Osharp)
    (E : (Vect Osharp).FullSubcategory) (x : X) :
    Module.finrank ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E.obj.val.presheaf x) = vectRank hO E x := by
  obtain ⟨ℓ⟩ := nonempty_stalk_linearEquiv_vectRank hO E x
  have := hO x
  rw [ℓ.finrank_eq, Module.finrank_finsupp_self, Fintype.card_fin]

/-- **The rank is additive in short exact sequences of finite locally free modules.** -/
theorem vectRank_X₂ (hO : LocallyFreeRank.StalksNontrivial X Osharp)
    (S : ShortComplex (_root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology X) Osharp)))
    (hS : S.ShortExact) (h₁ : Vect Osharp S.X₁) (h₂ : Vect Osharp S.X₂) (h₃ : Vect Osharp S.X₃) :
    vectRank hO (mkObj S.X₂ h₂) = vectRank hO (mkObj S.X₁ h₁) + vectRank hO (mkObj S.X₃ h₃) := by
  ext x
  exact @finiteLocallyFreeRank_X₂_of_shortExact X Osharp hO S hS h₁ h₂ h₃ x

/-- **The rank homomorphism** `K₀(Vect(X)) → Map_cont(X, ℤ)`, `[E] ↦ rank_E`. -/
noncomputable def rankHom (hO : LocallyFreeRank.StalksNontrivial X Osharp) :
    KZero (Vect Osharp) →+ C(X, ℤ) :=
  KZero.lift (fun E => ((vectRank hO E).map (Nat.cast : ℕ → ℤ)).toContinuousMap)
    fun S hS h₁ h₂ h₃ => by
      ext x
      change ((vectRank hO (mkObj S.X₂ h₂) x : ℕ) : ℤ) =
        ((vectRank hO (mkObj S.X₁ h₁) x : ℕ) : ℤ) + ((vectRank hO (mkObj S.X₃ h₃) x : ℕ) : ℤ)
      rw [vectRank_X₂ hO S hS h₁ h₂ h₃, LocallyConstant.add_apply, Nat.cast_add]

/-- The rank homomorphism sends the class of a finite locally free module to its rank. -/
theorem rankHom_of (hO : LocallyFreeRank.StalksNontrivial X Osharp)
    (E : (Vect Osharp).FullSubcategory) (x : X) :
    rankHom hO (KZero.of E) x = (vectRank hO E x : ℤ) := by
  rw [rankHom, KZero.lift_of]
  rfl

/-! ### Determinants -/

/-- **The determinant `det(E)`** of a sheaf of modules: the annihilator of the degree-one part
inside its exterior algebra ([Stacks, Tag 0FJN]), for the chosen package of algebras. -/
noncomputable abbrev determinant
    (E : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology X) Osharp)) :
    _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology X) Osharp) :=
  (_root_.SheafOfModules.algebras (Opens.grothendieckTopology X) E).determinant

/-- A morphism of sheaves of modules on a ringed space which is bijective on the stalks at all
points of an open is an isomorphism after restriction to that open. -/
theorem isIso_over_of_bijective_stalkMapL
    {M N : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology X) Osharp)}
    (φ : M ⟶ N) (W : Opens X)
    (h : ∀ x ∈ W, Function.Bijective (PresheafOfModules.stalkMapL x φ.val)) :
    IsIso (φ.over W) := by
  let R := toRingCat (Opens.grothendieckTopology X) Osharp
  have key : ∀ U : (Over W)ᵒᵖ, IsIso
      (((PresheafOfModules.toPresheaf (R.over W).obj).map
        ((_root_.SheafOfModules.forget (R.over W)).map (φ.over W))).app U) := fun U =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective
        ((_root_.SheafOfModules.toSheaf R).map φ) U.unop.left
        fun x hxU => h x (leOfHom U.unop.hom hxU))
  have h1 : IsIso ((PresheafOfModules.toPresheaf (R.over W).obj).map
      ((_root_.SheafOfModules.forget (R.over W)).map (φ.over W))) :=
    NatIso.isIso_of_isIso_app _
  have h2 : IsIso ((_root_.SheafOfModules.forget (R.over W)).map (φ.over W)) :=
    isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf (R.over W).obj)
  exact isIso_of_reflects_iso _ (_root_.SheafOfModules.forget (R.over W))

/-- **Over an open on which every stalk of `E` is free of rank `r`, the determinant is the
`r`-th exterior power**: the inclusions `det(E) ⟵ det(E)_r ⟶ ⋀ʳ E` of the degree-`r` summand
are isomorphisms there, being bijective on stalks. -/
noncomputable def determinantOverIso
    (E : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology X) Osharp))
    {V : Opens X} (r : ℕ)
    (hV : ∀ y ∈ V, Nonempty (↑(TopCat.Presheaf.stalk E.val.presheaf y)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj y)]
      (Fin r →₀ ↑(TopCat.Presheaf.stalk Osharp.obj y)))) :
    (determinant E).over V ≅
      ((_root_.SheafOfModules.algebras (Opens.grothendieckTopology X) E).exteriorPower r).over V :=
  let A := _root_.SheafOfModules.algebras (Opens.grothendieckTopology X) E
  have : IsIso ((A.determinantSummand r).over V) :=
    isIso_over_of_bijective_stalkMapL _ V fun x hx =>
      TopWedge.bijective_stalkMapL_determinantSummand A x r (Module.Basis.ofRepr (hV x hx).some)
  have : IsIso ((A.exteriorAnnihilator r).ι.over V) :=
    isIso_over_of_bijective_stalkMapL _ V fun x hx =>
      TopWedge.bijective_stalkMapL_exteriorAnnihilator_ι A r x hx
        (TopWedge.subsingleton_exteriorPower_stalk_of_free hV)
  (asIso ((A.determinantSummand r).over V)).symm ≪≫ asIso ((A.exteriorAnnihilator r).ι.over V)

/-- **The determinant of a finite locally free module is finite locally free of rank one.** -/
theorem isFiniteLocallyFreeOfRank_one_determinant
    (E : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology X) Osharp))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (determinant E) 1 := by
  classical
  choose W hxW I hI e using exists_free_iso_over E
  refine isFiniteLocallyFreeOfRank_of_coversTop ((Opens.coversTop_iff X W).mpr
    (eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hxW x⟩)) (determinant E) 1 fun x => ?_
  let : LinearOrder (I x) := IsWellOrder.linearOrder WellOrderingRel
  have hV := fun y hy => nonempty_stalk_linearEquiv_of_iso E (I x) (e x).some y hy
  refine ⟨Set.powersetCard (I x) (Nat.card (I x)), ⟨Finite.equivFinOfCardEq ?_⟩,
    ⟨(exteriorPowerOverFreeIsoOfIsoFree
      (_root_.SheafOfModules.algebras (Opens.grothendieckTopology X) E) (W x)
      (Nat.card (I x)) (I x) (e x).some.symm).symm ≪≫ (determinantOverIso E _ hV).symm⟩⟩
  rw [Set.powersetCard.card, Nat.choose_self]

/-- The sheaf-of-rings condition on `O_X`, in the spelling of the Picard group. -/
theorem isSheaf_structureRingPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj) :=
  (toRingCat (Opens.grothendieckTopology X) Osharp).property

/-- **The determinant of a finite locally free module is invertible.** -/
theorem isInvertible_determinant
    (E : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology X) Osharp))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    IsInvertible Osharp.obj isSheaf_structureRingPresheaf (determinant E) := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf Osharp.obj
        isSheaf_structureRingPresheaf) (determinant E) 1 :=
    isFiniteLocallyFreeOfRank_one_determinant E
  exact isInvertible_of_isFiniteLocallyFreeOfRank_one Osharp.obj _ (determinant E)

/-- **The determinant is `⋀ⁱ(E|_{X_i})` on the rank locus `X_i`.** -/
theorem nonempty_determinant_over_rankStratum_iso
    (hO : LocallyFreeRank.StalksNontrivial X Osharp) (E : (Vect Osharp).FullSubcategory)
    (i : ℕ) :
    Nonempty ((determinant E.obj).over (@rankStratum X Osharp E.obj hO E.property i) ≅
      (_root_.SheafOfModules.algebras
        (Osharp := Osharp.over (@rankStratum X Osharp E.obj hO E.property i))
        ((Opens.grothendieckTopology X).over (@rankStratum X Osharp E.obj hO E.property i))
        (show _root_.SheafOfModules.{u} (toRingCat
          ((Opens.grothendieckTopology X).over (@rankStratum X Osharp E.obj hO E.property i))
          (Osharp.over (@rankStratum X Osharp E.obj hO E.property i))) from
          E.obj.over (@rankStratum X Osharp E.obj hO E.property i))).exteriorPower i) := by
  set U := @rankStratum X Osharp E.obj hO E.property i
  have hV : ∀ y ∈ U, Nonempty (↑(TopCat.Presheaf.stalk E.obj.val.presheaf y)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj y)]
      (Fin i →₀ ↑(TopCat.Presheaf.stalk Osharp.obj y))) := fun y hy => by
    have hy' : vectRank hO E y = i := hy
    rw [← hy']
    exact nonempty_stalk_linearEquiv_vectRank hO E y
  let A := _root_.SheafOfModules.algebras (Opens.grothendieckTopology X) E.obj
  let B := _root_.SheafOfModules.algebras (Osharp := Osharp.over U)
    ((Opens.grothendieckTopology X).over U)
    (show _root_.SheafOfModules.{u} (toRingCat ((Opens.grothendieckTopology X).over U)
      (Osharp.over U)) from E.obj.over U)
  exact ⟨determinantOverIso E.obj i hV ≪≫ exteriorPowerOverIso E.obj U i A.exterior
    A.exteriorGenerator A.exterior_isExteriorAlgebra B.exterior B.exteriorGenerator
    B.exterior_isExteriorAlgebra⟩

/-- **The determinant homomorphism** `det : K₀(Vect(X)) → Pic(X)`, `[E] ↦ det(E)`. It is
additive by the canonical isomorphism `det(E') ⊗ det(E'') ≅ det(E)` of [Stacks, Tag 0B38]. -/
noncomputable def detHom :
    KZero (Vect Osharp) →+ Picard.PicardGroup Osharp.obj isSheaf_structureRingPresheaf :=
  KZero.lift (fun E => haveI := E.property
      Picard.classOf Osharp.obj isSheaf_structureRingPresheaf (determinant E.obj)
        (isInvertible_determinant E.obj))
    fun S hS h₁ h₂ h₃ => by
      have := h₁
      have := h₂
      have := h₃
      have := hS.mono_f
      have := hS.epi_g
      let φ := TopWedge.determinantTensorDeterminantIsoOfFiniteLocallyFree
        (_root_.SheafOfModules.algebras (Opens.grothendieckTopology X) S.X₁)
        (_root_.SheafOfModules.algebras (Opens.grothendieckTopology X) S.X₂)
        (_root_.SheafOfModules.algebras (Opens.grothendieckTopology X) S.X₃) S.f S.g S.zero
        hS.exact
      have := isInvertible_determinant S.X₂
      have hT := isInvertible_of_iso Osharp.obj isSheaf_structureRingPresheaf φ.symm
      dsimp only
      rw [Picard.classOf_tensor Osharp.obj isSheaf_structureRingPresheaf _ _
        (isInvertible_determinant S.X₁) (isInvertible_determinant S.X₃) hT]
      exact (Picard.classOf_eq_classOf_iff _ _ _ _ _ _).mpr ⟨φ.symm⟩

/-- The determinant homomorphism sends the class of a finite locally free module to the class of
its determinant. -/
theorem detHom_of (E : (Vect Osharp).FullSubcategory) :
    detHom (KZero.of E) = haveI := E.property
      Picard.classOf Osharp.obj isSheaf_structureRingPresheaf (determinant E.obj)
        (isInvertible_determinant E.obj) := by
  rw [detHom, KZero.lift_of]

/-- **Stacks Project, Tag 0B37: rank and determinant of finite locally free modules.** Let
`(X, O_X)` be a ringed space and `Vect(X)` the category of finite locally free `O_X`-modules.

1. `Vect(X)`, with the short exact sequences of `O_X`-modules all of whose terms are finite
   locally free, is an exact category ([Stacks, Tag 05SF]). Its admissible epimorphisms are the
   surjections whose kernel is finite locally free (in particular surjections), and its admissible
   monomorphisms are the kernels of those.
2. `Vect(X)` has a set of isomorphism classes of objects, and `K₀(Vect(X))` is generated by the
   classes `[E]` subject to `[E] = [E'] + [E'']` for every short exact sequence
   `0 → E' → E → E'' → 0` of finite locally free modules.
3. If all stalks `O_{X,x}` are nonzero rings, the rank `rank_E(x) = rank_{O_{X,x}} E_x` is a
   locally constant function, additive in short exact sequences, so that `[E] ↦ rank_E` is a
   homomorphism `K₀(Vect(X)) → Map_cont(X, ℤ)`. The loci `X_i` where the rank is `i` are open and
   closed, pairwise disjoint and cover `X`, `E` is finite locally free of rank `i` on `X_i`, and
   `det(E)` is `⋀ⁱ(E|_{X_i})` on `X_i`.
4. The determinant `det(E)` is an invertible module, finite locally free of rank `1`, and
   `[E] ↦ det(E)` is a homomorphism `det : K₀(Vect(X)) → Pic(X)`.

`det(E)` is the determinant of [Stacks, Tag 0FJN] and the additivity of `det` is the isomorphism
`det(E') ⊗ det(E'') ≅ det(E)` of [Stacks, Tag 0B38]. -/
@[stacks 0B37 "Vect(X) is an exact category with the conflations, admissible epimorphisms and \
admissible monomorphisms stated; it has a set of isomorphism classes and K_0(Vect(X)) is given by \
the stated generators and relations; the rank is the stalk rank, locally constant, additive and \
defines K_0(Vect(X)) → Map_cont(X, Z); the clopen decomposition X = X_0 ⊔ X_1 ⊔ … with E of rank \
i on X_i and det(E) = ⋀^i(E|_{X_i}) there; det(E) is invertible and locally free of rank 1 and \
defines det : K_0(Vect(X)) → Pic(X). The admissible epimorphisms are the surjections whose kernel \
is finite locally free, which on a ringed space is not every surjection of Vect(X)"]
theorem rank_and_determinant_of_vect :
    IsExactStructure (conflation (Vect Osharp)) ∧
    (∀ {E F : (Vect Osharp).FullSubcategory} (p : E ⟶ F),
      AdmissibleEpi (conflation (Vect Osharp)) p ↔ Epi p.hom ∧ Vect Osharp (kernel p.hom)) ∧
    (∀ {E F : (Vect Osharp).FullSubcategory} (i : E ⟶ F),
      AdmissibleMono (conflation (Vect Osharp)) i ↔
        ∃ (G : (Vect Osharp).FullSubcategory) (p : F ⟶ G) (w : i.hom ≫ p.hom = 0),
          (Epi p.hom ∧ Vect Osharp (kernel p.hom)) ∧
            Nonempty (IsLimit (KernelFork.ofι i.hom w))) ∧
    ObjectProperty.EssentiallySmall.{u} (Vect Osharp) ∧
    (∀ (S : ShortComplex
        (_root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology X) Osharp)))
        (_ : S.ShortExact) (h₁ : Vect Osharp S.X₁) (h₂ : Vect Osharp S.X₂)
        (h₃ : Vect Osharp S.X₃),
      KZero.of (mkObj S.X₂ h₂) = KZero.of (mkObj S.X₁ h₁) + KZero.of (mkObj S.X₃ h₃)) ∧
    (∀ hO : LocallyFreeRank.StalksNontrivial X Osharp,
      (∀ (E : (Vect Osharp).FullSubcategory) (x : X),
        Module.finrank ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk E.obj.val.presheaf x) = vectRank hO E x) ∧
      (∀ (S : ShortComplex
          (_root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology X) Osharp)))
          (_ : S.ShortExact) (h₁ : Vect Osharp S.X₁) (h₂ : Vect Osharp S.X₂)
          (h₃ : Vect Osharp S.X₃),
        vectRank hO (mkObj S.X₂ h₂) = vectRank hO (mkObj S.X₁ h₁) + vectRank hO (mkObj S.X₃ h₃)) ∧
      (∀ (E : (Vect Osharp).FullSubcategory) (x : X),
        rankHom hO (KZero.of E) x = (vectRank hO E x : ℤ)) ∧
      ∀ E : (Vect Osharp).FullSubcategory,
        IsLocallyConstant (⇑(vectRank hO E)) ∧
        (∀ i : ℕ, IsClopen (@rankStratum X Osharp E.obj hO E.property i : Set X)) ∧
        Pairwise (Function.onFun Disjoint
          fun i : ℕ => (@rankStratum X Osharp E.obj hO E.property i : Set X)) ∧
        (⨆ i : ℕ, @rankStratum X Osharp E.obj hO E.property i) = ⊤ ∧
        (∀ (i : ℕ) (x : X), x ∈ @rankStratum X Osharp E.obj hO E.property i →
          ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ @rankStratum X Osharp E.obj hO E.property i)
            (I : Type u), Nonempty (I ≃ Fin i) ∧
              Nonempty (_root_.SheafOfModules.free.{u} I ≅ E.obj.over V)) ∧
        ∀ i : ℕ, Nonempty ((determinant E.obj).over (@rankStratum X Osharp E.obj hO E.property i) ≅
          (_root_.SheafOfModules.algebras
            (Osharp := Osharp.over (@rankStratum X Osharp E.obj hO E.property i))
            ((Opens.grothendieckTopology X).over (@rankStratum X Osharp E.obj hO E.property i))
            (show _root_.SheafOfModules.{u} (toRingCat
              ((Opens.grothendieckTopology X).over (@rankStratum X Osharp E.obj hO E.property i))
              (Osharp.over (@rankStratum X Osharp E.obj hO E.property i))) from
              E.obj.over (@rankStratum X Osharp E.obj hO E.property i))).exteriorPower i)) ∧
    (∀ E : (Vect Osharp).FullSubcategory,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          (determinant E.obj) 1 ∧
        haveI := E.property
        IsInvertible Osharp.obj isSheaf_structureRingPresheaf (determinant E.obj)) ∧
    ∀ E : (Vect Osharp).FullSubcategory,
      detHom (KZero.of E) = haveI := E.property
        Picard.classOf Osharp.obj isSheaf_structureRingPresheaf (determinant E.obj)
          (isInvertible_determinant E.obj) :=
  ⟨isExactStructure_conflation, admissibleEpi_conflation_iff, admissibleMono_conflation_iff,
    essentiallySmall_vect Osharp, fun _ hS h₁ h₂ h₃ => KZero.of_shortExact hS h₁ h₂ h₃,
    fun hO => ⟨finrank_stalk_eq_vectRank hO, vectRank_X₂ hO, rankHom_of hO, fun E =>
      let h := @rankDecomposition X Osharp E.obj hO E.property
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2,
        nonempty_determinant_over_rankStratum_iso hO E⟩⟩,
    fun E => haveI := E.property
      ⟨isFiniteLocallyFreeOfRank_one_determinant E.obj, isInvertible_determinant E.obj⟩,
    detHom_of⟩

end RingedSpace

end Stacks.SheafOfModules

end
