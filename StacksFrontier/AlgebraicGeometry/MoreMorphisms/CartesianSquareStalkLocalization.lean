module

public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.SheafifyStalk.StalkMap
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentExactSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceDifferentials

/-!
# Local rings in a cartesian square of schemes

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a *cartesian* square of schemes and let `x'` be a point of `X'`.  Then the local ring of `X'`
at `x'` is a localization of `𝒪_{X,g'(x')} ⊗_{𝒪_{Y,y}} 𝒪_{Y',f'(x')}`, where `y` is the common
image of `x'` in `Y`.

`AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization` is this statement for the
*canonical* fibre product `pullback f g`; the content here is the transport of it along the
isomorphism `X' ≅ pullback f g` that cartesianness provides, so that it becomes available for an
arbitrary cartesian square — which is the shape a base-change statement about a square of schemes
is given in.

A consumer of that statement — flat base change for the naive cotangent complex, Stacks 0FJZ —
does not meet those three local rings in the spelling `𝒪_{X,g'(x')}`, `𝒪_{Y',f'(x')}`,
`𝒪_{Y,y}`: the complexes it compares are built from the three sheaves of commutative rings
`(g')^{-1}f^{-1}𝒪_Y ⟶ (g')^{-1}𝒪_X ⟶ 𝒪_{X'}` and `(f')^{-1}𝒪_{Y'}` on the single space `X'`,
so what it has at `x'` are the *stalks of those inverse images*.  The second half of this file
identifies each of them with the local ring above and restates the localization statement in
that spelling.

## Main results

* `AlgebraicGeometry.BaseChangeStalk.stalk_isLocalization_of_isPullback`: for a cartesian square
  the tensor product of the local rings of `X` and `Y'` over the local ring of `Y` maps to the
  local ring of `X'`, restricting on the two factors to the two stalk maps, and exhibits the local
  ring of `X'` as a localization of itself.
* `AlgebraicGeometry.BaseChangeStalk.isLocalization_of_comp_ringEquiv`: a localization stays one
  after composing its structure map with a ring isomorphism of the target.
* `AlgebraicGeometry.BaseChangeStalk.stalkInverseImageBaseRingIso`,
  `AlgebraicGeometry.BaseChangeStalk.stalkInverseImageMiddleRingIso` and
  `AlgebraicGeometry.BaseChangeStalk.stalkInverseImageSheafIso`: the stalks at `x'` of
  `(g')^{-1}f^{-1}𝒪_Y`, of `(g')^{-1}𝒪_X` and of `(f')^{-1}𝒪_{Y'}` are `𝒪_{Y,(g' ≫ f)(x')}`,
  `𝒪_{X,g'(x')}` and `𝒪_{Y',f'(x')}`.
* `AlgebraicGeometry.BaseChangeStalk.stalk_ringedSpaceStructureMap`: those identifications carry
  the stalk of the structure map `h^{-1}𝒪_S ⟶ 𝒪_T` of a morphism of schemes to its stalk map.
* `AlgebraicGeometry.BaseChangeStalk.stalkSheafPullbackIso_naturality` and
  `AlgebraicGeometry.BaseChangeStalk.stalkSheafPullbackIso_hom_naturality`: the stalk of the
  sheaf inverse image is natural in the sheaf.
* `AlgebraicGeometry.BaseChangeStalk.stalkInverseImageBaseRingIso_hom_comp_stalkMap`: hence the
  identifications also carry the stalk of the first map `(g')^{-1}f^{-1}𝒪_Y ⟶ (g')^{-1}𝒪_X` of
  the tower to the stalk map of `f`.
* `AlgebraicGeometry.BaseChangeStalk.stalk_isLocalization_of_isPullback_inverseImage` and
  `AlgebraicGeometry.BaseChangeStalk.stalk_isLocalization_of_isPullback_inverseImage_comm`: the
  localization statement in that spelling, in the two orders of the tensor factors.  Three of its
  four structure maps are the stalks of the sheaf-level maps of the two towers; only
  `𝒪_{Y,y} ⟶ (f')^{-1}𝒪_{Y'}` is a transported stalk map.
* `AlgebraicGeometry.BaseChangeStalk.tensorRingEquivOfRingEquiv` and
  `AlgebraicGeometry.BaseChangeStalk.exists_isLocalization_of_source_ringEquiv`: the algebraic
  transport the restatement runs on — a tensor product follows ring isomorphisms of its base and
  of its two factors, and a localization follows a ring isomorphism of the ring it localizes.

## Implementation notes

The isomorphism `X' ≅ pullback f g` is obtained from `CategoryTheory.IsPullback.isoPullback` and
then substituted into the goal, so that `g'` and `f'` are literally the composites of that
isomorphism with the two projections.  Every stalk appearing in the statement is then the stalk
appearing in `pullback_stalk_isLocalization` at the transported point, with no `eqToHom` left to
carry: the only comparison is the one between the local rings of `X'` and of `pullback f g`, which
is the stalk of an isomorphism of schemes and hence an isomorphism of rings.

The localization is transported along that isomorphism with
`IsLocalization.isLocalization_of_algEquiv`; the algebra equivalence is the ring isomorphism of
stalks, which commutes with the structure maps out of the tensor product by the very definition of
the algebra structure on the local ring of `X'`.

The three stalk identifications are instances of
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso`, which says that the stalk of
`h^{-1}𝒪_S` at a point is the stalk of `𝒪_S` at its image.  Two of them are that statement
verbatim; the one for `(g')^{-1}f^{-1}𝒪_Y` is a *double* inverse image and is therefore the
composite of `Stacks.SheafifyStalk.stalkInverseImageIso` at the sheaf `f^{-1}𝒪_Y` with
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso` for `f` at the intermediate point.
No `eqToHom` arises: `(g' ≫ f).base x'` and `f.base (g'.base x')` are the same term.

Three of the four structure maps of the restated statement are left in the sheaf-level form the
consumer's towers are built from, rather than transported: `(g')^{-1}f^{-1}𝒪_Y ⟶ (g')^{-1}𝒪_X`
is the stalk of `Stacks.SheafOfModules.inverseImageFirstRingMap`, and the two maps into
`𝒪_{X',x'}` are the stalks of `Stacks.SheafOfModules.ringedSpaceStructureMap`.
`stalk_ringedSpaceStructureMap` and `stalkInverseImageBaseRingIso_hom_comp_stalkMap` are what let
those be read as the stalk maps the library statement is about; the first is
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_hom_comp_stalkMap` together with the
fact that `Stacks.SheafOfModules.ringedSpaceStructureMap` and
`AlgebraicGeometry.inverseImageStructureMap` are the same morphism, and the second needs
naturality of the comparison in the sheaf, which is proved here.

The fourth map, `(g')^{-1}f^{-1}𝒪_Y ⟶ (f')^{-1}𝒪_{Y'}`, is a transported stalk map of `g` and
not the stalk of any sheaf morphism.  It cannot be otherwise: the comparison of sheaves of rings
that `Stacks.NaiveCotangentFlatBaseChange.exists_baseRingComparison` produces for a commutative
square is not determined by the square, and nothing here chooses one for a cartesian square.

Changing the base ring of a tensor product is not something Mathlib transports:
`Algebra.TensorProduct.congr` keeps the base fixed, and
`Algebra.TensorProduct.equivOfCompatibleSMul` compares two base rings that already act on the
same two factors.  So `tensorRingEquivOfRingEquiv` is
built here from `Algebra.TensorProduct.lift` in both directions, over the algebra structure that
a ring isomorphism of the base induces on the target tensor product, and the two composites are
checked on pure tensors.  The source of a localization is then moved along the resulting
isomorphism with `IsLocalization.of_ringEquiv_left`, the submonoid being the preimage of the
given one.

Both orders of the two tensor factors are stated.  The ring-level flat base change that consumes
this — `NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_of_flat_base` — takes its localized
ring to be a localization of `B ⊗_R A` with `B` the flat factor, so it needs the `_comm` form;
the other matches the shape of `stalk_isLocalization_of_isPullback` above.  The two differ by
`Algebra.TensorProduct.comm`.

## References

* [Stacks Project, Tag 01JR](https://stacks.math.columbia.edu/tag/01JR), fibre products of
  schemes.
* [Stacks Project, Tag 0FJZ](https://stacks.math.columbia.edu/tag/0FJZ), flat base change for the
  naive cotangent complex, which consumes this statement at every point of `X'`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry
open Stacks.SheafOfModules (ringedSpaceStructureMap inverseImageBaseRing inverseImageMiddleRing
  inverseImageFirstRingMap)
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf)

universe v w u

namespace AlgebraicGeometry.BaseChangeStalk

/-- **Transport of a localization along an isomorphism of the target.**  If `S` is a localization
of `T` at `M` for the algebra structure given by a ring map `φ : T → S`, and `ρ : S ≃+* S'` is a
ring isomorphism, then `S'` is a localization of `T` at `M` for the algebra structure given by
`ρ ∘ φ`.

Stated over bare commutative rings so that it can be applied to a ring map whose source is a
tensor product: the instance arguments are then fixed by the explicit types rather than guessed
while unifying, which is what instance search cannot do for the two spellings of the semiring
structure of a tensor product. -/
theorem isLocalization_of_comp_ringEquiv {T S S' : Type*} [CommRing T] [CommRing S] [CommRing S']
    (φ : T →+* S) (ρ : S ≃+* S') (M : Submonoid T)
    (hM : letI := φ.toAlgebra; IsLocalization M S) :
    letI := (((ρ : S →+* S')).comp φ).toAlgebra; IsLocalization M S' := by
  let _ := φ.toAlgebra
  let _ := ((ρ : S →+* S').comp φ).toAlgebra
  have := hM
  exact IsLocalization.isLocalization_of_algEquiv M (AlgEquiv.ofRingEquiv (f := ρ) fun _ => rfl)

/-- **The local ring at a point of a cartesian square is a localization of the tensor product of
the local rings of the other three corners.**  For a cartesian square `g' ≫ f = f' ≫ g` of
schemes and a point `x'` of `X'`, there is a ring map
`𝒪_{X,g'(x')} ⊗_{𝒪_{Y,y}} 𝒪_{Y',f'(x')} ⟶ 𝒪_{X',x'}` restricting on the two factors to the
stalk maps of `g'` and of `f'`, and it exhibits `𝒪_{X',x'}` as a localization of its source.

This is `AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization` transported along the
isomorphism `X' ≅ pullback f g` supplied by cartesianness. -/
theorem stalk_isLocalization_of_isPullback {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : IsPullback g' f' f g) (x' : X'.carrier) :
    let h : (g' ≫ f).base x' = (f' ≫ g).base x' :=
      congrArg (fun k : X' ⟶ Y => k.base x') hsq.w
    let R := Y.presheaf.stalk ((g' ≫ f).base x')
    let A := X.presheaf.stalk (g'.base x')
    let B := Y'.presheaf.stalk (f'.base x')
    let C := X'.presheaf.stalk x'
    letI : Algebra R A := (f.stalkMap (g'.base x')).hom.toAlgebra
    letI : Algebra R B :=
      ((eqToHom (congrArg Y.presheaf.stalk h)) ≫ g.stalkMap (f'.base x')).hom.toAlgebra
    ∃ φ : TensorProduct R A B →+* C,
      φ.comp Algebra.TensorProduct.includeLeftRingHom = (g'.stalkMap x').hom ∧
      φ.comp Algebra.TensorProduct.includeRight.toRingHom = (f'.stalkMap x').hom ∧
      letI : Algebra (TensorProduct R A B) C := φ.toAlgebra
      ∃ M : Submonoid (TensorProduct R A B), IsLocalization M C := by
  obtain ⟨e, he₁, he₂⟩ : ∃ e : X' ≅ pullback f g,
      e.hom ≫ pullback.fst f g = g' ∧ e.hom ≫ pullback.snd f g = f' :=
    ⟨hsq.isoPullback, hsq.isoPullback_hom_fst, hsq.isoPullback_hom_snd⟩
  subst he₁
  subst he₂
  intro hpt R A B C
  let _ : Algebra R A :=
    (f.stalkMap ((e.hom ≫ pullback.fst f g).base x')).hom.toAlgebra
  let _ : Algebra R B :=
    ((eqToHom (congrArg Y.presheaf.stalk hpt)) ≫
      g.stalkMap ((e.hom ≫ pullback.snd f g).base x')).hom.toAlgebra
  obtain ⟨φ₀, hL, hR, M, hM⟩ := pullback_stalk_isLocalization f g (e.hom.base x')
  dsimp only at hL hR
  have key : ∀ {Z : Scheme.{u}} (p : pullback f g ⟶ Z)
      (y : Z.presheaf.stalk (p.base (e.hom.base x'))) (c : (pullback f g).presheaf.stalk _),
      c = (p.stalkMap (e.hom.base x')).hom y →
        (e.hom.stalkMap x').hom c = ((e.hom ≫ p).stalkMap x').hom y := by
    rintro Z p y c rfl
    exact (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (Scheme.Hom.stalkMap_comp e.hom p x')) y).symm
  refine ⟨(e.hom.stalkMap x').hom.comp
      (φ₀ : TensorProduct R A B →+* (pullback f g).presheaf.stalk (e.hom.base x')),
    RingHom.ext fun t => ?_, RingHom.ext fun t => ?_, ?_⟩
  · exact key _ t _ (DFunLike.congr_fun hL t)
  · exact key _ t _ (DFunLike.congr_fun hR t)
  · exact ⟨M, isLocalization_of_comp_ringEquiv (T := TensorProduct R A B)
      (S := (pullback f g).presheaf.stalk (e.hom.base x')) (S' := C) φ₀
      (asIso (e.hom.stalkMap x')).commRingCatIsoToRingEquiv M hM⟩

/-! ### Transport of a tensor product and of a localization along ring isomorphisms -/

section Transport

variable {R A B R' A' B' : Type*} [CommRing R] [CommRing A] [CommRing B]
  [CommRing R'] [CommRing A'] [CommRing B']
  [Algebra R A] [Algebra R B] [Algebra R' A'] [Algebra R' B']

/-- **A tensor product follows ring isomorphisms of its base and of its two factors**, as a ring
homomorphism `A ⊗_R B ⟶ A' ⊗_{R'} B'`.

`Stacks.SheafifyStalk.stalkInverseImageIso`-style identifications of all three rings are exactly
this data, which is why the transport is stated for bare ring isomorphisms together with the two
squares `hA`, `hB` saying that they commute with the structure maps of the base.  The target is
given the `R`-algebra structure induced by `eR`, so that
`Algebra.TensorProduct.lift` applies to the two factors.

`AlgebraicGeometry.BaseChangeStalk.tensorRingEquivOfRingEquiv` upgrades this to an isomorphism;
this is its underlying map, kept separate so that its value on pure tensors is available before
the inverse is built. -/
noncomputable def tensorMapOfRingEquiv (eR : R ≃+* R') (eA : A ≃+* A') (eB : B ≃+* B')
    (hA : ∀ r : R, eA (algebraMap R A r) = algebraMap R' A' (eR r))
    (hB : ∀ r : R, eB (algebraMap R B r) = algebraMap R' B' (eR r)) :
    TensorProduct R A B →+* TensorProduct R' A' B' :=
  letI : Algebra R (TensorProduct R' A' B') :=
    ((algebraMap R' (TensorProduct R' A' B')).comp (eR : R →+* R')).toAlgebra
  (Algebra.TensorProduct.lift (R := R) (S := R)
    (⟨(Algebra.TensorProduct.includeLeftRingHom (R := R') (A := A') (B := B')).comp
        (eA : A →+* A'), fun r => by
      change (eA (algebraMap R A r)) ⊗ₜ[R'] (1 : B') = _
      rw [hA r]
      rfl⟩)
    (⟨((Algebra.TensorProduct.includeRight : B' →ₐ[R'] TensorProduct R' A' B').toRingHom).comp
        (eB : B →+* B'), fun r => by
      change (1 : A') ⊗ₜ[R'] (eB (algebraMap R B r)) = _
      rw [hB r]
      exact (Algebra.TensorProduct.includeRight (R := R') (A := A') (B := B')).commutes (eR r)⟩)
    (fun _ _ => Commute.all _ _)).toRingHom

/-- The transport of a tensor product sends a pure tensor to the pure tensor of the images. -/
@[simp]
theorem tensorMapOfRingEquiv_tmul (eR : R ≃+* R') (eA : A ≃+* A') (eB : B ≃+* B')
    (hA : ∀ r : R, eA (algebraMap R A r) = algebraMap R' A' (eR r))
    (hB : ∀ r : R, eB (algebraMap R B r) = algebraMap R' B' (eR r)) (a : A) (b : B) :
    tensorMapOfRingEquiv eR eA eB hA hB (a ⊗ₜ[R] b) = (eA a) ⊗ₜ[R'] (eB b) := by
  show (eA a ⊗ₜ[R'] (1 : B')) * ((1 : A') ⊗ₜ[R'] eB b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- **A tensor product follows ring isomorphisms of its base and of its two factors.**  Given
`eR : R ≃+* R'`, `eA : A ≃+* A'` and `eB : B ≃+* B'` commuting with the structure maps of the
bases, `A ⊗_R B ≃+* A' ⊗_{R'} B'`.

The inverse is the transport along the three inverse isomorphisms, and the two composites are
identities because they are on pure tensors. -/
noncomputable def tensorRingEquivOfRingEquiv (eR : R ≃+* R') (eA : A ≃+* A') (eB : B ≃+* B')
    (hA : ∀ r : R, eA (algebraMap R A r) = algebraMap R' A' (eR r))
    (hB : ∀ r : R, eB (algebraMap R B r) = algebraMap R' B' (eR r)) :
    TensorProduct R A B ≃+* TensorProduct R' A' B' :=
  RingEquiv.ofRingHom (tensorMapOfRingEquiv eR eA eB hA hB)
    (tensorMapOfRingEquiv eR.symm eA.symm eB.symm
      (fun r' => by
        refine (eA.symm_apply_eq).2 ?_
        rw [hA (eR.symm r'), eR.apply_symm_apply])
      (fun r' => by
        refine (eB.symm_apply_eq).2 ?_
        rw [hB (eR.symm r'), eR.apply_symm_apply]))
    (RingHom.ext fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => simp_all [map_add])
    (RingHom.ext fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => simp_all [map_add])

/-- The transport isomorphism of a tensor product sends a pure tensor to the pure tensor of the
images. -/
@[simp]
theorem tensorRingEquivOfRingEquiv_tmul (eR : R ≃+* R') (eA : A ≃+* A') (eB : B ≃+* B')
    (hA : ∀ r : R, eA (algebraMap R A r) = algebraMap R' A' (eR r))
    (hB : ∀ r : R, eB (algebraMap R B r) = algebraMap R' B' (eR r)) (a : A) (b : B) :
    tensorRingEquivOfRingEquiv eR eA eB hA hB (a ⊗ₜ[R] b) = (eA a) ⊗ₜ[R'] (eB b) :=
  tensorMapOfRingEquiv_tmul eR eA eB hA hB a b

end Transport

/-- **Transport of a localization along an isomorphism of the ring being localized.**  If `S` is
a localization of `T` at `M` for the algebra structure given by `φ : T → S`, and `e : T' ≃+* T`
is a ring isomorphism, then `S` is a localization of `T'` for the algebra structure given by
`φ ∘ e` — at the preimage of `M`, which is why the submonoid is existentially quantified rather
than named.

The companion of `AlgebraicGeometry.BaseChangeStalk.isLocalization_of_comp_ringEquiv`, which
moves the *target* of a localization instead.  Stated over bare commutative rings for the same
reason: it is applied to a ring map whose source is a tensor product. -/
theorem exists_isLocalization_of_source_ringEquiv {T T' S : Type*} [CommRing T] [CommRing T']
    [CommRing S] (e : T' ≃+* T) (φ : T →+* S) (M : Submonoid T)
    (hM : letI := φ.toAlgebra; IsLocalization M S) :
    letI := (φ.comp (e : T' →+* T)).toAlgebra; ∃ M' : Submonoid T', IsLocalization M' S := by
  let _ : Algebra T S := φ.toAlgebra
  let _ : Algebra T' S := (φ.comp (e : T' →+* T)).toAlgebra
  have := hM
  exact ⟨M.comap (e : T' →+* T),
    IsLocalization.of_ringEquiv_left e (Submonoid.map_comap_eq_of_surjective e.surjective M)
      (fun _ => rfl)⟩

/-! ### Naturality of the inverse-image stalk comparison in the sheaf -/

section Naturality

open TopCat.Presheaf

-- as in `StacksFrontier.AlgebraicGeometry.SheafifyStalk.Basic`: `TopCat.Presheaf.stalk` is a `def`,
-- so the domain of the stalk comparison and the stalk functor applied to the inverse image are
-- definitionally but not syntactically equal, and `rw` cannot see through that on its own.
attribute [local implicit_reducible] TopCat.Presheaf.stalk

variable {X Y : TopCat.{v}} (A : Type w) [Category.{v} A] {FA : A → A → Type*} {CA : A → Type v}
variable [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{v} A FA] [HasColimits A]
variable [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

/-- **The stalk of the sheaf inverse image is natural in the sheaf.**  For `α : F ⟶ G` of
sheaves on `Y` the square relating `(f⁻¹F)_x ≅ F_{f(x)}` and `(f⁻¹G)_x ≅ G_{f(x)}` commutes,
here in the direction of the inverses.

`Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_comp` already says that the comparison is
compatible with adjunction, for an arbitrary morphism `φ : f⁻¹F ⟶ G'` out of the inverse image;
naturality is that statement at `φ = f⁻¹α`, whose adjoint transpose is `α` followed by the unit
by naturality of the unit, read back through
`Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_eq`.

This and `stalkSheafPullbackIso_hom_naturality` belong with the other properties of the
comparison, in `StacksFrontier.AlgebraicGeometry.SheafifyStalk.StalkMap`, whose module docstring
records them as missing; they are stated here so that this file is the only one changed. -/
theorem stalkSheafPullbackIso_naturality (f : X ⟶ Y) {F G : TopCat.Sheaf A Y} (α : F ⟶ G)
    (x : X) :
    (Stacks.SheafifyStalk.stalkSheafPullbackIso A f F x).inv ≫
        (stalkFunctor A x).map ((TopCat.Sheaf.pullback A f).map α).hom =
      (stalkFunctor A (f x)).map α.hom ≫
        (Stacks.SheafifyStalk.stalkSheafPullbackIso A f G x).inv := by
  have hu : (TopCat.Sheaf.pullbackPushforwardAdjunction A f).homEquiv F
        ((TopCat.Sheaf.pullback A f).obj G) ((TopCat.Sheaf.pullback A f).map α) =
      α ≫ (TopCat.Sheaf.pullbackPushforwardAdjunction A f).unit.app G :=
    (Adjunction.homEquiv_unit _ _ _ _).trans
      ((TopCat.Sheaf.pullbackPushforwardAdjunction A f).unit.naturality α).symm
  refine (Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_comp A f
      ((TopCat.Sheaf.pullback A f).map α) x).trans ?_
  refine (congrArg (fun z : F ⟶ (TopCat.Sheaf.pushforward A f).obj
      ((TopCat.Sheaf.pullback A f).obj G) =>
    (stalkFunctor A (f x)).map (InducedCategory.Hom.hom z) ≫
      TopCat.Presheaf.stalkPushforward A f
        ((TopCat.Sheaf.pullback A f).obj G).presheaf x) hu).trans ?_
  refine (congrArg (fun z => z ≫ TopCat.Presheaf.stalkPushforward A f
      ((TopCat.Sheaf.pullback A f).obj G).presheaf x)
    (CategoryTheory.Functor.map_comp (stalkFunctor A (f x)) α.hom
      ((TopCat.Sheaf.pullbackPushforwardAdjunction A f).unit.app G).hom)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun z => (stalkFunctor A (f x)).map α.hom ≫ z)
    (Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_eq A f G x).symm

/-- **The stalk of the sheaf inverse image is natural in the sheaf**, in the direction of the
isomorphisms themselves: `(f⁻¹α)_x` followed by `(f⁻¹G)_x ≅ G_{f(x)}` is `(f⁻¹F)_x ≅ F_{f(x)}`
followed by `α_{f(x)}`.  `stalkSheafPullbackIso_naturality` with both isomorphisms moved to the
other side. -/
theorem stalkSheafPullbackIso_hom_naturality (f : X ⟶ Y) {F G : TopCat.Sheaf A Y} (α : F ⟶ G)
    (x : X) :
    (stalkFunctor A x).map ((TopCat.Sheaf.pullback A f).map α).hom ≫
        (Stacks.SheafifyStalk.stalkSheafPullbackIso A f G x).hom =
      (Stacks.SheafifyStalk.stalkSheafPullbackIso A f F x).hom ≫
        (stalkFunctor A (f x)).map α.hom := by
  rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
  exact stalkSheafPullbackIso_naturality A f α x

end Naturality

/-! ### The stalks of the inverse-image structure sheaves of a square -/

section InverseImage

variable {X Y X' Y' : Scheme.{u}}

/-- **The stalk of `(g')^{-1}f^{-1}𝒪_Y` at `x'` is `𝒪_{Y,(g' ≫ f)(x')}`.**

A *double* inverse image, so this is `Stacks.SheafifyStalk.stalkInverseImageIso` at the sheaf
`f^{-1}𝒪_Y` on `X`, which carries the stalk at `x'` to the stalk of `f^{-1}𝒪_Y` at `g'(x')`,
followed by `Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso` for `f` at that point. -/
noncomputable def stalkInverseImageBaseRingIso (f : X ⟶ Y) (g' : X' ⟶ X) (x' : X'.carrier) :
    (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom).presheaf.stalk x' ≅
      Y.presheaf.stalk ((g' ≫ f).base x') :=
  (Stacks.SheafifyStalk.stalkInverseImageIso g'
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) x').trans
    (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f (g'.base x'))

/-- **The stalk of `(g')^{-1}𝒪_X` at `x'` is `𝒪_{X,g'(x')}`.**  This is
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso` for `g'`, read at the spelling
`Stacks.SheafOfModules.inverseImageMiddleRing` of the middle sheaf of rings of the tower
`(g')^{-1}f^{-1}𝒪_Y ⟶ (g')^{-1}𝒪_X ⟶ 𝒪_{X'}`. -/
noncomputable def stalkInverseImageMiddleRingIso (g' : X' ⟶ X) (x' : X'.carrier) :
    (inverseImageMiddleRing g'.toLRSHom.toShHom).presheaf.stalk x' ≅
      X.presheaf.stalk (g'.base x') :=
  Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso g' x'

/-- **The stalk of `(f')^{-1}𝒪_{Y'}` at `x'` is `𝒪_{Y',f'(x')}`.**  This is
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso` for `f'`, read at the spelling
`Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf` of the middle sheaf of rings of the
tower `(g')^{-1}f^{-1}𝒪_Y ⟶ (f')^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}`. -/
noncomputable def stalkInverseImageSheafIso (f' : X' ⟶ Y') (x' : X'.carrier) :
    (inverseImageSheaf f'.toLRSHom.toShHom).presheaf.stalk x' ≅
      Y'.presheaf.stalk (f'.base x') :=
  Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f' x'

/-- **The stalk of the structure map `h^{-1}𝒪_S ⟶ 𝒪_T` of a morphism of schemes is its stalk
map**, read through the identification of the stalk of `h^{-1}𝒪_S` with `𝒪_{S,h(t)}`.

This is `Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_hom_comp_stalkMap` in the
spelling `Stacks.SheafOfModules.ringedSpaceStructureMap` of the structure map, which is the one
the towers of naive cotangent complexes on `X'` are built from; the two spellings of the
structure map are the same morphism. -/
theorem stalk_ringedSpaceStructureMap {T S : Scheme.{u}} (h : T ⟶ S) (t : T.carrier) :
    (TopCat.Presheaf.stalkFunctor CommRingCat.{u} t).map
        (ringedSpaceStructureMap h.toLRSHom.toShHom).hom =
      (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso h t).hom ≫ h.stalkMap t :=
  (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_hom_comp_stalkMap h t).symm

/-- **The stalk of the first map `(g')^{-1}f^{-1}𝒪_Y ⟶ (g')^{-1}𝒪_X` of the tower is the stalk
map of `f`**, read through the identifications of the two stalks.

The inverse image along `g'` of the structure map of `f`, so this is
`stalkSheafPullbackIso_hom_naturality` for `g'` at the structure map of `f`, followed by
`stalk_ringedSpaceStructureMap` for `f` at `g'(x')`.  It is what makes the `R`-algebra structure
of `A` in `stalk_isLocalization_of_isPullback_inverseImage` below the sheaf-level one. -/
theorem stalkInverseImageBaseRingIso_hom_comp_stalkMap (f : X ⟶ Y) (g' : X' ⟶ X)
    (x' : X'.carrier) :
    (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x').map
          (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom).hom ≫
        (stalkInverseImageMiddleRingIso g' x').hom =
      (stalkInverseImageBaseRingIso f g' x').hom ≫ f.stalkMap (g'.base x') := by
  refine (stalkSheafPullbackIso_hom_naturality CommRingCat.{u} g'.base
    (ringedSpaceStructureMap f.toLRSHom.toShHom) x').trans ?_
  refine (congrArg (fun z => (Stacks.SheafifyStalk.stalkInverseImageIso g'
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) x').hom ≫ z)
    (stalk_ringedSpaceStructureMap f (g'.base x'))).trans ?_
  exact (Category.assoc _ _ _).symm

/-- **The local ring at a point of a cartesian square is a localization of the tensor product of
the stalks of the inverse-image structure sheaves.**  For a cartesian square `g' ≫ f = f' ≫ g`
of schemes and a point `x'` of `X'`, write `R`, `A`, `B` for the stalks at `x'` of the three
sheaves of commutative rings `(g')^{-1}f^{-1}𝒪_Y`, `(g')^{-1}𝒪_X` and `(f')^{-1}𝒪_{Y'}` on
`X'`, and let `A` and `B` be algebras over `R` through the stalk maps of `f` and of `g` read
along the three identifications.  Then there is a ring map `A ⊗_R B ⟶ 𝒪_{X',x'}` restricting on
the two factors to the stalks of the structure maps of `(g')^{-1}𝒪_X` and of `(f')^{-1}𝒪_{Y'}`,
and it exhibits `𝒪_{X',x'}` as a localization of its source.

This is `AlgebraicGeometry.BaseChangeStalk.stalk_isLocalization_of_isPullback` in the spelling
the base change map of the naive cotangent complex of a square of schemes is built in. -/
theorem stalk_isLocalization_of_isPullback_inverseImage (f : X ⟶ Y) (g : Y' ⟶ Y)
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : IsPullback g' f' f g) (x' : X'.carrier) :
    let hpt : (g' ≫ f).base x' = (f' ≫ g).base x' :=
      congrArg (fun k : X' ⟶ Y => k.base x') hsq.w
    let R := (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom).presheaf.stalk x'
    let A := (inverseImageMiddleRing g'.toLRSHom.toShHom).presheaf.stalk x'
    let B := (inverseImageSheaf f'.toLRSHom.toShHom).presheaf.stalk x'
    let C := X'.presheaf.stalk x'
    letI : Algebra R A :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x').map
        (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom).hom).hom.toAlgebra
    letI : Algebra R B :=
      ((stalkInverseImageBaseRingIso f g' x').hom ≫ eqToHom (congrArg Y.presheaf.stalk hpt) ≫
        g.stalkMap (f'.base x') ≫ (stalkInverseImageSheafIso f' x').inv).hom.toAlgebra
    ∃ φ : TensorProduct R A B →+* C,
      φ.comp Algebra.TensorProduct.includeLeftRingHom =
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x').map
          (ringedSpaceStructureMap g'.toLRSHom.toShHom).hom).hom ∧
      φ.comp Algebra.TensorProduct.includeRight.toRingHom =
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x').map
          (ringedSpaceStructureMap f'.toLRSHom.toShHom).hom).hom ∧
      letI : Algebra (TensorProduct R A B) C := φ.toAlgebra
      ∃ M : Submonoid (TensorProduct R A B), IsLocalization M C := by
  intro hpt R A B C
  let _ : Algebra R A :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x').map
      (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom).hom).hom.toAlgebra
  let _ : Algebra R B :=
    ((stalkInverseImageBaseRingIso f g' x').hom ≫ eqToHom (congrArg Y.presheaf.stalk hpt) ≫
      g.stalkMap (f'.base x') ≫ (stalkInverseImageSheafIso f' x').inv).hom.toAlgebra
  let _ : Algebra (Y.presheaf.stalk ((g' ≫ f).base x')) (X.presheaf.stalk (g'.base x')) :=
    (f.stalkMap (g'.base x')).hom.toAlgebra
  let _ : Algebra (Y.presheaf.stalk ((g' ≫ f).base x')) (Y'.presheaf.stalk (f'.base x')) :=
    ((eqToHom (congrArg Y.presheaf.stalk hpt)) ≫ g.stalkMap (f'.base x')).hom.toAlgebra
  obtain ⟨φ₀, hL, hR, M, hM⟩ := stalk_isLocalization_of_isPullback f g g' f' hsq x'
  set eR := (stalkInverseImageBaseRingIso f g' x').commRingCatIsoToRingEquiv
  set eA := (stalkInverseImageMiddleRingIso g' x').commRingCatIsoToRingEquiv
  set eB := (stalkInverseImageSheafIso f' x').commRingCatIsoToRingEquiv
  have hA : ∀ r : R, eA (algebraMap R A r) =
      algebraMap (Y.presheaf.stalk ((g' ≫ f).base x'))
        (X.presheaf.stalk (g'.base x')) (eR r) :=
    fun r => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (stalkInverseImageBaseRingIso_hom_comp_stalkMap f g' x')) r
  have hB : ∀ r : R, eB (algebraMap R B r) =
      algebraMap (Y.presheaf.stalk ((g' ≫ f).base x'))
        (Y'.presheaf.stalk (f'.base x')) (eR r) :=
    fun r => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (stalkInverseImageSheafIso f' x').inv_hom_id) _
  refine ⟨φ₀.comp (tensorRingEquivOfRingEquiv eR eA eB hA hB : _ →+* _),
    RingHom.ext fun a => ?_, RingHom.ext fun b => ?_, ?_⟩
  · change φ₀ (tensorRingEquivOfRingEquiv eR eA eB hA hB (a ⊗ₜ[R] (1 : B))) = _
    rw [tensorRingEquivOfRingEquiv_tmul, map_one, stalk_ringedSpaceStructureMap g' x']
    exact DFunLike.congr_fun hL (eA a)
  · change φ₀ (tensorRingEquivOfRingEquiv eR eA eB hA hB ((1 : A) ⊗ₜ[R] b)) = _
    rw [tensorRingEquivOfRingEquiv_tmul, map_one, stalk_ringedSpaceStructureMap f' x']
    exact DFunLike.congr_fun hR (eB b)
  · exact exists_isLocalization_of_source_ringEquiv
      (tensorRingEquivOfRingEquiv eR eA eB hA hB) φ₀ M hM

/-- **The local ring at a point of a cartesian square is a localization of the tensor product of
the stalks of the inverse-image structure sheaves**, with the two tensor factors in the other
order.

`AlgebraicGeometry.BaseChangeStalk.stalk_isLocalization_of_isPullback_inverseImage` composed
with `Algebra.TensorProduct.comm`.  This is the order the ring-level flat base change of the
naive cotangent complex consumes — `B ⊗_R A` with `B` the stalk of `(f')^{-1}𝒪_{Y'}`, the factor
that flatness of `g` makes flat over `R`. -/
theorem stalk_isLocalization_of_isPullback_inverseImage_comm (f : X ⟶ Y) (g : Y' ⟶ Y)
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : IsPullback g' f' f g) (x' : X'.carrier) :
    let hpt : (g' ≫ f).base x' = (f' ≫ g).base x' :=
      congrArg (fun k : X' ⟶ Y => k.base x') hsq.w
    let R := (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom).presheaf.stalk x'
    let A := (inverseImageMiddleRing g'.toLRSHom.toShHom).presheaf.stalk x'
    let B := (inverseImageSheaf f'.toLRSHom.toShHom).presheaf.stalk x'
    let C := X'.presheaf.stalk x'
    letI : Algebra R A :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x').map
        (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom).hom).hom.toAlgebra
    letI : Algebra R B :=
      ((stalkInverseImageBaseRingIso f g' x').hom ≫ eqToHom (congrArg Y.presheaf.stalk hpt) ≫
        g.stalkMap (f'.base x') ≫ (stalkInverseImageSheafIso f' x').inv).hom.toAlgebra
    ∃ φ : TensorProduct R B A →+* C,
      φ.comp Algebra.TensorProduct.includeLeftRingHom =
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x').map
          (ringedSpaceStructureMap f'.toLRSHom.toShHom).hom).hom ∧
      φ.comp Algebra.TensorProduct.includeRight.toRingHom =
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x').map
          (ringedSpaceStructureMap g'.toLRSHom.toShHom).hom).hom ∧
      letI : Algebra (TensorProduct R B A) C := φ.toAlgebra
      ∃ M : Submonoid (TensorProduct R B A), IsLocalization M C := by
  intro hpt R A B C
  let _ : Algebra R A :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x').map
      (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom).hom).hom.toAlgebra
  let _ : Algebra R B :=
    ((stalkInverseImageBaseRingIso f g' x').hom ≫ eqToHom (congrArg Y.presheaf.stalk hpt) ≫
      g.stalkMap (f'.base x') ≫ (stalkInverseImageSheafIso f' x').inv).hom.toAlgebra
  obtain ⟨φ₀, hL, hR, M, hM⟩ :=
    stalk_isLocalization_of_isPullback_inverseImage f g g' f' hsq x'
  refine ⟨φ₀.comp ((Algebra.TensorProduct.comm R B A).toRingEquiv : _ →+* _),
    RingHom.ext fun b => ?_, RingHom.ext fun a => ?_, ?_⟩
  · exact DFunLike.congr_fun hR b
  · exact DFunLike.congr_fun hL a
  · exact exists_isLocalization_of_source_ringEquiv
      (Algebra.TensorProduct.comm R B A).toRingEquiv φ₀ M hM

end InverseImage

end AlgebraicGeometry.BaseChangeStalk

end
