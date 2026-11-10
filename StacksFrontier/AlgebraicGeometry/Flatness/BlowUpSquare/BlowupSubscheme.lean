module

public import Mathlib.RingTheory.TensorProduct.Free
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubscheme
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Functors.Module.FlatPullback
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# The closed subscheme of the modified divisor, and the locally free locus after modification

Let `(X, D, M)` be a triple as in Situation 0F8S, let `b : X' ⟶ X` be the morphism of Stacks tag
0GTY with `D' = b⁻¹D`, let `Q = Lη_{ℐ'}Lb^*M` be the perfect object of tag 0F8U, and let
`W ⊆ X` be the maximal open over which the cohomology sheaves of `M` are locally free. Stacks
tag 0F8X asserts the existence of a closed immersion `i : T ⟶ D'` of finite presentation such
that (1) `D' ∩ b⁻¹(W) ⊆ T` scheme theoretically, (2) `Li^*Q` has locally free cohomology
sheaves, and (3) for `t ∈ T` over `w ∈ W` the rank of `H^i(Li^*Q)_t` equals the rank of
`H^i(M)_x`.

This file proves that if `b⁻¹W ↪ X' ⟶ X` is flat, then `b⁻¹W` is contained in the maximal open
`W' ⊆ X'` over which `Lb^*M` has locally free cohomology, and deduces the finite presentation of
`i` and part (1) for a closed subscheme `T` whose ideal is prescribed on good charts.

## Main definitions

* `Stacks.BlowUpComplexes.homologyDerivedPullbackIso`: `H^i(Lf^*E) ≅ f^*H^i(E)` for a morphism
  of ringed spaces whose module pullback is exact.

## Main results

* `Stacks.BlowUpComplexes.preimage_subset_cohomologyFiniteFreeLocus_derivedPullback` and
  `Stacks.BlowUpComplexes.mem_cohomologyFiniteFreeLocus_of_mem_derivedPullback`: the finite free
  cohomology locus of a derived pullback along a morphism with exact module pullback contains the
  preimage of the finite free cohomology locus, and descends again when the germ maps on local
  rings are bijective.
* `AlgebraicGeometry.ComplexAndDivisorSituation.le_locallyFreeLocus_pullback`: `b⁻¹W ⊆ W'`, for
  a `b` whose restriction over `W` is flat.
* `AlgebraicGeometry.ComplexAndDivisorSituation`
  `.locallyOfFinitePresentation_and_comap_eq_bot_of_isGoodOver`: the closed immersion
  `i : T ⟶ D'` is locally of finite presentation, and `D' ∩ b⁻¹(W) ⊆ T` scheme theoretically.

## References

* [Stacks Project, Tag 0F8X](https://stacks.math.columbia.edu/tag/0F8X)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0GTZ](https://stacks.math.columbia.edu/tag/0GTZ)
* [Stacks Project, Tag 0F8W](https://stacks.math.columbia.edu/tag/0F8W)
* [Stacks Project, Tag 0GT1](https://stacks.math.columbia.edu/tag/0GT1)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory StrictlyPerfect AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance] HasDerivedCategory.standard

universe u d

namespace Stacks.BlowUpComplexes

/-! ### Base change of a finite free module -/

section Algebra

variable {R S N : Type u} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup N] [Module R N]

/-- Base change of a finite free module along a ring homomorphism is finite free. -/
@[sga "1 III 1.4" "special case"]
private theorem free_and_finite_tensorProduct
    (hfree : Module.Free R N) (hfin : Module.Finite R N) :
    Module.Free S (TensorProduct R S N) ∧ Module.Finite S (TensorProduct R S N) := by
  have _ := hfree
  have _ := hfin
  let b := Module.Free.chooseBasis R N
  have hfinite : Finite (Module.Free.ChooseBasisIndex R N) :=
    Finite.of_fintype (Module.Free.ChooseBasisIndex R N)
  exact ⟨Module.Free.of_basis (Algebra.TensorProduct.basis S b),
    Module.Finite.of_basis (Algebra.TensorProduct.basis S b)⟩

/-- Along a bijective ring homomorphism, finite freeness of the base change descends. -/
private theorem free_and_finite_of_tensorProduct (hbij : Function.Bijective (algebraMap R S))
    (hfree : Module.Free S (TensorProduct R S N))
    (hfin : Module.Finite S (TensorProduct R S N)) :
    Module.Free R N ∧ Module.Finite R N := by
  have _ := hfree
  have _ := hfin
  let eR : R ≃+* S := RingEquiv.ofBijective (algebraMap R S) hbij
  have heR : ∀ r : R, eR r = algebraMap R S r := fun _ => rfl
  have hsmul : ∀ (r : R) (s : S), r • s = eR r * s := fun r s => Algebra.smul_def r s
  let fS : S →ₗ[R] R :=
    { toFun := eR.symm
      map_add' := fun s t => eR.symm.map_add s t
      map_smul' := fun r s => by
        change eR.symm (r • s) = r • eR.symm s
        rw [hsmul, map_mul, eR.symm_apply_apply, smul_eq_mul] }
  let eS : S ≃ₗ[R] R := LinearEquiv.ofBijective fS eR.symm.bijective
  let elid : TensorProduct R S N ≃ₗ[R] N :=
    (TensorProduct.congr eS (LinearEquiv.refl R N)).trans (TensorProduct.lid R N)
  have _h1 : RingHomInvPair (eR.symm : S →+* R) (eR : R →+* S) :=
    RingHomInvPair.of_ringEquiv eR.symm
  have _h2 : RingHomInvPair (eR : R →+* S) (eR.symm : S →+* R) :=
    RingHomInvPair.of_ringEquiv_symm eR.symm
  let eScalar : TensorProduct R S N ≃ₛₗ[(eR.symm : S →+* R)] TensorProduct R S N :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro s z
        change s • z = eR.symm s • z
        rw [← algebraMap_smul (A := S) (R := R) (eR.symm s) z, ← heR, eR.apply_symm_apply] }
  have hfreeR : Module.Free R (TensorProduct R S N) := Module.Free.of_equiv eScalar
  have _hSfin : Module.Finite R S := Module.Finite.equiv eS.symm
  have hfinR : Module.Finite R (TensorProduct R S N) :=
    Module.Finite.trans S (TensorProduct R S N)
  exact ⟨Module.Free.of_equiv' hfreeR elid, Module.Finite.equiv elid⟩

end Algebra

/-! ### Finite freeness of a stalk -/

section Stalk

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

/-- The finite free cohomology locus of Stacks tag 0GT1 is the set of points at which every
cohomology sheaf has a finite free stalk. -/
theorem mem_cohomologyFiniteFreeLocus_iff_forall_freeAndFiniteStalk
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (E : DerivedCategory (OXMod.{u, u} X))
    (x : X.carrier) :
    x ∈ RingedSpace.cohomologyFiniteFreeLocus E ↔
      ∀ i : ℤ, RingedSpace.FreeAndFiniteStalk
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E) x :=
  Iff.rfl

/-- An isomorphism of `𝒪_X`-modules induces an `𝒪_{X,x}`-linear isomorphism of stalks. -/
private def stalkLinearEquivOfIso {M N : OXMod.{u, u} X} (e : M ≅ N) (x : X.carrier) :
    ToType (TopCat.Presheaf.stalk M.val.presheaf x) ≃ₗ[ToType (X.presheaf.stalk x)]
      ToType (TopCat.Presheaf.stalk N.val.presheaf x) :=
  LinearEquiv.ofBijective
    (RingedSpace.stalkLinearMapOfHom ((RingedSpace.moduleStalkFunctor X x).map e.hom))
    ((ConcreteCategory.isIso_iff_bijective ((RingedSpace.moduleStalkFunctor X x).map e.hom)).1
      (inferInstanceAs (IsIso ((RingedSpace.moduleStalkFunctor X x).mapIso e).hom)))

/-- Finite freeness of a stalk only depends on the isomorphism class of the module. -/
theorem FreeAndFiniteStalk.of_iso {M N : OXMod.{u, u} X} (e : M ≅ N) {x : X.carrier}
    (h : RingedSpace.FreeAndFiniteStalk M x) : RingedSpace.FreeAndFiniteStalk N x :=
  have _ := h.1
  have _ := h.2
  ⟨Module.Free.of_equiv (stalkLinearEquivOfIso e x),
    Module.Finite.equiv (stalkLinearEquivOfIso e x)⟩

variable {Y : AlgebraicGeometry.RingedSpace.{u, u}}

/-- The stalk at `x` of a module isomorphic to the pullback `f^*G` is the base change along the
germ map of the stalk of `G` at `f x`. -/
private theorem exists_pullbackStalkLinearEquiv (f : X ⟶ Y) (G : OXMod.{u, u} Y)
    {P : OXMod.{u, u} X} (ε : P ≅ (modulePullback f).obj G) (x : X.carrier) :
    letI : Algebra (ToType (Y.presheaf.stalk (f.hom.base x))) (ToType (X.presheaf.stalk x)) :=
      (f.hom.stalkMap x).hom.toAlgebra
    Nonempty (ToType (TopCat.Presheaf.stalk P.val.presheaf x) ≃ₗ[ToType (X.presheaf.stalk x)]
      TensorProduct (ToType (Y.presheaf.stalk (f.hom.base x))) (ToType (X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk G.val.presheaf (f.hom.base x)))) := by
  let _ : Algebra (ToType (Y.presheaf.stalk (f.hom.base x))) (ToType (X.presheaf.stalk x)) :=
    (f.hom.stalkMap x).hom.toAlgebra
  obtain ⟨e₀, -⟩ := exists_modulePullbackStalkLinearEquiv f G x
  obtain ⟨Q, hQ⟩ : ∃ Q : OXMod.{u, u} X, Q = (modulePullback f).obj G := ⟨_, rfl⟩
  have eQ : ToType (TopCat.Presheaf.stalk Q.val.presheaf x) ≃ₗ[ToType (X.presheaf.stalk x)]
      TensorProduct (ToType (Y.presheaf.stalk (f.hom.base x))) (ToType (X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk G.val.presheaf (f.hom.base x))) := by
    rw [hQ]; exact e₀
  have εQ : P ≅ Q := by rw [hQ]; exact ε
  exact ⟨(stalkLinearEquivOfIso εQ x).trans eQ⟩

/-- If the stalk of `G` at `f x` is finite free, then so is the stalk at `x` of any module
isomorphic to the pullback `f^*G`. -/
theorem freeAndFiniteStalk_of_iso_modulePullback (f : X ⟶ Y) (G : OXMod.{u, u} Y)
    {P : OXMod.{u, u} X} (ε : P ≅ (modulePullback f).obj G) (x : X.carrier)
    (h : RingedSpace.FreeAndFiniteStalk G (f.hom.base x)) : RingedSpace.FreeAndFiniteStalk P x := by
  let _ : Algebra (ToType (Y.presheaf.stalk (f.hom.base x))) (ToType (X.presheaf.stalk x)) :=
    (f.hom.stalkMap x).hom.toAlgebra
  obtain ⟨e⟩ := exists_pullbackStalkLinearEquiv f G ε x
  obtain ⟨h1, h2⟩ :=
    free_and_finite_tensorProduct (S := ToType (X.presheaf.stalk x)) h.1 h.2
  have _ := h2
  exact ⟨Module.Free.of_equiv' h1 e.symm, Module.Finite.equiv e.symm⟩

/-- If the germ map on stalks at `x` is bijective and the stalk at `x` of a module isomorphic to
the pullback `f^*G` is finite free, then the stalk of `G` at `f x` is finite free. -/
theorem freeAndFiniteStalk_of_freeAndFiniteStalk_of_iso_modulePullback (f : X ⟶ Y)
    (G : OXMod.{u, u} Y) {P : OXMod.{u, u} X} (ε : P ≅ (modulePullback f).obj G) (x : X.carrier)
    (hbij : Function.Bijective (f.hom.stalkMap x).hom) (h : RingedSpace.FreeAndFiniteStalk P x) :
    RingedSpace.FreeAndFiniteStalk G (f.hom.base x) := by
  let _ : Algebra (ToType (Y.presheaf.stalk (f.hom.base x))) (ToType (X.presheaf.stalk x)) :=
    (f.hom.stalkMap x).hom.toAlgebra
  obtain ⟨e⟩ := exists_pullbackStalkLinearEquiv f G ε x
  have _ := h.2
  exact free_and_finite_of_tensorProduct hbij (Module.Free.of_equiv' h.1 e)
    (Module.Finite.equiv e)

end Stalk

/-! ### The finite free cohomology locus and derived pullback -/

section DerivedPullback

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}}

/-- The finite free cohomology locus only depends on the isomorphism class of the object. -/
theorem cohomologyFiniteFreeLocus_congr [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    {E F : DerivedCategory (OXMod.{u, u} X)} (e : E ≅ F) :
    RingedSpace.cohomologyFiniteFreeLocus E = RingedSpace.cohomologyFiniteFreeLocus F := by
  ext x
  exact ⟨fun h i => FreeAndFiniteStalk.of_iso
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).mapIso e) (h i),
    fun h i => FreeAndFiniteStalk.of_iso
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).mapIso e).symm (h i)⟩

variable (f : X ⟶ Y) [Limits.PreservesFiniteLimits (modulePullback f)]
  [Limits.PreservesFiniteColimits (modulePullback f)]

/-- For a morphism with exact module pullback, `H^i(Lf^*E) ≅ f^*H^i(E)`. -/
def homologyDerivedPullbackIso (E : DerivedCategory (OXMod.{u, u} Y)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj ((derivedPullback f).obj E) ≅
      (modulePullback f).obj ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) i).obj E) :=
  (DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).mapIso
      ((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory f).app E) ≪≫
    ((modulePullback f).mapDerivedCategoryHomologyIso i).app E

/-- For a morphism with exact module pullback, the finite free cohomology locus of a derived
pullback contains the preimage of the finite free cohomology locus. -/
theorem preimage_subset_cohomologyFiniteFreeLocus_derivedPullback
    (E : DerivedCategory (OXMod.{u, u} Y)) :
    f.hom.base ⁻¹' RingedSpace.cohomologyFiniteFreeLocus E ⊆
      RingedSpace.cohomologyFiniteFreeLocus ((derivedPullback f).obj E) := fun x hx i =>
  freeAndFiniteStalk_of_iso_modulePullback f _ (homologyDerivedPullbackIso f E i) x (hx i)

/-- For a morphism with exact module pullback whose germ map on stalks at `x` is bijective, if `x`
lies in the finite free cohomology locus of the derived pullback of `E`, then its image lies in the
finite free cohomology locus of `E`. -/
theorem mem_cohomologyFiniteFreeLocus_of_mem_derivedPullback
    (E : DerivedCategory (OXMod.{u, u} Y)) (x : X.carrier)
    (hbij : Function.Bijective (f.hom.stalkMap x).hom)
    (hx : x ∈ RingedSpace.cohomologyFiniteFreeLocus ((derivedPullback f).obj E)) :
    f.hom.base x ∈ RingedSpace.cohomologyFiniteFreeLocus E := fun i =>
  freeAndFiniteStalk_of_freeAndFiniteStalk_of_iso_modulePullback f _
    (homologyDerivedPullbackIso f E i) x hbij (hx i)

end DerivedPullback

end Stacks.BlowUpComplexes

/-! ### The locally free locus of the pulled-back triple -/

namespace AlgebraicGeometry.ComplexAndDivisorSituation

open Stacks.BlowUpComplexes

variable (S : ComplexAndDivisorSituation.{u, d})

/-- The standard model of the derived category of `𝒪_X`-modules on a scheme. -/
private abbrev standardModel (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (OXMod.{u, u} X.toRingedSpace) :=
  HasDerivedCategory.standard _

/-- The perfect object of a triple as in Situation 0F8S, carried from the situation's own model
of the derived category of `𝒪_X`-modules to the standard model by the canonical equivalence of
two localizations at the quasi-isomorphisms. -/
private def standardModelObject :
    @DerivedCategory (OXMod.{u, u} S.X.toRingedSpace) _ _ (standardModel S.X) :=
  (Localization.uniq
      (@DerivedCategory.Q _ _ _ S.hasDerivedCategory)
      (@DerivedCategory.Q _ _ _ (standardModel S.X))
      (HomologicalComplex.quasiIso (OXMod.{u, u} S.X.toRingedSpace)
        (ComplexShape.up ℤ))).functor.obj S.M

/-- The cohomology of the object of a triple, read in the situation's own model of the derived
category, agrees with the cohomology of `standardModelObject`, read in the standard model. -/
private def homologyStandardModelObjectIso (i : ℤ) :
    (@DerivedCategory.homologyFunctor (OXMod.{u, u} S.X.toRingedSpace) _ _
        S.hasDerivedCategory i).obj S.M ≅
      (@DerivedCategory.homologyFunctor (OXMod.{u, u} S.X.toRingedSpace) _ _
        (standardModel S.X) i).obj S.standardModelObject :=
  ((@DerivedCategory.homologyFunctor _ _ _ S.hasDerivedCategory i).mapIso
      ((@DerivedCategory.Q _ _ _ S.hasDerivedCategory).objObjPreimageIso S.M)).symm ≪≫
    (@DerivedCategory.homologyFunctorFactors _ _ _ S.hasDerivedCategory i).app
      ((@DerivedCategory.Q _ _ _ S.hasDerivedCategory).objPreimage S.M) ≪≫
    ((@DerivedCategory.homologyFunctorFactors _ _ _ (standardModel S.X) i).app
      ((@DerivedCategory.Q _ _ _ S.hasDerivedCategory).objPreimage S.M)).symm ≪≫
    (@DerivedCategory.homologyFunctor _ _ _ (standardModel S.X) i).mapIso
      (((Localization.compUniqFunctor (@DerivedCategory.Q _ _ _ S.hasDerivedCategory)
            (@DerivedCategory.Q _ _ _ (standardModel S.X))
            (HomologicalComplex.quasiIso (OXMod.{u, u} S.X.toRingedSpace)
              (ComplexShape.up ℤ))).app
          ((@DerivedCategory.Q _ _ _ S.hasDerivedCategory).objPreimage S.M)).symm ≪≫
        (Localization.uniq (@DerivedCategory.Q _ _ _ S.hasDerivedCategory)
            (@DerivedCategory.Q _ _ _ (standardModel S.X))
            (HomologicalComplex.quasiIso (OXMod.{u, u} S.X.toRingedSpace)
              (ComplexShape.up ℤ))).functor.mapIso
          ((@DerivedCategory.Q _ _ _ S.hasDerivedCategory).objObjPreimageIso S.M))

/-- The locally free locus of a triple is contained in the finite free cohomology locus of
`standardModelObject`. -/
private theorem subset_cohomologyFiniteFreeLocus_standardModelObject :
    (S.locallyFreeLocus : Set S.X) ⊆
      @RingedSpace.cohomologyFiniteFreeLocus S.X.toRingedSpace (standardModel S.X)
        S.standardModelObject :=
  fun _ hx i => FreeAndFiniteStalk.of_iso (S.homologyStandardModelObjectIso i) (hx i)

/-- Let `j : X'' ⟶ X'` be an open immersion such that `j ≫ b` is flat. If `z : X''` lies over the
locally free locus of the triple, then the cohomology stalks of `Lb^*M` at `j z` are finite
free. -/
private theorem mem_cohomologyFiniteFreeLocus_derivedPullbackObject
    {X'' X' : Scheme.{u}} (j : X'' ⟶ X') (b : X' ⟶ S.X) [IsOpenImmersion j]
    (hjb : AlgebraicGeometry.Flat (j ≫ b)) (z : X'')
    (hz : (j ≫ b).base z ∈ (S.locallyFreeLocus : Set S.X)) :
    j.base z ∈ @RingedSpace.cohomologyFiniteFreeLocus X'.toRingedSpace (standardModel X')
      (S.derivedPullbackObject b) := by
  have hexact : ∀ {A B : AlgebraicGeometry.RingedSpace.{u, u}} (g : A ⟶ B),
      AlgebraicGeometry.IsFlat g → Limits.PreservesFiniteLimits (modulePullback g) ∧
        Limits.PreservesFiniteColimits (modulePullback g) := fun g hg =>
    ⟨preservesFiniteLimits_modulePullback_of_isFlat _ hg, preservesFiniteColimits_modulePullback _⟩
  obtain ⟨_, _⟩ := hexact (j.toLRSHom.toShHom ≫ b.toLRSHom.toShHom) (Flat.stalkMap (j ≫ b))
  obtain ⟨_, _⟩ := hexact j.toLRSHom.toShHom (Flat.stalkMap j)
  have h3 := Stacks.BlowUpComplexes.preimage_subset_cohomologyFiniteFreeLocus_derivedPullback
    (j.toLRSHom.toShHom ≫ b.toLRSHom.toShHom) S.standardModelObject
    (S.subset_cohomologyFiniteFreeLocus_standardModelObject hz)
  rw [← Stacks.BlowUpComplexes.cohomologyFiniteFreeLocus_congr
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      j.toLRSHom.toShHom b.toLRSHom.toShHom).app S.standardModelObject)] at h3
  exact Stacks.BlowUpComplexes.mem_cohomologyFiniteFreeLocus_of_mem_derivedPullback
    j.toLRSHom.toShHom _ _
    ((ConcreteCategory.isIso_iff_bijective (j.stalkMap z)).1 inferInstance) h3

/-- Let `(X, D, M)` be a triple as in Situation 0F8S, let `W ⊆ X` be the maximal open over which
the cohomology sheaves of `M` are locally free, and let `b : X' ⟶ X` be a morphism for which the
pullback of `D` is defined.  If the composite `b⁻¹W ↪ X' ⟶ X` is flat, then `b⁻¹W` is contained in
the maximal open `W' ⊆ X'` over which the cohomology sheaves of `Lb^*M` are locally free. -/
theorem le_locallyFreeLocus_pullback {X' : Scheme.{u}} (b : X' ⟶ S.X)
    (hD : Stacks.Divisors.IsPullbackDefined b S.D)
    (hflat : AlgebraicGeometry.Flat ((b ⁻¹ᵁ S.locallyFreeLocus).ι ≫ b)) :
    b ⁻¹ᵁ S.locallyFreeLocus ≤ (S.pullback b hD).locallyFreeLocus := fun x' hx' =>
  S.mem_cohomologyFiniteFreeLocus_derivedPullbackObject
    (b ⁻¹ᵁ S.locallyFreeLocus).ι b hflat ⟨x', hx'⟩ hx'

/-! ### Stacks tag 0F8X -/

/-- In Situation 0F8S let `b : X' ⟶ X` be good for the triple — condition (1) of tag 0GTY —
so that `D' = b⁻¹D` is defined and `(X', D', Lb^*M)` is a good triple, let `W ⊆ X` be the
maximal open over which the cohomology sheaves of `M` are locally free, and suppose that
`b⁻¹W ↪ X' ⟶ X` is flat. Let `T ⊆ D'` be a closed subscheme whose ideal over `D' ∩ U` is the
total obstruction ideal `J(N^•, g)` of More on Algebra, tag 0F81 for every affine chart
`(U, g, N^•)` of the pulled-back triple with principal determinantal ideals. Then

* the closed immersion `i : T ⟶ D'` is locally of finite presentation, and
* `D' ∩ b⁻¹(W) ⊆ T` scheme theoretically: the inverse image on `D' ∩ b⁻¹(W)` of the ideal sheaf
  of `T` is zero. -/
@[stacks 0F8X "the finite presentation of `i : T → b^{-1}D` and part (1), in the general form: \
over any `b` satisfying condition (1) of tag 0GTY and flat over `W` --- which is what Tag 0F8W \
supplies for the morphism tag 0GTY produces --- and for a closed subscheme `T` of `b^{-1}D` \
given to cut out the obstruction ideal of Tag 0F81 on every good chart of the pulled-back \
triple, as in Tag 0GTZ. Parts (2) and (3) specialize parts (2) and (3) of Tag 0GTZ, \
which need the chart-level comparison \
AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage over and above Tag 08DW --- that tag \
being proved in both its parts. The tag over the morphism tag 0GTY produces is \
AlgebraicGeometry.ComplexAndDivisorSituation.\
locallyOfFinitePresentation_and_comap_eq_bot_goodBlowupToBase"]
theorem locallyOfFinitePresentation_and_comap_eq_bot_of_isGoodOver
    {X' : Scheme.{u}} (b : X' ⟶ S.X) (hb : S.IsGoodOver b)
    (hflat : AlgebraicGeometry.Flat ((b ⁻¹ᵁ S.locallyFreeLocus).ι ≫ b))
    (T : (S.pullback b hb.pullbackDefined).D.subscheme.IdealSheafData)
    (hT : ∀ C : AffineChart (S.pullback b hb.pullbackDefined),
      (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) →
        T.ideal C.divisorAffineOpen = C.obstructionIdeal) :
    LocallyOfFinitePresentation T.subschemeι ∧
      T.comap ((S.pullback b hb.pullbackDefined).D.subschemeι ⁻¹ᵁ
        (b ⁻¹ᵁ S.locallyFreeLocus)).ι = ⊥ := by
  have hle : (S.pullback b hb.pullbackDefined).D.subschemeι ⁻¹ᵁ (b ⁻¹ᵁ S.locallyFreeLocus) ≤
      (S.pullback b hb.pullbackDefined).D.subschemeι ⁻¹ᵁ
        (S.pullback b hb.pullbackDefined).locallyFreeLocus := fun z hz =>
    S.le_locallyFreeLocus_pullback b hb.pullbackDefined hflat hz
  refine ⟨locallyOfFinitePresentation_subschemeι_of_ideal_eq_obstructionIdeal _
      hb.isGoodTriple T hT, Scheme.IdealSheafData.ext (funext fun V => ?_)⟩
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    ideal_eq_bot_of_le_preimage_locallyFreeLocus _ hb.isGoodTriple T hT _
      (le_trans (Scheme.Opens.ι_image_le _ V.1) hle),
    ← RingHom.ker_eq_comap_bot]
  exact RingHom.ker_coe_equiv
    ((((S.pullback b hb.pullbackDefined).D.subschemeι ⁻¹ᵁ
      (b ⁻¹ᵁ S.locallyFreeLocus)).ι.appIso V.1).symm).commRingCatIsoToRingEquiv

end AlgebraicGeometry.ComplexAndDivisorSituation

end
