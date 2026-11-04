module

public import StacksFrontier.Algebra.Homology.InjectiveDimension.Criteria
public import StacksFrontier.RingTheory.Dualizing.Gluing

/-!
# Gluing dualizing complexes along a standard open cover

Let `A` be a Noetherian ring and let `f : ι → A` be a family generating the unit ideal. If the
derived localization of `K ∈ D(A)` at every `f i` is a dualizing complex over `A_{f i}`, then `K`
is a dualizing complex over `A`: this is [stacks 0A7H], proved here as
`Dualizing.isDualizingComplex_of_localizations`.

The three defining conditions of [stacks 0A7B] are glued separately. Finiteness of the cohomology
and boundedness come from pseudo-coherence, which descends along a standard open cover, and are
proved in `StacksFrontier.RingTheory.Dualizing.Gluing`. The two conditions treated here both reduce
to vanishing statements about `Ext` groups, and both use the same comparison: for `X`
pseudo-coherent and `Y` bounded below, derived Hom commutes with the flat base change `A → A_g`
([stacks 0A6A]), and the cohomology of a derived localization is the localization of the
cohomology, so each `Ext^n_A(X, Y)` is a module whose localizations along the cover are the
`Ext^n_{A_g}(X_g, Y_g)`.

Finite injective dimension is then tested by vanishing of `Ext^i_A(A/J, K)` in high degrees
([stacks 0A5T]); the single complex on `A/J` is pseudo-coherent over a Noetherian ring, and the
injective amplitudes of the localizations of a finite subfamily of the cover supply a common
upper bound.

The homothety condition `A → RHom_A(K, K)` needs no compatibility between the base-change
comparison and the homothety, which is what makes it accessible: away from degree zero the
relevant cohomology vanishes locally, hence globally, and in degree zero the localization of
`E = End_{D(A)}(K)` is *abstractly* linearly isomorphic to `A_g`. Since `A_g ⊗_A E` is a unital
`A_g`-algebra that is free of rank one as a module, its structure map is automatically bijective
(`bijective_algebraMap_of_linearEquiv`), and bijectivity of `A → E` is local on the cover. The
rank-one input to `Dualizing.homothety_quasiIso_of_rankOne` is an arbitrary linear equivalence,
so this suffices.

## Main results

* `Dualizing.derivedInternalHomModelIso₂` — a bounded-below complex of injectives computes
  `RHom_R(X, -)` by the ordinary Hom complex, for an arbitrary first variable.
* `Dualizing.homologyDerivedInternalHomModelIso` and
  `Dualizing.extAddEquivHomologyDerivedInternalHom` — the degree-`n` cohomology of `RHom_R(X, Y)`
  read on the Hom complex of models, and as `Hom_{D(R)}(X, Y⟦n⟧)`.
* `Dualizing.localizationAwayDerivedInternalHomIso` — derived Hom out of a pseudo-coherent object
  into a bounded-below object commutes with the base change `A → A_g` ([stacks 0A6A]).
* `Dualizing.isZero_homology_derivedInternalHom_of_localizations` — vanishing of a cohomology
  module of such a derived Hom is local on a standard open cover.
* `Dualizing.hasFiniteInjectiveDimension_of_localizations` — condition (1) of [stacks 0A7B]
  glues.
* `Dualizing.isZero_homology_homComplexR_of_localizations` — the nonzero degrees of condition (3)
  glue.
* `Dualizing.bijective_algebraMap_of_localizations` — an algebra whose base changes along a
  standard open cover are free of rank one has bijective structure map.
* `Dualizing.isDualizingComplex_of_localizations` — [stacks 0A7H].

## Implementation notes

The derived internal Hom used here is `Stacks.DerivedHom.ScalarTransportedInternalHom.hom`, the
  bifunctor whose
base-change morphism [stacks 0E1X] is the one [stacks 0A6A] proves invertible. Its value at a
bounded-below injective representative in the second variable is computed by the ordinary Hom
complex: `Dualizing.derivedInternalHomModelIso₂` is the two-variable form of
`Dualizing.derivedInternalHomModelIso`, which treats only the diagonal.

The derived localization functor is `StacksDraft.PseudoCoherence.localizationAwayFunctorAux`,
which is definitionally `(ModuleCat.extendScalars (algebraMap R R_g)).mapDerivedCategory`; the
exactness instances are rebuilt wherever it is used, as elsewhere in the pseudo-coherence
development, and the `IsLeftDerivedFunctor` certificate that [stacks 0E1X] asks for is
`Functor.isLeftDerivedFunctor_of_inverts` applied to `Functor.mapDerivedCategoryFactors`.

## References

* [Stacks Project, Tag 0A7H](https://stacks.math.columbia.edu/tag/0A7H)
* [Stacks Project, Tag 0A5T](https://stacks.math.columbia.edu/tag/0A5T)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

universe u v w

/-- Localizing a universe-lifted module agrees with localizing the module itself. -/
noncomputable def localizedModuleUliftIso {R : Type u} [CommRing R]
    (S : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M] :
    ModuleCat.of R (LocalizedModule S (ULift.{u} M)) ≅ ModuleCat.of R (LocalizedModule S M) :=
  ((IsLocalizedModule.mapEquiv S (LocalizedModule.mkLinearMap S (ULift.{u} M))
    (LocalizedModule.mkLinearMap S M) (Localization S)
    (ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M)).restrictScalars R).toModuleIso

section Models

variable {R : Type u} [CommRing R]

/-- Conjugation by isomorphisms in both variables identifies Hom complexes. -/
noncomputable def homComplexCongrIso₂
    {I₁ I₂ J₁ J₂ : CochainComplex (ModuleCat.{v} R) ℤ} (e₁ : I₁ ≅ J₁) (e₂ : I₂ ≅ J₂) :
    CochainComplex.HomComplexR R I₁ I₂ ≅ CochainComplex.HomComplexR R J₁ J₂ := by
  let p : CochainComplex.HomComplexR R I₁ I₂ ≅ CochainComplex.HomComplexR R J₁ I₂ :=
    { hom := Stacks.HomComplex.TensorHomMap.precomp R J₁ I₁ I₂ e₁.inv
      inv := Stacks.HomComplex.TensorHomMap.precomp R I₁ J₁ I₂ e₁.hom
      hom_inv_id := by simp [← Stacks.HomComplex.TensorHomMap.precomp_comp]
      inv_hom_id := by simp [← Stacks.HomComplex.TensorHomMap.precomp_comp] }
  let q : CochainComplex.HomComplexR R J₁ I₂ ≅ CochainComplex.HomComplexR R J₁ J₂ :=
    { hom := Stacks.HomComplex.TensorHomMap.postcomp R J₁ I₂ J₂ e₂.hom
      inv := Stacks.HomComplex.TensorHomMap.postcomp R J₁ J₂ I₂ e₂.inv
      hom_inv_id := by simp [← Stacks.HomComplex.TensorHomMap.postcomp_comp]
      inv_hom_id := by simp [← Stacks.HomComplex.TensorHomMap.postcomp_comp] }
  exact p ≪≫ q

/-- Restriction along a ring equivalence commutes with the Hom complex, in both variables. -/
noncomputable def homComplexRestrictScalarsIso₂
    {S : Type w} [CommRing S] (e : S ≃+* R) (I J : CochainComplex (ModuleCat.{v} R) ℤ) :
    (((ModuleCat.restrictScalars.{v} e.toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (CochainComplex.HomComplexR R I J)) ≅
      CochainComplex.HomComplexR S
        (((ModuleCat.restrictScalars.{v} e.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)
        (((ModuleCat.restrictScalars.{v} e.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J) := by
  let F := ModuleCat.restrictScalars.{v} e.toRingHom
  haveI : F.Additive := inferInstance
  apply HomologicalComplex.Hom.isoOfComponents
    (fun n => by
      let h := cochainAddEquivOfFullyFaithful F I J n
      let f : F.obj ((CochainComplex.HomComplexR R I J).X n) →ₗ[S] _ := {
        toFun := fun z => h z
        map_add' := h.map_add
        map_smul' := by
          intro s z
          apply CochainComplex.HomComplex.Cochain.ext
          intro p q hpq
          rfl }
      exact (LinearEquiv.ofBijective f h.bijective).toModuleIso)

/-- **Two-variable model for derived internal Hom.** A bounded-below complex of injectives
computes `RHom_R(X, -)` by the ordinary Hom complex, for an arbitrary first variable presented
by a cochain model. -/
noncomputable def derivedInternalHomModelIso₂
    {X : DerivedCategory (ModuleCat.{max u v} R)}
    (L : CochainComplex (ModuleCat.{max u v} R) ℤ) (eL : X ≅ DerivedCategory.Q.obj L)
    (I : CochainComplex (ModuleCat.{max u v} R) ℤ) (a : ℤ)
    (hGE : I.IsStrictlyGE a) (hInj : ∀ i, Injective (I.X i)) :
    (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, max u v} R).obj
        (Opposite.op X, DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (CochainComplex.HomComplexR R L I) := by
  let S := ULift.{max u v} R
  let e : S ≃+* R := ULift.ringEquiv
  let F := ModuleCat.restrictScalars.{max u v} e.toRingHom
  let G := ModuleCat.restrictScalars.{max u v} e.symm.toRingHom
  let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, max u v} R
  let J : CochainComplex (ModuleCat.{max u v} S) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  let LS : CochainComplex (ModuleCat.{max u v} S) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  haveI : J.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact Functor.map_isZero F ((CochainComplex.isStrictlyGE_iff I a).mp hGE i hi)
  haveI : ∀ i, Injective (J.X i) := by
    intro i
    change Injective (F.obj (I.X i))
    have : Injective (I.X i) := hInj i
    infer_instance
  haveI : J.IsKInjective := CochainComplex.isKInjective_of_injective J a
  let eJ : E.functor.obj (DerivedCategory.Q.obj I) ≅ DerivedCategory.Q.obj J :=
    F.mapDerivedCategoryFactors.app I
  let eLS : E.functor.obj X ≅ DerivedCategory.Q.obj LS :=
    E.functor.mapIso eL ≪≫ F.mapDerivedCategoryFactors.app L
  let eH := Stacks.DerivedHom.BaseChange.homModelIso LS J eLS eJ
  let eG := G.mapDerivedCategoryFactors.app (CochainComplex.HomComplexR S LS J)
  let eC := homComplexRestrictScalarsIso₂ e.symm LS J
  let eM := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let eI : I ≅ (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj J := eM.unitIso.app I
  let eL' : L ≅ (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj LS := eM.unitIso.app L
  exact E.inverse.mapIso eH ≪≫ eG ≪≫
    DerivedCategory.Q.mapIso eC ≪≫
    DerivedCategory.Q.mapIso (homComplexCongrIso₂ eL'.symm eI.symm)

/-- The degree-`n` cohomology module of `RHom_R(X, Y)` is the degree-`n` cohomology of the Hom
complex of the chosen models, when the model of `Y` is a bounded-below complex of injectives. -/
noncomputable def homologyDerivedInternalHomModelIso
    {X Y : DerivedCategory (ModuleCat.{max u v} R)}
    (L : CochainComplex (ModuleCat.{max u v} R) ℤ) (eL : X ≅ DerivedCategory.Q.obj L)
    (I : CochainComplex (ModuleCat.{max u v} R) ℤ) (a : ℤ)
    (hGE : I.IsStrictlyGE a) (hInj : ∀ i, Injective (I.X i))
    (eI : Y ≅ DerivedCategory.Q.obj I) (n : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).obj
      ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, max u v} R).obj (Opposite.op X, Y)))
        ≅
      (CochainComplex.HomComplexR R L I).homology n :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).mapIso
      ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, max u v} R).mapIso
          ((Iso.refl (Opposite.op X)).prod eI) ≪≫
        derivedInternalHomModelIso₂ L eL I a hGE hInj) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) n).app
      (CochainComplex.HomComplexR R L I)

/-- **Stacks 0A64 for the derived internal Hom bifunctor.** The degree-`n` cohomology module of
`RHom_R(X, Y)` is the group of morphisms `X ⟶ Y⟦n⟧` in the derived category, whenever `Y` is
represented by a bounded-below complex of injectives. -/
noncomputable def extAddEquivHomologyDerivedInternalHom
    {X Y : DerivedCategory (ModuleCat.{max u v} R)}
    (L : CochainComplex (ModuleCat.{max u v} R) ℤ) (eL : X ≅ DerivedCategory.Q.obj L)
    (I : CochainComplex (ModuleCat.{max u v} R) ℤ) (a : ℤ)
    (hGE : I.IsStrictlyGE a) (hInj : ∀ i, Injective (I.X i))
    (eI : Y ≅ DerivedCategory.Q.obj I) (n : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).obj
      ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, max u v} R).obj (Opposite.op X, Y)))
        ≃+
      (X ⟶ Y⟦n⟧) := by
  haveI : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  let H := CochainComplex.HomComplexR R L I
  let eMod := homologyDerivedInternalHomModelIso L eL I a hGE hInj eI n
  let V := forget₂ (ModuleCat.{max u v} R) AddCommGrpCat
  let eV : (H.homology n) ≃+ (L.HomComplex I).homology n :=
    ((H.sc n).mapHomologyIso V).symm.addCommGroupIsoToAddEquiv
  let eClass := (CochainComplex.HomComplex.homologyAddEquiv L I n).trans
    (cohomologyClassRHomAddEquivOfIsKInjective L I n)
  let eShift := (shiftFunctor (DerivedCategory (ModuleCat.{max u v} R)) n).mapIso eI
  let q := HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)
  let η := DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} R)
  let eSrc : DerivedCategory.Qh.obj (q.obj L) ≅ X := η.app L ≪≫ eL.symm
  let eTgt : DerivedCategory.Qh.obj (q.obj (I⟦n⟧)) ≅ Y⟦n⟧ :=
    η.app (I⟦n⟧) ≪≫ (DerivedCategory.Q.commShiftIso n).app I ≪≫ eShift.symm
  let g : (DerivedCategory.Qh.obj (q.obj L) ⟶ DerivedCategory.Qh.obj (q.obj (I⟦n⟧))) →+
      (X ⟶ Y⟦n⟧) := {
    toFun := fun x => eSrc.inv ≫ x ≫ eTgt.hom
    map_zero' := by simp
    map_add' := fun x y => by simp }
  let eFin : (DerivedCategory.Qh.obj (q.obj L) ⟶ DerivedCategory.Qh.obj (q.obj (I⟦n⟧))) ≃+
      (X ⟶ Y⟦n⟧) :=
    AddEquiv.ofBijective g (Iso.homCongr eSrc eTgt).bijective
  exact (eMod.toLinearEquiv.toAddEquiv.trans eV).trans (eClass.trans eFin)

end Models

section BaseChange

open StacksDraft.PseudoCoherence

variable {A : Type u} [CommRing A]

/-- **Stacks 0A6A for a principal localization.** Derived Hom out of a pseudo-coherent object
into a bounded-below object commutes with the flat base change `A → A_g`. -/
noncomputable def localizationAwayDerivedInternalHomIso (g : A)
    (X Y : DerivedCategory (ModuleCat.{u} A)) (hX : IsPseudoCoherent X) (b : ℤ)
    (hY : DerivedCategory.IsGE Y b) :
    (localizationAwayFunctorAux.{u, u} g).obj
        ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A).obj (Opposite.op X, Y)) ≅
      (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} (Localization.Away g)).obj
        (Opposite.op ((localizationAwayFunctorAux.{u, u} g).obj X),
          (localizationAwayFunctorAux.{u, u} g).obj Y) := by
  let B := Localization.Away g
  let fm : A →+* B := algebraMap A B
  have hflat : fm.Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B (Submonoid.powers g))
  let Fm := ModuleCat.extendScalars.{u, u, u} fm
  have : Fm.Additive := extendScalars_additive.{u, u} _
  have : PreservesFiniteLimits Fm :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _ hflat
  have : PreservesColimitsOfSize.{0, 0} Fm :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} fm).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits Fm := PreservesColimitsOfSize.preservesFiniteColimits Fm
  let F := Fm.mapDerivedCategory
  let α := Fm.mapDerivedCategoryFactors.hom
  have : F.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ Fm.mapDerivedCategoryFactors
  have : (ModuleCat.extendScalars.{u, u, u} fm).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} fm).isLeftAdjoint
  have : (ModuleCat.restrictScalars.{u, u, u} fm).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} fm).isRightAdjoint
  have : (ModuleCat.restrictScalars.{u, u, u} fm).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} fm).isLeftAdjoint
  exact @asIso _ _ _ _ (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, u} fm F α X
    Y) (Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange.{u, u, u} fm F α X Y
      (Or.inr (Or.inr (Or.inl ⟨hflat, hX, ⟨b, hY⟩⟩))))

/-- Vanishing of a cohomology module of derived Hom out of a pseudo-coherent object into a
bounded-below object is local on a standard open cover. -/
theorem isZero_homology_derivedInternalHom_of_localizations
    {ι : Type w} (f : ι → A) (hspan : Ideal.span (Set.range f) = ⊤)
    (X Y : DerivedCategory (ModuleCat.{u} A)) (hX : IsPseudoCoherent X) (b : ℤ)
    (hY : DerivedCategory.IsGE Y b) (n : ℤ)
    (h : ∀ i, IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (Localization.Away (f i))) n).obj
      ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} (Localization.Away (f i))).obj
        (Opposite.op ((localizationAwayFunctorAux.{u, u} (f i)).obj X),
          (localizationAwayFunctorAux.{u, u} (f i)).obj Y)))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A).obj (Opposite.op X, Y))) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine Module.subsingleton_of_localizationSpan_range f hspan fun i => ?_
  have hi : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Localization.Away (f i))) n).obj
    ((localizationAwayFunctorAux.{u, u} (f i)).obj
      ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A).obj (Opposite.op X, Y)))) :=
    (h i).of_iso ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Localization.Away (f i))) n).mapIso
        (localizationAwayDerivedInternalHomIso (f i) X Y hX b hY))
  exact ModuleCat.isZero_iff_subsingleton.mp
    (hi.of_iso (localizationAwayHomologyIso.{u, u} (f i) _ n).symm)

end BaseChange

section InjectiveDimension

open StacksDraft.PseudoCoherence StacksDraft.InjectiveDimension

/-- A bounded-below object of a derived category with enough injectives is represented by a
complex of injectives supported in the same degrees. -/
theorem exists_boundedBelow_injective_representative {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] [EnoughInjectives C] (K : DerivedCategory C) (a : ℤ)
    [K.IsGE a] :
    ∃ (I : CochainComplex C ℤ) (_ : I.IsStrictlyGE a),
      (∀ n, Injective (I.X n)) ∧ Nonempty (K ≅ DerivedCategory.Q.obj I) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K a
  obtain ⟨I, hI, φ, hφ⟩ := CochainComplex.Plus.exists_quasiIso_injective ⟨L, a, hL⟩ a
  have : QuasiIso φ.hom := hφ
  have hiso : IsIso (DerivedCategory.Q.map φ.hom) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := φ.hom)).mpr inferInstance
  exact ⟨((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj I.obj, inferInstance,
    fun n => inferInstanceAs (Injective ((InjectiveObject.ι C).obj (I.obj.X n))),
    ⟨e ≪≫ @asIso _ _ _ _ (DerivedCategory.Q.map φ.hom) hiso⟩⟩

variable {A : Type u} [CommRing A]

/-- The single complex on a finite module over a Noetherian ring is pseudo-coherent. -/
theorem isPseudoCoherent_singleFunctor_obj [IsNoetherianRing A] (N : ModuleCat.{u} A)
    [Module.Finite A N] :
    IsPseudoCoherent ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) := by
  let S := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N
  have hfin : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj S) := by
    intro i
    by_cases h : i = 0
    · subst h
      have : Module.Finite A ((𝟭 (ModuleCat.{u} A)).obj N) := inferInstanceAs (Module.Finite A N)
      exact Module.Finite.equiv
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (C := ModuleCat.{u} A) 0).app N).toLinearEquiv.symm
    · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj S) := by
        rcases lt_or_gt_of_ne h with hi | hi
        · exact DerivedCategory.isZero_of_isGE S 0 i hi
        · exact DerivedCategory.isZero_of_isLE S 0 i hi
      rw [ModuleCat.isZero_iff_subsingleton] at hz
      have : Finite ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj S) :=
        Finite.of_subsingleton
      exact Module.Finite.of_finite
  exact (pseudoCoherent_iff_boundedAbove_finite_homology S 0 A).2.1.mpr
    ⟨⟨0, fun i hi => DerivedCategory.isZero_of_isLE S 0 i hi⟩, hfin⟩

/-- `Ext` out of a single complex, read on the derived localization. If the derived localization
of `Y` away from `g` has injective amplitude in `[c, d]`, then for `i` outside `[c, d]` the
degree-`i` cohomology of `RHom_{A_g}(N_g, Y_g)` vanishes, for every `A`-module `N`. -/
theorem isZero_homology_derivedInternalHom_localizationAway_single
    (g : A) (N : ModuleCat.{u} A) (Y : DerivedCategory (ModuleCat.{u} A)) (c d : ℤ)
    (hamp : HasInjectiveAmplitude ((localizationAwayFunctorAux.{u, u} g).obj Y) c d)
    (i : ℤ) (hi : i < c ∨ d < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization.Away g)) i).obj
      ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} (Localization.Away g)).obj
        (Opposite.op ((localizationAwayFunctorAux.{u, u} g).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)),
          (localizationAwayFunctorAux.{u, u} g).obj Y))) := by
  let B := Localization.Away g
  let fm : A →+* B := algebraMap A B
  have hflat : fm.Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B (Submonoid.powers g))
  let Fm := ModuleCat.extendScalars.{u, u, u} fm
  have : Fm.Additive := extendScalars_additive.{u, u} _
  have : PreservesFiniteLimits Fm :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _ hflat
  have : PreservesColimitsOfSize.{0, 0} Fm :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} fm).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits Fm := PreservesColimitsOfSize.preservesFiniteColimits Fm
  -- the localization of the single complex is the single complex on the localized module
  let eSingle : (localizationAwayFunctorAux.{u, u} g).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (Fm.obj N) :=
    (Fm.mapDerivedCategorySingleFunctor 0).app N
  -- a bounded-below injective representative of the localization of `Y`
  obtain ⟨I, hIGE, hILE, hIinj, ⟨eI⟩⟩ := hamp
  -- `Ext` out of a single complex vanishes outside the injective amplitude
  have hExt : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (Fm.obj N))
      ((localizationAwayFunctorAux.{u, u} g).obj Y) i) :=
    (hasInjectiveAmplitude_iff_ext_vanishing_iff_quotient_vanishing
      ((localizationAwayFunctorAux.{u, u} g).obj Y) c d).1.1
        ⟨I, hIGE, hILE, hIinj, ⟨eI⟩⟩ (Fm.obj N) i hi
  have hSrc : Subsingleton ((localizationAwayFunctorAux.{u, u} g).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ⟶
      ((localizationAwayFunctorAux.{u, u} g).obj Y)⟦i⟧) :=
    Equiv.subsingleton (Iso.homCongr eSingle (Iso.refl _))
  rw [ModuleCat.isZero_iff_subsingleton]
  exact Equiv.subsingleton (AddEquiv.toEquiv
    (extAddEquivHomologyDerivedInternalHom
      ((CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (Fm.obj N))
      (eSingle ≪≫ (DerivedCategory.singleFunctorIsoCompQ (C := ModuleCat.{u} B) 0).app (Fm.obj N))
      I c hIGE hIinj eI i))

/-- **Condition (1) of [stacks 0A7B] glues**, the first half of [stacks 0A7H]. If the derived
localization of `K` at every member of a family generating the unit ideal is a dualizing complex,
then `K` has finite injective dimension. -/
theorem hasFiniteInjectiveDimension_of_localizations [IsNoetherianRing A]
    {ι : Type w} (f : ι → A) (hspan : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ i, IsDualizingComplex ((localizationAwayFunctorAux.{u, u} (f i)).obj K)) :
    HasFiniteInjectiveDimension K := by
  classical
  obtain ⟨s, hsfin, hspan'⟩ := exists_finite_index_set_span_eq_top f hspan
  have : Finite s := hsfin
  choose a b hab using fun j : s => (hK j.1).finiteInjectiveDimension
  obtain ⟨b', hb'⟩ := Finite.bddAbove_range b
  obtain ⟨c, -, hGE, -⟩ := isGE_and_isLE_of_localizations f hspan K hK
  obtain ⟨I, hIGE, hIinj, ⟨eK⟩⟩ := exists_boundedBelow_injective_representative K c
  refine ⟨c, b', ?_⟩
  apply (hasInjectiveAmplitude_iff_ext_vanishing_iff_quotient_vanishing K c b').1.2
  apply (hasInjectiveAmplitude_iff_ext_vanishing_iff_quotient_vanishing K c b').2.2
  intro J i hi
  let N : ModuleCat.{u} A := ModuleCat.of A (Shrink.{u} (A ⧸ J))
  let X := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N
  rcases hi with hi | hi
  · -- below the lower bound, vanishing is the t-structure argument
    have : X.IsLE 0 := by
      dsimp [X]
      infer_instance
    have : (K⟦i⟧).IsGE (c - i) :=
      DerivedCategory.TStructure.t.isGE_shift K c i (c - i) (by omega)
    exact subsingleton_of_forall_eq 0 (fun φ ↦
      DerivedCategory.TStructure.t.zero φ 0 (c - i) (by omega))
  · -- above the common upper bound of the local amplitudes, vanishing is local
    have hNfin : Module.Finite A N :=
      Module.Finite.equiv (Shrink.linearEquiv A (A ⧸ J)).symm
    have hXpc : IsPseudoCoherent X := isPseudoCoherent_singleFunctor_obj N
    have hzero : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A).obj (Opposite.op X, K))) :=
      isZero_homology_derivedInternalHom_of_localizations (fun j : s => f j.1) hspan' X K hXpc c
        hGE i fun j => isZero_homology_derivedInternalHom_localizationAway_single (f j.1) N K
          (a j) (b j) (hab j) i (Or.inr ((hb' ⟨j, rfl⟩).trans_lt hi))
    rw [ModuleCat.isZero_iff_subsingleton] at hzero
    exact Equiv.subsingleton (AddEquiv.toEquiv
      (extAddEquivHomologyDerivedInternalHom
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N)
        ((DerivedCategory.singleFunctorIsoCompQ (C := ModuleCat.{u} A) 0).app N)
        I c hIGE hIinj eK i).symm)

/-- If the homothety of a representative is a quasi-isomorphism, its endomorphism complex has
no cohomology away from degree zero. -/
theorem isZero_homology_homComplexR_of_quasiIso_homothety {R : Type u} [CommRing R]
    (J : CochainComplex (ModuleCat.{max u v} R) ℤ) (h : QuasiIso (homothety J)) (n : ℤ)
    (hn : n ≠ 0) :
    IsZero ((CochainComplex.HomComplexR R J J).homology n) := by
  let V := forget₂ (ModuleCat.{max u v} R) AddCommGrpCat
  let H := CochainComplex.HomComplexR R J J
  let eLift : (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj H ≅
      liftedEndomorphismComplex J :=
    HomologicalComplex.Hom.isoOfComponents
      (fun k => (AddEquiv.ulift.symm :
        CochainComplex.HomComplex.Cochain J J k ≃+
          ULift.{u} (CochainComplex.HomComplex.Cochain J J k)).toAddCommGrpIso)
  have hsrc : IsZero (((CochainComplex.singleFunctor AddCommGrpCat.{max u v} 0).obj
      (AddCommGrpCat.of (ULift.{max u v} R))).homology n) :=
    HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0
      (AddCommGrpCat.of (ULift.{max u v} R)) n hn
  have hiso : IsIso (HomologicalComplex.homologyMap (homothety J) n) :=
    (quasiIsoAt_iff_isIso_homologyMap (homothety J) n).mp (h.quasiIsoAt n)
  have htgt : IsZero ((liftedEndomorphismComplex J).homology n) :=
    hsrc.of_iso (@asIso _ _ _ _ _ hiso).symm
  have hV : IsZero (((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj H).homology n) :=
    htgt.of_iso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v}
      (ComplexShape.up ℤ) n).mapIso eLift)
  let eV : (H.homology n) ≃+ (J.HomComplex J).homology n :=
    ((H.sc n).mapHomologyIso V).symm.addCommGroupIsoToAddEquiv
  rw [ModuleCat.isZero_iff_subsingleton]
  have hsub : Subsingleton ((J.HomComplex J).homology n) := by
    constructor
    intro x y
    have h0 := hV.eq_of_src (𝟙 _) 0
    have hxy := congrArg (fun φ => φ.hom (x - y)) h0
    change x - y = 0 at hxy
    exact sub_eq_zero.mp hxy
  exact Equiv.subsingleton eV.toEquiv

/-- **The off-diagonal half of condition (3) glues.** If the derived localization of `K` at every
member of a family generating the unit ideal is a dualizing complex, then the endomorphism complex
of any bounded-below injective representative of `K` has no cohomology away from degree zero. -/
theorem isZero_homology_homComplexR_of_localizations [IsNoetherianRing A]
    {ι : Type w} (f : ι → A) (hspan : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ i, IsDualizingComplex ((localizationAwayFunctorAux.{u, u} (f i)).obj K))
    (J : CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ) (hJGE : J.IsStrictlyGE a)
    (hJinj : ∀ i, Injective (J.X i)) (eJ : K ≅ DerivedCategory.Q.obj J) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((CochainComplex.HomComplexR A J J).homology n) := by
  have hpc : IsPseudoCoherent K := isPseudoCoherent_of_localizations f hspan K hK
  obtain ⟨c, -, hGE, -⟩ := isGE_and_isLE_of_localizations f hspan K hK
  have hzero : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A).obj (Opposite.op K, K))) := by
    refine isZero_homology_derivedInternalHom_of_localizations f hspan K K hpc c hGE n
      fun i => ?_
    obtain ⟨p, q, I, hIGE, hILE, hIinj, ⟨eI⟩⟩ := (hK i).finiteInjectiveDimension
    exact (isZero_homology_homComplexR_of_quasiIso_homothety I
      ((hK i).homothetyQuasiIso I ⟨eI.symm⟩ hIinj ⟨p, q, hIGE, hILE⟩) n hn).of_iso
        (homologyDerivedInternalHomModelIso I eI I p hIGE hIinj eI n)
  exact hzero.of_iso (homologyDerivedInternalHomModelIso J eJ J a hJGE hJinj eJ n).symm

/-- The two conditions of [stacks 0A7B] that are controlled by the cohomology modules of `K` —
finite injective dimension and finiteness of the cohomology — glue along a standard open cover.
The homothety condition is a hypothesis here; it is discharged in
`Dualizing.isDualizingComplex_of_localizations`. -/
theorem isDualizingComplex_of_localizations_of_homothetyQuasiIso [IsNoetherianRing A]
    {ι : Type w} (f : ι → A) (hspan : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ i, IsDualizingComplex ((localizationAwayFunctorAux.{u, u} (f i)).obj K))
    (homothetyQuasiIso : IsDerivedHomothetyQuasiIso K) :
    IsDualizingComplex K :=
  ⟨hasFiniteInjectiveDimension_of_localizations f hspan K hK,
    finite_homology_of_localizations f hspan K hK, homothetyQuasiIso⟩

/-- [stacks 0A7H] reduced to a rank-one statement. Given, for each bounded injective
representative `J` of `K`, *any* `A`-linear equivalence `H⁰(Hom^•_A(J, J)) ≃ₗ[A] A` — no
compatibility with the homothety is required, by `Dualizing.homothety_quasiIso_of_rankOne` — the
complex `K` is dualizing. The remaining degrees are handled by
`Dualizing.isZero_homology_homComplexR_of_localizations`. -/
theorem isDualizingComplex_of_localizations_of_rankOne [IsNoetherianRing A]
    {ι : Type w} (f : ι → A) (hspan : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ i, IsDualizingComplex ((localizationAwayFunctorAux.{u, u} (f i)).obj K))
    (hrank : ∀ (J : CochainComplex (ModuleCat.{u} A) ℤ),
      Nonempty (DerivedCategory.Q.obj J ≅ K) → (∀ i, Injective (J.X i)) →
      (∃ a b : ℤ, J.IsStrictlyGE a ∧ J.IsStrictlyLE b) →
      Nonempty ((CochainComplex.HomComplexR A J J).homology 0 ≃ₗ[A] A)) :
    IsDualizingComplex K := by
  refine isDualizingComplex_of_localizations_of_homothetyQuasiIso f hspan K hK ?_
  intro J hJ hJinj hJbound
  obtain ⟨e⟩ := hrank J hJ hJinj hJbound
  obtain ⟨a, -, hJGE, -⟩ := hJbound
  have : J.IsKInjective := CochainComplex.isKInjective_of_injective J a
  exact quasiIso_homothety_of_rankOne J e fun n hn =>
    isZero_homology_homComplexR_of_localizations f hspan K hK J a hJGE hJinj
      (Classical.choice hJ).symm n hn

end InjectiveDimension

section Homothety

open StacksDraft.PseudoCoherence StacksDraft.InjectiveDimension TensorProduct

/-- An algebra that is free of rank one as a module is its own base ring: if the algebra map
becomes bijective after localizing at every member of a family generating the unit ideal, it is
bijective. The local hypothesis asks only for *some* linear equivalence `A_g ≃ₗ A_g ⊗_A E`, with
no compatibility with the algebra map; unitality supplies the rest. -/
theorem bijective_algebraMap_of_localizations {A : Type u} [CommRing A] {E : Type v} [Ring E]
    [Algebra A E] {ι : Type w} (f : ι → A) (hspan : Ideal.span (Set.range f) = ⊤)
    (h : ∀ i, Nonempty (Localization.Away (f i) ≃ₗ[Localization.Away (f i)]
      TensorProduct A (Localization.Away (f i)) E)) :
    Function.Bijective (algebraMap A E) := by
  have hb : Function.Bijective (Algebra.linearMap A E) := by
    refine bijective_of_isLocalized_span (Set.range f) hspan
      (fun r : Set.range f => Localization.Away r.1) (fun _ => Algebra.linearMap A _)
      (fun r : Set.range f => TensorProduct A (Localization.Away r.1) E)
      (fun r => TensorProduct.mk A (Localization.Away r.1) E 1)
      (Algebra.linearMap A E) ?_
    intro r
    obtain ⟨i, hi⟩ := r.2
    obtain ⟨e⟩ := hi ▸ h i
    have hmap : (IsLocalizedModule.map (Submonoid.powers (r : A))
        (Algebra.linearMap A (Localization.Away (r : A)))
        ((TensorProduct.mk A (Localization.Away (r : A)) E) 1)) (Algebra.linearMap A E) =
        (Algebra.linearMap (Localization.Away (r : A))
          (TensorProduct A (Localization.Away (r : A)) E)).restrictScalars A := by
      apply IsLocalizedModule.linearMap_ext (Submonoid.powers (r : A))
        (Algebra.linearMap A (Localization.Away (r : A)))
        ((TensorProduct.mk A (Localization.Away (r : A)) E) 1)
      refine LinearMap.ext fun a => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
      rw [IsLocalizedModule.map_apply]
      simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]
    rw [hmap]
    exact bijective_algebraMap_of_linearEquiv e
  exact hb

/-- If the homothety of a bounded injective representative is a quasi-isomorphism, the zeroth
cohomology of its endomorphism complex is free of rank one: it is linearly isomorphic to the base
ring. -/
theorem linearEquiv_homology_homComplexR_of_quasiIso_homothety {R : Type u} [CommRing R]
    (I : CochainComplex (ModuleCat.{u} R) ℤ) (h : QuasiIso (homothety I)) :
    Nonempty ((CochainComplex.HomComplexR R I I).homology 0 ≃ₗ[R] R) := by
  have hq : QuasiIso (liftedModuleHomothety.{u, u} I) := quasiIso_liftedModuleHomothety I h
  have hiso : IsIso (HomologicalComplex.homologyMap (liftedModuleHomothety.{u, u} I) 0) :=
    (quasiIsoAt_iff_isIso_homologyMap _ 0).mp (hq.quasiIsoAt 0)
  let U := ModuleCat.uliftFunctor.{u, u} R
  let H := CochainComplex.HomComplexR R I I
  let e1 := HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
    (ModuleCat.of R (ULift.{u} R))
  let e2 := (mapHomologicalComplexCompHomologyFunctorIso U 0).app H
  let e3 : ModuleCat.of R (ULift.{u} R) ≅ U.obj (H.homology 0) :=
    e1.symm ≪≫
      @asIso _ _ _ _ (HomologicalComplex.homologyMap (liftedModuleHomothety.{u, u} I) 0) hiso
        ≪≫ e2
  exact ⟨((ULift.moduleEquiv (R := R) (M := R)).symm.trans
    (e3.toLinearEquiv.trans ULift.moduleEquiv)).symm⟩

variable {A : Type u} [CommRing A]

/-- **Stacks Project, Tag 0A7H.** A complex over a Noetherian ring is dualizing as soon as its
derived localization at every member of a family of elements generating the unit ideal is a
dualizing complex over the corresponding localization. -/
@[stacks 0A7H]
theorem isDualizingComplex_of_localizations [IsNoetherianRing A]
    {ι : Type w} (f : ι → A) (K : DerivedCategory (ModuleCat.{u} A))
    (hspan : Ideal.span (Set.range f) = ⊤)
    (hK : ∀ i, IsDualizingComplex ((localizationAwayFunctorAux.{u, u} (f i)).obj K)) :
    IsDualizingComplex K := by
  refine isDualizingComplex_of_localizations_of_rankOne f hspan K hK ?_
  rintro J hJ hJinj ⟨a, -, hJGE, -⟩
  have hpc : IsPseudoCoherent K := isPseudoCoherent_of_localizations f hspan K hK
  obtain ⟨c, -, hGE, -⟩ := isGE_and_isLE_of_localizations f hspan K hK
  have : J.IsKInjective := CochainComplex.isKInjective_of_injective J a
  let eJ : K ≅ DerivedCategory.Q.obj J := (Classical.choice hJ).symm
  let Z := (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A).obj (Opposite.op K, K)
  let eEZ : End (DerivedCategory.Q.obj J) ≃ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj Z) :=
    (homologyZeroEndLinearEquiv J).symm.trans
      (homologyDerivedInternalHomModelIso J eJ J a hJGE hJinj eJ 0).symm.toLinearEquiv
  have hbij : Function.Bijective (algebraMap A (End (DerivedCategory.Q.obj J))) := by
    refine bijective_algebraMap_of_localizations (A := A)
      (E := End (DerivedCategory.Q.obj J)) f hspan fun i => ?_
    obtain ⟨p, q, I, hIGE, hILE, hIinj, ⟨eI⟩⟩ := (hK i).finiteInjectiveDimension
    obtain ⟨eB⟩ := linearEquiv_homology_homComplexR_of_quasiIso_homothety I
      ((hK i).homothetyQuasiIso I ⟨eI.symm⟩ hIinj ⟨p, q, hIGE, hILE⟩)
    exact ⟨((TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl (Localization.Away (f i)) (Localization.Away (f i))) eEZ) ≪≫ₗ
      (IsLocalizedModule.isBaseChange (Submonoid.powers (f i)) (Localization.Away (f i))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i))
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj Z))).equiv ≪≫ₗ
      (localizationAwayHomologyIso.{u, u} (f i) Z 0).symm.toLinearEquiv ≪≫ₗ
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization.Away (f i))) 0).mapIso
        (localizationAwayDerivedInternalHomIso (f i) K K hpc c hGE)).toLinearEquiv ≪≫ₗ
      (homologyDerivedInternalHomModelIso I eI I p hIGE hIinj eI 0).toLinearEquiv ≪≫ₗ
      eB).symm⟩
  exact ⟨(homologyZeroEndLinearEquiv J).trans
    (LinearEquiv.ofBijective (Algebra.linearMap A (End (DerivedCategory.Q.obj J)))
      hbij).symm⟩

end Homothety

end Dualizing

end
