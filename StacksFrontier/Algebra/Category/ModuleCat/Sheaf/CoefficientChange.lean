module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence

/-!
# Changing the sheaf of rings of a sheaf of modules along a family of ring isomorphisms

Let `R` and `S` be two sheaves of rings on one site, with sections in possibly different
universes, and let `e U : S(U) ≃+* R(U)` be a family of ring isomorphisms compatible with the
restriction maps.  Restriction of scalars along `e` turns sheaves of `R`-modules into sheaves of
`S`-modules without changing the underlying abelian sheaves, and is an equivalence of
categories.  This file records that equivalence and proves that it carries quasi-coherence
(Stacks 03DL (6)).

The point is the universe of the rings: Mathlib's restriction of scalars of sheaves of modules
asks for a morphism of sheaves of rings, hence for two sheaves valued in one category
`RingCat.{r}`, while the structure sheaf of the small étale site of an algebraic space and the
structure sheaf of its spaces-étale site, read on the small étale site, have their sections one
universe apart.

## Main definitions

* `Stacks.SheafOfModules.CoefficientChange.restrictCoefficients`: restriction of coefficients
  along a compatible family of ring maps.
* `Stacks.SheafOfModules.CoefficientChange.coefficientEquivalence`: along a compatible family of
  ring isomorphisms it is an equivalence.

## Main results

* `Stacks.SheafOfModules.CoefficientChange.hasGlobalPresentation_of_map`: a global presentation
  is carried along a colimit-preserving functor between categories of sheaves of modules over
  rings in different universes, provided the lifted structure sheaves correspond.
* `Stacks.SheafOfModules.CoefficientChange.isQuasicoherentOnSite_restrictCoefficients`:
  **restriction of coefficients along a compatible family of ring isomorphisms carries
  quasi-coherence.**

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c h r s m

namespace Stacks.SheafOfModules.CoefficientChange

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}

/-- Restriction of the coefficients of sheaves of modules along a family of ring maps
`φ U : S(U) →+* R(U)` compatible with restriction, the two sheaves of rings having their sections
in possibly different universes. -/
def restrictCoefficients (R : Sheaf J RingCat.{r}) (S : Sheaf J RingCat.{s})
    (φ : ∀ U, S.obj.obj U →+* R.obj.obj U)
    (hφ : ∀ {U V} (f : U ⟶ V) (a : S.obj.obj U),
      φ V (S.obj.map f a) = R.obj.map f (φ U a)) :
    SheafOfModules.{m} R ⥤ SheafOfModules.{m} S where
  obj M := {
    val := {
      obj U := (ModuleCat.restrictScalars (φ U)).obj (M.val.obj U)
      map {U V} f := ModuleCat.ofHom
        (X := (ModuleCat.restrictScalars (φ U)).obj (M.val.obj U))
        (Y := (ModuleCat.restrictScalars (S.obj.map f).hom).obj
          ((ModuleCat.restrictScalars (φ V)).obj (M.val.obj V))) {
        toFun := M.val.map f
        map_add' := map_add _
        map_smul' a x :=
          (M.val.map_smul f (φ U a) x).trans (congrArg (· • M.val.map f x) (hφ f a).symm) }
      map_id U := by
        ext x
        exact (congrArg (fun φ => (ConcreteCategory.hom φ) x) (M.val.map_id U)).trans rfl
      map_comp f g := by
        ext x
        exact M.val.map_comp_apply f g x }
    isSheaf := M.isSheaf }
  map f := { val := {
    app U := (ModuleCat.restrictScalars (φ U)).map (f.val.app U)
    naturality g := by
      ext x
      exact congrArg (fun φ => φ x) (congrArg (fun ψ => (ConcreteCategory.hom ψ : _ → _))
        (f.val.naturality g)) } }

/-- Restriction of coefficients along a compatible family of ring isomorphisms is an equivalence
of categories of sheaves of modules. -/
def coefficientEquivalence (R : Sheaf J RingCat.{r}) (S : Sheaf J RingCat.{s})
    (e : ∀ U, S.obj.obj U ≃+* R.obj.obj U)
    (he : ∀ {U V} (f : U ⟶ V) (a : S.obj.obj U),
      e V (S.obj.map f a) = R.obj.map f (e U a)) :
    SheafOfModules.{m} R ≌ SheafOfModules.{m} S := by
  let F := restrictCoefficients.{c, h, r, s, m} R S (fun U => (e U).toRingHom) he
  have he' {U V} (f : U ⟶ V) (a : R.obj.obj U) :
      (e V).symm (R.obj.map f a) = S.obj.map f ((e U).symm a) := by
    apply (e V).injective
    simp only [RingEquiv.apply_symm_apply, he]
  let G := restrictCoefficients.{c, h, s, r, m} S R (fun U => (e U).symm.toRingHom) he'
  let η (M : SheafOfModules.{m} R) : M ≅ G.obj (F.obj M) :=
    (SheafOfModules.fullyFaithfulForget R).preimageIso <| PresheafOfModules.isoMk
      (fun U => (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (e U)).unitIso.app
        (M.val.obj U)) (fun _ _ _ => by ext; rfl)
  let ε (M : SheafOfModules.{m} S) : F.obj (G.obj M) ≅ M :=
    (SheafOfModules.fullyFaithfulForget S).preimageIso <| PresheafOfModules.isoMk
      (fun U => (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (e U)).counitIso.app
        (M.val.obj U)) (fun _ _ _ => by ext; rfl)
  exact {
    functor := F
    inverse := G
    unitIso := NatIso.ofComponents η fun _ => by ext; rfl
    counitIso := NatIso.ofComponents ε fun _ => by ext; rfl }

/-- The functor of `coefficientEquivalence` is restriction of coefficients. -/
theorem coefficientEquivalence_functor (R : Sheaf J RingCat.{r}) (S : Sheaf J RingCat.{s})
    (e : ∀ U, S.obj.obj U ≃+* R.obj.obj U)
    (he : ∀ {U V} (f : U ⟶ V) (a : S.obj.obj U),
      e V (S.obj.map f a) = R.obj.map f (e U a)) :
    (coefficientEquivalence.{c, h, r, s, m} R S e he).functor =
      restrictCoefficients R S (fun U => (e U).toRingHom) he := rfl

/-! ### Global presentations across a change of coefficients -/

section Presentation

universe w v

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}

/-- **A global presentation is carried along a functor between categories of sheaves of modules
over two sheaves of rings in possibly different universes**, provided the functor preserves
colimits and zero morphisms and matches the universe-lifted structure sheaves.  The module
universe `max r s m` is chosen so that a global presentation on either side lives in the one
universe `max w v r s m`. -/
theorem hasGlobalPresentation_of_map {R : Sheaf J RingCat.{r}} {S : Sheaf J RingCat.{s}}
    (M : SheafOfModules.{max r s m} R) (N : SheafOfModules.{max r s m} S)
    (Φ : SheafOfModules.{max w v r s m} R ⥤ SheafOfModules.{max w v r s m} S)
    [PreservesColimitsOfSize.{max w v r s m, max w v r s m} Φ] [Φ.PreservesZeroMorphisms]
    (η₁ : Φ.obj (SheafOfModules.uliftForPresentation.{w, v, r, r, max w v r s m}
      (SheafOfModules.unit R)) ≅
      SheafOfModules.uliftForPresentation.{w, v, s, s, max w v r s m} (SheafOfModules.unit S))
    (ηM : Φ.obj (SheafOfModules.uliftForPresentation.{w, v, r, max r s m, max w v r} M) ≅
      SheafOfModules.uliftForPresentation.{w, v, s, max r s m, max w v s} N)
    (hM : M.HasGlobalPresentation) : N.HasGlobalPresentation := by
  classical
  have : PreservesColimitsOfSize.{0, 0} Φ := preservesColimitsOfSize_shrink Φ
  obtain ⟨I, K, P, Q, ι, κ, hP, hQ, a, b, hab, hc⟩ := hM
  have hcofan {T : Type _} {X : SheafOfModules.{max w v r s m} R}
      (π : T → (SheafOfModules.uliftForPresentation.{w, v, r, r, max w v r s m}
        (SheafOfModules.unit R) ⟶ X))
      (h : IsColimit (Cofan.mk X π)) :
      IsColimit (Cofan.mk (Φ.obj X) (fun i => η₁.inv ≫ Φ.map (π i))) :=
    isColimitCofan_precomposeIso η₁.symm _
      ((Cofan.isColimitMapCoconeEquiv Φ _ (Cofan.mk X π)).toFun (isColimitOfPreserves Φ h))
  let b' := Φ.map b ≫ ηM.hom
  have hab' : Φ.map a ≫ b' = 0 := by
    simp only [b', ← Category.assoc, ← Φ.map_comp, hab, Functor.map_zero, zero_comp]
  let d := (parallelPair a 0) ⋙ Φ
  let i₁ : d ≅ parallelPair (Φ.map a) (Φ.map 0) := by
    refine NatIso.ofComponents (fun j => ?_) ?_
    · cases j <;> exact Iso.refl _
    rintro _ _ (_ | _ | _) <;> simp [d]
  let i₂ : parallelPair (Φ.map a) (Φ.map 0) ≅ parallelPair (Φ.map a) 0 :=
    parallelPairIsoMk (Iso.refl (Φ.obj Q)) (Iso.refl (Φ.obj P))
  let c' := CokernelCofork.ofπ b' hab'
  have hc' : IsColimit c' :=
    (IsColimit.equivOfNatIsoOfIso (i₁ ≪≫ i₂)
      (Φ.mapCocone (CokernelCofork.ofπ b hab)) c'
      (Cocone.ext ηM (by rintro (_ | _) <;>
        simp [c', b', d, i₁, i₂, parallelPairIsoMk,
          NatIso.ofComponents_inv_app]))).toFun (isColimitOfPreserves Φ hc.some)
  exact ⟨I, K, Φ.obj P, Φ.obj Q, _, _, ⟨hcofan ι hP.some⟩, ⟨hcofan κ hQ.some⟩, Φ.map a, b', hab',
    ⟨hc'⟩⟩

variable (R : Sheaf J RingCat.{r}) (S : Sheaf J RingCat.{s})
    (e : ∀ U, S.obj.obj U ≃+* R.obj.obj U)
    (he : ∀ {U V} (f : U ⟶ V) (a : S.obj.obj U),
      e V (S.obj.map f a) = R.obj.map f (e U a))

/-- Restriction of coefficients carries the universe-lifted structure sheaf to the universe-lifted
structure sheaf. -/
def restrictCoefficientsUnitIso :
    (restrictCoefficients.{w, v, r, s, max w v r s m} R S (fun U => (e U).toRingHom) he).obj
      (SheafOfModules.uliftForPresentation.{w, v, r, r, max w v r s m}
        (SheafOfModules.unit R)) ≅
      SheafOfModules.uliftForPresentation.{w, v, s, s, max w v r s m}
        (SheafOfModules.unit S) := by
  apply (SheafOfModules.fullyFaithfulForget S).preimageIso
  refine PresheafOfModules.isoMk (fun U => ?_) ?_
  · let A := ((restrictCoefficients.{w, v, r, s, max w v r s m} R S
        (fun U => (e U).toRingHom) he).obj
        (SheafOfModules.uliftForPresentation.{w, v, r, r, max w v r s m}
          (SheafOfModules.unit R))).val.obj U
    let B := (SheafOfModules.uliftForPresentation.{w, v, s, s, max w v r s m}
          (SheafOfModules.unit S)).val.obj U
    let g : A ≃ₗ[S.obj.obj U] B :=
      { toFun := fun x => ULift.up ((e U).symm (show R.obj.obj U from x.down))
        invFun := fun x => ULift.up (show (SheafOfModules.unit R).val.obj U from
          e U x.down)
        map_add' := fun x y => congrArg ULift.up (map_add (e U).symm
          (show R.obj.obj U from x.down) (show R.obj.obj U from y.down))
        map_smul' := fun a x => by
          refine congrArg ULift.up ?_
          change (e U).symm (e U a * (show R.obj.obj U from x.down)) =
            a * (e U).symm (show R.obj.obj U from x.down)
          rw [map_mul, RingEquiv.symm_apply_apply]
        left_inv := fun x => congrArg ULift.up ((e U).apply_symm_apply _)
        right_inv := fun x => congrArg ULift.up ((e U).symm_apply_apply _) }
    exact g.toModuleIso
  · intro U V f
    ext x
    apply ULift.ext
    change (e V).symm (R.obj.map f x.down) = S.obj.map f ((e U).symm x.down)
    apply (e V).injective
    simp only [RingEquiv.apply_symm_apply, he]
    exact congrArg _ ((e U).apply_symm_apply _).symm

/-- Restriction of coefficients commutes with raising the universe of the sections. -/
def restrictCoefficientsUliftIso (M : SheafOfModules.{max r s m} R) :
    (restrictCoefficients.{w, v, r, s, max w v r s m} R S (fun U => (e U).toRingHom) he).obj
      (SheafOfModules.uliftForPresentation.{w, v, r, max r s m, max w v r} M) ≅
    SheafOfModules.uliftForPresentation.{w, v, s, max r s m, max w v s}
      ((restrictCoefficients.{w, v, r, s, max r s m} R S (fun U => (e U).toRingHom) he).obj M) := by
  apply (SheafOfModules.fullyFaithfulForget S).preimageIso
  refine PresheafOfModules.isoMk (fun U => ?_) ?_
  · let A := ((restrictCoefficients.{w, v, r, s, max w v r s m} R S
      (fun U => (e U).toRingHom) he).obj
      (SheafOfModules.uliftForPresentation.{w, v, r, max r s m, max w v r} M)).val.obj U
    let B := (SheafOfModules.uliftForPresentation.{w, v, s, max r s m, max w v s}
      ((restrictCoefficients.{w, v, r, s, max r s m} R S
        (fun U => (e U).toRingHom) he).obj M)).val.obj U
    let g : A ≃ₗ[S.obj.obj U] B :=
      { toFun := fun x => ULift.up x.down
        invFun := fun x => ULift.up x.down
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact g.toModuleIso
  · exact fun _ _ _ => by ext; rfl

/-- **Quasi-coherence is carried by restriction of coefficients along a compatible family of
ring isomorphisms**, the two sheaves of rings having sections in possibly different universes. -/
theorem isQuasicoherentOnSite_restrictCoefficients (M : SheafOfModules.{max r s m} R)
    (hM : M.IsQuasicoherentOnSite) :
    ((restrictCoefficients.{w, v, r, s, max r s m} R S (fun U => (e U).toRingHom) he).obj
      M).IsQuasicoherentOnSite := by
  refine ⟨fun U => ?_⟩
  obtain ⟨I, V, f, hcover, hpres⟩ := hM.locally_hasGlobalPresentation U
  refine ⟨I, V, f, hcover, fun i => ?_⟩
  let e' : ∀ W, (S.over (V i)).obj.obj W ≃+* (R.over (V i)).obj.obj W :=
    fun W => e ((Over.forget (V i)).op.obj W)
  have he' : ∀ {W W'} (g : W ⟶ W') (a : (S.over (V i)).obj.obj W),
      e' W' ((S.over (V i)).obj.map g a) = (R.over (V i)).obj.map g (e' W a) :=
    fun g a => he ((Over.forget (V i)).op.map g) a
  let E := coefficientEquivalence.{max w v, v, r, s, max w v r s m}
    (R.over (V i)) (S.over (V i)) e' he'
  have : E.functor.IsEquivalence := E.isEquivalence_functor
  have : E.functor.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  exact hasGlobalPresentation_of_map.{r, s, m, max w v, v} (M.over (V i)) _ E.functor
    (restrictCoefficientsUnitIso.{r, s, m, max w v, v} (R.over (V i)) (S.over (V i)) e' he')
    (restrictCoefficientsUliftIso.{r, s, m, max w v, v} (R.over (V i)) (S.over (V i)) e' he'
      (M.over (V i)))
    (hpres i)

end Presentation

end Stacks.SheafOfModules.CoefficientChange
