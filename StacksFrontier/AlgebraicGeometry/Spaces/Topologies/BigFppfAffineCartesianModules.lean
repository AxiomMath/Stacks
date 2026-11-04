module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfAffinePresentedModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfFlatAffineSchemesOver
public import StacksFrontier.CategoryTheory.Sites.Modules.CartesianLocalOnCover

/-!
# Locally presented modules on `(Spaces/X)_fppf` are cartesian along maps of affines

Let `T` be a big fppf site of algebraic spaces over a scheme `S` and `X` one of its objects. A
sheaf of modules `N` on `(Spaces/X)_fppf` which has a global presentation over the objects of a
covering of every object is *cartesian* over the morphisms of affine schemes over an affine object
`U`: the restriction map exhibits the sections over the source as the base change of the sections
over the target.

## Main results

* `AffineSchemesOver.isIso_restrictionBaseChange_of_hasGlobalPresentation`: a module presented
  over an affine scheme `W` over `U` is cartesian over every morphism into `W`.
* `AffineSchemesOver.isIso_restrictionBaseChange_of_flat`: a locally presented module is cartesian
  over every morphism with flat ring map between affine schemes over an affine `U`.
* `AffineSchemesOver.isIso_restrictionBaseChange_of_locallyPresented`: a locally presented module
  is cartesian over every morphism between affine schemes over an affine `U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.PresheafOfModules

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

/-- Being cartesian over a morphism transfers along equalities of its source and target. -/
theorem isIso_restrictionBaseChange_of_eq {A A' B B' : C} (hA : A = A') (hB : B = B')
    (g : B ⟶ A) (g' : B' ⟶ A') (hg : g' = eqToHom hB.symm ≫ g ≫ eqToHom hA)
    (h : IsIso (restrictionBaseChange.{_, _, u, u} M g.op)) :
    IsIso (restrictionBaseChange.{_, _, u, u} M g'.op) := by
  subst hA hB
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hg
  subst hg
  exact h

/-- Being cartesian over a morphism of the opposite category transfers along equalities of its
source and target. -/
theorem isIso_restrictionBaseChange_of_eq_op {A A' B B' : Cᵒᵖ} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (f' : A' ⟶ B') (hf : f' = eqToHom hA.symm ≫ f ≫ eqToHom hB)
    (h : IsIso (restrictionBaseChange.{_, _, u, u} M f)) :
    IsIso (restrictionBaseChange.{_, _, u, u} M f') := by
  subst hA hB
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  subst hf
  exact h

end Stacks.PresheafOfModules

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {X : T.Spaces}

/-- The sections of the ring sheaf of `(Spaces/X)_fppf` are commutative. -/
instance bigFppfRingSheaf_commSections :
    Stacks.TerminalBaseChange.CommSections (bigFppfRingSheaf T X).obj where
  mul_comm A a b := mul_comm (G := (T.structureSheaf X).obj.obj A) a b

/-- The sections of the restriction of the ring sheaf of `(Spaces/X)_fppf` to the slice over `U`
are commutative. -/
instance sliceRingSheaf_commSections (U : BigFppfSpaceOver T X) :
    Stacks.TerminalBaseChange.CommSections ((bigFppfRingSheaf T X).over U).obj where
  mul_comm A a b := mul_comm (G := (T.structureSheaf X).obj.obj (op A.unop.left)) a b

namespace AffineSchemesOver

variable {U : BigFppfSpaceOver T X}

/-- **The base-change comparison of the restriction of a sheaf of modules to the affine schemes
over `U` is that of the sheaf itself**, along the image morphism in `(Spaces/X)_fppf`. -/
theorem isIso_restrictionBaseChange_affineRestriction_iff
    (N : SheafOfModules.{u + 1} (bigFppfRingSheaf T X)) {Y Y' : AffineSchemesOver T U}
    (k : Y ⟶ Y') :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{_, _, u + 1, u + 1}
        (R := ringFunctor T U) (affineRestriction N).val k.op) ↔
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{_, _, u + 1, u + 1}
        (R := Stacks.TerminalBaseChange.commPresheaf (bigFppfRingSheaf T X).obj) N.val
        ((Over.forget U).map ((toSlice T U).map k)).op) := by
  have h₁ := Stacks.PresheafOfModules.isIso_restrictionBaseChange_pushforward_iff
    (J := topology (T := T) (V := U)) (K := (BigFppfSpaceOver.topology T X).over U) (toSlice T U)
    ((bigFppfRingSheaf T X).over U) (N.over U) k.op
  have h₂ := Stacks.PresheafOfModules.isIso_restrictionBaseChange_pushforward_iff
    (J := (BigFppfSpaceOver.topology T X).over U) (K := BigFppfSpaceOver.topology T X)
    (Over.forget U) (bigFppfRingSheaf T X) N ((toSlice T U).op.map k.op)
  exact h₁.trans h₂

/-- **A sheaf of modules presented over an affine scheme `W` over `U` is cartesian over every
morphism of affine schemes into `W`.** -/
theorem isIso_restrictionBaseChange_of_hasGlobalPresentation
    (N : SheafOfModules.{u + 1} (bigFppfRingSheaf T X)) {W Y : AffineSchemesOver T U}
    (hW : (N.over ((toOver T U).obj W)).HasGlobalPresentation) (k : Y ⟶ W) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{_, _, u + 1, u + 1}
      (R := ringFunctor T U) (affineRestriction N).val k.op) := by
  rw [isIso_restrictionBaseChange_affineRestriction_iff]
  let V' : BigFppfSpaceOver T X := (toOver T U).obj W
  let e' : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj W.obj.left ≅ V'.left := Iso.refl _
  obtain ⟨p⟩ := SheafOfModules.HasGlobalPresentation.nonempty_presentation.{u + 1, u + 1, u + 1} hW
  obtain ⟨M', ⟨eM⟩⟩ := Stacks.DenseSubsiteBaseChange.exists_iso_associatedSheaf_of_presentation
    (baseChangeIsSheaf (V := V') W.obj.left W.property e')
    (isTerminal_toSlice_ofIso (U := V') W.obj.left W.property e') p
  let R' := Stacks.DenseSubsiteModules.moduleRestriction (topology (T := T) (V := V'))
    ((BigFppfSpaceOver.topology T X).over V') (toSlice T V') sliceRingSheaf
  let Ŷ : AffineSchemesOver T V' :=
    ⟨CostructuredArrow.mk ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).map k.hom.left),
      Y.property⟩
  let k' : Ŷ ⟶ ofIso W.obj.left W.property e' :=
    ObjectProperty.homMk (CostructuredArrow.homMk k.hom.left (Category.comp_id _))
  have h₁ := (isIso_restrictionBaseChange_affineRestriction_iff N k').mp
    (@Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_iso _ _ (ringFunctor T V') _ _
      ((SheafOfModules.forget _).mapIso (R'.mapIso eM ≪≫
        (Stacks.DenseSubsiteBaseChange.associatedSheafRestrictionIso
          (baseChangeIsSheaf (V := V') W.obj.left W.property e')).app M')).symm _ _ k'.op
      (Stacks.TerminalBaseChange.isIso_restrictionBaseChange_baseChangePresheaf.{u + 1}
        (ringPresheaf (T := T) (V := V')) (isTerminalOfIso W.obj.left W.property e') M' k'))
  refine Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_eq N.val ?_ ?_
    ((Over.forget V').map ((toSlice T V').map k')) ((Over.forget U).map ((toSlice T U).map k))
    ?_ h₁
  · show Over.mk ((Iso.refl _).hom ≫ W.obj.hom ≫ U.hom) = Over.mk (W.obj.hom ≫ U.hom)
    rw [Iso.refl_hom, Category.id_comp]
  · show Over.mk ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).map k.hom.left ≫
        W.obj.hom ≫ U.hom) = Over.mk (Y.obj.hom ≫ U.hom)
    rw [← Category.assoc, CostructuredArrow.w k.hom]
  · apply Over.OverMorphism.ext
    simp
    rfl

/-- The affine schemes over `U` mapping to an affine scheme `W₀` over `U` over which a sheaf of
modules has a global presentation. -/
def presentedSieve (W₀ : AffineSchemesOver T U)
    (N : SheafOfModules.{u + 1} (bigFppfRingSheaf T X)) : Sieve W₀ where
  arrows W _ := (N.over ((toOver T U).obj W)).HasGlobalPresentation
  downward_closed {_W _W'} _ hW f :=
    SheafOfModules.HasGlobalPresentation.overMap.{u + 1, u + 1, u + 1} N ((toOver T U).map f) hW

/-- **A locally presented sheaf of modules is presented over a covering of every affine scheme
over `U`.** -/
theorem presentedSieve_mem (W₀ : AffineSchemesOver T U)
    (N : SheafOfModules.{u + 1} (bigFppfRingSheaf T X))
    (hN : ∀ Z : BigFppfSpaceOver T X,
      Sieve.generate (fun (Z' : BigFppfSpaceOver T X) (_ : Z' ⟶ Z) ↦
        (N.over Z').HasGlobalPresentation) ∈ BigFppfSpaceOver.topology T X Z) :
    presentedSieve W₀ N ∈ topology (T := T) (V := U) W₀ := by
  let K := (BigFppfSpaceOver.topology T X).over U
  let S₁ : Sieve ((toSlice T U).obj W₀) :=
    { arrows := fun Z _ ↦ (N.over Z.left).HasGlobalPresentation
      downward_closed := fun {Z Z'} _ hZ f ↦
        SheafOfModules.HasGlobalPresentation.overMap.{u + 1, u + 1, u + 1} N f.left hZ }
  have hS₁ : S₁ ∈ K _ := by
    rw [GrothendieckTopology.mem_over_iff]
    refine (BigFppfSpaceOver.topology T X).superset_covering ?_ (hN _)
    rw [Sieve.generate_le_iff]
    intro Z' a ha
    rwa [Sieve.overEquiv_iff]
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense]
  refine K.superset_covering ?_ (K.bind_covering hS₁ (fun Z f _ ↦
    (toSlice T U).is_cover_of_isCoverDense K Z))
  rintro _ _ ⟨Z, g₁, f, hf, ⟨c⟩, rfl⟩
  exact ⟨c.obj, (toSlice T U).preimage (c.map ≫ f), c.lift,
    SheafOfModules.HasGlobalPresentation.overMap.{u + 1, u + 1, u + 1} N c.map.left hf,
    by rw [Functor.map_preimage, ← Category.assoc, c.fac]⟩

variable (V₀ : T.Schemes)
  (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
  (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ U.left)

include hV₀ e in
/-- **A locally presented sheaf of modules on `(Spaces/X)_fppf` is cartesian over every morphism
with flat ring map between affine schemes over an affine `U`.** -/
theorem isIso_restrictionBaseChange_of_flat (N : SheafOfModules.{u + 1} (bigFppfRingSheaf T X))
    (hN : ∀ Z : BigFppfSpaceOver T X,
      Sieve.generate (fun (Z' : BigFppfSpaceOver T X) (_ : Z' ⟶ Z) ↦
        (N.over Z').HasGlobalPresentation) ∈ BigFppfSpaceOver.topology T X Z)
    {Y W₀ : AffineSchemesOver T U} (g : Y ⟶ W₀)
    (hg : ((ringFunctor T U).map g.op).hom.Flat) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{_, _, u + 1, u + 1}
      (R := ringFunctor T U) (affineRestriction N).val g.op) := by
  classical
  have := hasFiniteLimits V₀ e hV₀
  obtain ⟨n, Z, hZ, φ, hRφ, hcov, -⟩ := exists_finite_fppf_ofArrows_le W₀
    (presentedSieve W₀ N) (presentedSieve_mem W₀ N hN)
  let W : Fin n → AffineSchemesOver T U := fun i ↦ memberObj W₀ (hZ i) (φ i)
  let gw : ∀ i, W i ⟶ W₀ := fun i ↦ homOfScheme W₀ (hZ i) (φ i)
  let M := (affineRestriction (U := U) N).val
  have hsT : Presieve.IsSheaf (topology (T := T) (V := U)) (M.presheaf ⋙ forget AddCommGrpCat) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact (Presheaf.isSheaf_iff_isSheaf_comp (topology (T := T) (V := U))
      M.presheaf (forget AddCommGrpCat)).mp (affineRestriction (U := U) N).isSheaf
  have hsf {Y' : AffineSchemesOver T U} {R : Presieve Y'}
      (h : Sieve.generate R ∈ topology (T := T) (V := U) Y') :
      Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat) R :=
    (Presieve.isSheafFor_iff_generate _).mpr (hsT _ h)
  have hcoverU : Sieve.ofArrows (fun i ↦ pullback g (gw i))
      (fun i ↦ pullback.fst g (gw i)) ∈ topology (T := T) (V := U) Y := by
    refine (topology (T := T) (V := U)).superset_covering ?_
      ((topology (T := T) (V := U)).pullback_stable g hcov)
    rintro Z' h ⟨Y', g₁, g₂, ⟨i⟩, hg'⟩
    have hmem := (Sieve.ofArrows (fun i ↦ pullback g (gw i))
        (fun i ↦ pullback.fst g (gw i))).downward_closed
      (Sieve.ofArrows_mk (fun i ↦ pullback g (gw i)) (fun i ↦ pullback.fst g (gw i)) i)
      (pullback.lift h g₁ hg'.symm)
    rwa [pullback.lift_fst] at hmem
  refine Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_cover (R := ringFunctor T U) M g
    W gw hg (hsf hcov) (hsf hcoverU)
    (fun i ↦ isPushout_ringPresheaf (f := g) (g := gw i) (p₁ := pullback.fst g (gw i))
      (p₂ := pullback.snd g (gw i))
      ((IsPullback.of_hasPullback g (gw i)).map (toSchemeFunctor V₀ e)))
    (fun c ↦ isPushout_ringPresheaf (f := g) (g := pullback.fst (gw c.1) (gw c.2) ≫ gw c.1)
      (p₁ := pullback.fst g _) (p₂ := pullback.snd g _)
      ((IsPullback.of_hasPullback g _).map (toSchemeFunctor V₀ e)))
    (fun i ↦ isIso_restrictionBaseChange_of_hasGlobalPresentation N (hRφ i) _)
    (fun c ↦ isIso_restrictionBaseChange_of_hasGlobalPresentation N
      (SheafOfModules.HasGlobalPresentation.overMap.{u + 1, u + 1, u + 1} N
        ((toOver T U).map (pullback.fst (gw c.1) (gw c.2))) (hRφ c.1)) _)

include hV₀ e in
/-- **A locally presented sheaf of modules on `(Spaces/X)_fppf` is cartesian over every morphism
of affine schemes over an affine `U`.** -/
theorem isIso_restrictionBaseChange_of_locallyPresented
    (N : SheafOfModules.{u + 1} (bigFppfRingSheaf T X))
    (hN : ∀ Z : BigFppfSpaceOver T X,
      Sieve.generate (fun (Z' : BigFppfSpaceOver T X) (_ : Z' ⟶ Z) ↦
        (N.over Z').HasGlobalPresentation) ∈ BigFppfSpaceOver.topology T X Z)
    {Y W₀ : AffineSchemesOver T U} (g : Y ⟶ W₀) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{_, _, u + 1, u + 1}
      (R := ringFunctor T U) (affineRestriction N).val g.op) := by
  classical
  have := hasFiniteLimits V₀ e hV₀
  obtain ⟨n, Z, hZ, φ, hRφ, -, hfppf⟩ := exists_finite_fppf_ofArrows_le W₀
    (presentedSieve W₀ N) (presentedSieve_mem W₀ N hN)
  let G := BigFppfOver.toScheme T.schemeSite S T.scheme_mem
  let W : Fin n → AffineSchemesOver T U := fun i ↦ memberObj W₀ (hZ i) (φ i)
  let gw : ∀ i, W i ⟶ W₀ := fun i ↦ homOfScheme W₀ (hZ i) (φ i)
  have hflat : ∀ i, Flat (G.map (gw i).hom.left) := by
    have h := hfppf
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at h
    exact fun i ↦ (h.2 i).1
  have hgw : ∀ i, ((ringFunctor T U).map (gw i).op).hom.Flat :=
    fun i ↦ flat_ringFunctor_map_of_flat (gw i) (hflat i)
  have hq : ∀ i, ((ringFunctor T U).map (pullback.fst g (gw i)).op).hom.Flat :=
    fun i ↦ flat_ringFunctor_of_isPullback V₀ hV₀ e (IsPullback.of_hasPullback g (gw i)) (hgw i)
  have hff := faithfullyFlat_pi_of_fppf Y (fun i ↦ pullback g (gw i))
    (fun i ↦ pullback.fst g (gw i))
    (Precoverage.mem_coverings_of_isPullback (fun i ↦ G.map (gw i).hom.left) hfppf
      (G.map g.hom.left) (fun i ↦ G.map (pullback.fst g (gw i)).hom.left)
      (fun i ↦ G.map (pullback.snd g (gw i)).hom.left)
      (fun i ↦ (IsPullback.of_hasPullback g (gw i)).map (toSchemeFunctor V₀ e)))
  refine Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_faithfullyFlat
    (R := ringFunctor T U) (affineRestriction N).val g.op (fun i ↦ Opposite.op (pullback g (gw i)))
    (fun i ↦ (pullback.fst g (gw i)).op) hff
    (fun i ↦ isIso_restrictionBaseChange_of_flat V₀ hV₀ e N hN _ (hq i)) (fun i ↦ ?_)
  rw [← op_comp, pullback.condition, op_comp]
  exact Stacks.PresheafOfModules.isIso_restrictionBaseChange_comp _ _ _
    (isIso_restrictionBaseChange_of_flat V₀ hV₀ e N hN _ (hgw i))
    (isIso_restrictionBaseChange_of_hasGlobalPresentation N (hRφ i) _)

end AffineSchemesOver

end AlgebraicGeometry.BigFppfSpaceSite

end
