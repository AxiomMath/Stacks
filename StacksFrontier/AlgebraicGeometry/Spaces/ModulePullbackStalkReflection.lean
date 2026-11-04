module

public import StacksFrontier.AlgebraicGeometry.Descent.UniversallyInjective.Exactness
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FaithfullyFlatLocalHom
import StacksFrontier.RingTheory.Flat.FaithfullyFlatComp
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Injectivity and surjectivity of a map of modules on stalks, and flat pullback

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `v : M ⟶ N` be a map
of `𝒪_X`-modules.  Two independence statements for the behaviour of `v` on stalks are proved.

Whether `v` is injective, respectively surjective, on the set-valued stalk at a geometric point
`x̄` depends only on the point of `X` that `x̄` lies over: by Stacks 04K4 the stalk functors at
two geometric points over a common point are isomorphic as functors, so the two stalk maps of
`v` sit in a commuting square with bijective vertical maps.

Along a flat morphism `φ : X' ⟶ X` the pullback `φ^*v` is injective, respectively surjective,
on the stalk at a geometric point `x̄` of `X'` exactly when `v` is on the stalk at the image
point `φ ∘ x̄`.  By Stacks 05V5 the stalk of `φ^*` at `x̄` is the stalk at `φ ∘ x̄` followed by
extension of scalars along the homomorphism `(𝒪_X)_{φ ∘ x̄} ⟶ (𝒪_{X'})_{x̄}` of structure-sheaf
stalks, which is faithfully flat by Stacks 03MK, and a faithfully flat base change neither
creates nor destroys injectivity or surjectivity.

## Main results

* `AlgebraicGeometry.Space.injective_moduleStalkSetMap_iff_of_liesOver` and
  `AlgebraicGeometry.Space.surjective_moduleStalkSetMap_iff_of_liesOver`: injectivity,
  respectively surjectivity, of the stalk map of a map of `𝒪_X`-modules at a geometric point
  depends only on the point of `X` the geometric point lies over.
* `AlgebraicGeometry.Space.faithfullyFlat_smallEtaleStalkPullbackRingMap`: the homomorphism
  `(𝒪_X)_{φ ∘ x̄} ⟶ (𝒪_{X'})_{x̄}` of structure-sheaf stalks of a flat morphism is faithfully
  flat.
* `AlgebraicGeometry.Space.mono_moduleStalk_map_modulePullback_iff_of_isFlat` and
  `AlgebraicGeometry.Space.epi_moduleStalk_map_modulePullback_iff_of_isFlat`: the stalk map of
  `φ^*v` at a geometric point of the source is a monomorphism, respectively an epimorphism,
  exactly when the stalk map of `v` at the image point is.
* `AlgebraicGeometry.Space.injective_moduleStalk_map_modulePullback_iff_of_isFlat` and
  `AlgebraicGeometry.Space.surjective_moduleStalk_map_modulePullback_iff_of_isFlat`: the same
  two statements read on the underlying maps of sets.

## References

* [Stacks Project, Tag 04K4](https://stacks.math.columbia.edu/tag/04K4)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 03MK](https://stacks.math.columbia.edu/tag/03MK)
* [Stacks Project, Tag 07UF](https://stacks.math.columbia.edu/tag/07UF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace RingHom.FaithfullyFlat

end RingHom.FaithfullyFlat

namespace CategoryTheory

/-- In a commuting square whose two vertical maps are isomorphisms, the top map is a
monomorphism exactly when the bottom one is. -/
theorem mono_iff_mono_of_comm_sq {C : Type*} [Category C] {A₁ A₂ A₃ A₄ : C} {f : A₁ ⟶ A₂}
    {f' : A₃ ⟶ A₄} (a : A₁ ≅ A₃) (b : A₂ ≅ A₄) (h : f ≫ b.hom = a.hom ≫ f') :
    Mono f ↔ Mono f' :=
  ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff (Arrow.isoMk a b h.symm)).trans Iff.rfl

/-- In a commuting square whose two vertical maps are isomorphisms, the top map is an
epimorphism exactly when the bottom one is. -/
theorem epi_iff_epi_of_comm_sq {C : Type*} [Category C] {A₁ A₂ A₃ A₄ : C} {f : A₁ ⟶ A₂}
    {f' : A₃ ⟶ A₄} (a : A₁ ≅ A₃) (b : A₂ ≅ A₄) (h : f ≫ b.hom = a.hom ≫ f') :
    Epi f ↔ Epi f' :=
  ((MorphismProperty.epimorphisms C).arrow_mk_iso_iff (Arrow.isoMk a b h.symm)).trans Iff.rfl

end CategoryTheory

namespace ModuleCat

variable {R T : Type u} [CommRing R] [CommRing T]

/-- **A faithfully flat base change neither creates nor destroys monomorphisms.**  For a
faithfully flat `f : R →+* T` and a map `w` of `R`-modules, `T ⊗_R w` is a monomorphism exactly
when `w` is.

Both directions are read off the kernel: extension of scalars along a flat ring map preserves
it, and along a faithfully flat one detects its vanishing. -/
@[ega "IV 2.2.7" "special case"]
theorem mono_extendScalars_map_iff_of_faithfullyFlat {f : R →+* T} (hf : f.FaithfullyFlat)
    {M N : ModuleCat.{u} R} (w : M ⟶ N) :
    Mono ((ModuleCat.extendScalars.{u, u, u} f).map w) ↔ Mono w := by
  have hlim := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf.flat
  rw [Preadditive.mono_iff_isZero_kernel, Preadditive.mono_iff_isZero_kernel,
    ← ModuleCat.extendScalars_isZero_iff_of_faithfullyFlat f hf (kernel w),
    Iso.isZero_iff (PreservesKernel.iso (ModuleCat.extendScalars.{u, u, u} f) w)]

/-- **A faithfully flat base change neither creates nor destroys epimorphisms.**  For a
faithfully flat `f : R →+* T` and a map `w` of `R`-modules, `T ⊗_R w` is an epimorphism exactly
when `w` is.

Both directions are read off the cokernel: extension of scalars preserves it, being a left
adjoint, and along a faithfully flat ring map detects its vanishing. -/
@[ega "IV 2.2.7" "special case"]
theorem epi_extendScalars_map_iff_of_faithfullyFlat {f : R →+* T} (hf : f.FaithfullyFlat)
    {M N : ModuleCat.{u} R} (w : M ⟶ N) :
    Epi ((ModuleCat.extendScalars.{u, u, u} f).map w) ↔ Epi w := by
  rw [Preadditive.epi_iff_isZero_cokernel, Preadditive.epi_iff_isZero_cokernel,
    ← ModuleCat.extendScalars_isZero_iff_of_faithfullyFlat f hf (cokernel w),
    Iso.isZero_iff (PreservesCokernel.iso (ModuleCat.extendScalars.{u, u, u} f) w)]

end ModuleCat

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Independence of the choice of geometric point -/

section Independence

variable (X : AlgebraicSpaces B S hS)

/-- The map of presheaves of sets underlying a map of `𝒪_X`-modules: forget the module
structure, then the group structure.  This is the morphism whose stalk map at a geometric point
is `AlgebraicGeometry.Space.moduleStalkSetMap`. -/
private def moduleSetMap {M N : Modules.{u, m} B S hS X.1 X.2} (v : M ⟶ N) :
    M.val.presheaf ⋙ forget AddCommGrpCat.{m} ⟶ N.val.presheaf ⋙ forget AddCommGrpCat.{m} :=
  Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map v.val) (forget AddCommGrpCat.{m})

/-- The stalk map of a map of `𝒪_X`-modules is the stalk map of the underlying morphism of
presheaves of sets. -/
private theorem moduleStalkSetMap_eq (p : GeometricPoint B S hS X.1)
    {M N : Modules.{u, m} B S hS X.1 X.2} (v : M ⟶ N) :
    moduleStalkSetMap B S hS X p v = stalkSetMap p (moduleSetMap B S hS X v) :=
  rfl

/-- **The two stalk maps of a map of modules at geometric points over a common point sit in a
commuting square with bijective vertical maps.**  The bijections are the components of an
isomorphism of stalk functors supplied by Stacks 04K4, so the square is its naturality square at
the morphism of presheaves of sets underlying the map of modules. -/
private theorem exists_equiv_comm_moduleStalkSetMap {x : points B S hS X.1}
    (p q : GeometricPoint B S hS X.1) (hp : p.LiesOver x) (hq : q.LiesOver x)
    {M N : Modules.{u, m} B S hS X.1 X.2} (v : M ⟶ N) :
    ∃ (eM : stalkSet p (M.val.presheaf ⋙ forget AddCommGrpCat.{m}) ≃
        stalkSet q (M.val.presheaf ⋙ forget AddCommGrpCat.{m}))
      (eN : stalkSet p (N.val.presheaf ⋙ forget AddCommGrpCat.{m}) ≃
        stalkSet q (N.val.presheaf ⋙ forget AddCommGrpCat.{m})),
      ∀ a, eN (moduleStalkSetMap B S hS X p v a) =
        moduleStalkSetMap B S hS X q v (eM a) := by
  obtain ⟨e⟩ := stalkSetFunctor_iso_of_liesOver.{u, m} X.2 p q hp hq
  exact ⟨(e.app (M.val.presheaf ⋙ forget AddCommGrpCat.{m})).toEquiv,
    (e.app (N.val.presheaf ⋙ forget AddCommGrpCat.{m})).toEquiv,
    NatTrans.naturality_apply e.hom (moduleSetMap B S hS X v)⟩

/-- **Injectivity of a map of `𝒪_X`-modules on a stalk depends only on the underlying point.**
For two geometric points `p` and `q` of `X` lying over the same point of the point set of `X`,
the stalk map of `v : M ⟶ N` at `p` is injective exactly when the stalk map at `q` is.

This is Stacks 04K4: the stalk functors at `p` and at `q` are isomorphic as functors on
presheaves on the small étale site, so the two stalk maps of `v` are conjugate. -/
theorem injective_moduleStalkSetMap_iff_of_liesOver {x : points B S hS X.1}
    (p q : GeometricPoint B S hS X.1) (hp : p.LiesOver x) (hq : q.LiesOver x)
    {M N : Modules.{u, m} B S hS X.1 X.2} (v : M ⟶ N) :
    Function.Injective (moduleStalkSetMap B S hS X p v) ↔
      Function.Injective (moduleStalkSetMap B S hS X q v) := by
  obtain ⟨eM, eN, hcomm⟩ :=
    exists_equiv_comm_moduleStalkSetMap B S hS X p q hp hq v
  refine ⟨fun h a b hab => ?_, fun h a b hab => ?_⟩
  · refine eM.symm.injective (h (eN.injective ?_))
    rwa [hcomm (eM.symm a), hcomm (eM.symm b), eM.apply_symm_apply, eM.apply_symm_apply]
  · refine eM.injective (h ?_)
    rw [← hcomm a, ← hcomm b, hab]

/-- **Surjectivity of a map of `𝒪_X`-modules on a stalk depends only on the underlying point.**
For two geometric points `p` and `q` of `X` lying over the same point of the point set of `X`,
the stalk map of `v : M ⟶ N` at `p` is surjective exactly when the stalk map at `q` is.

This is Stacks 04K4: the stalk functors at `p` and at `q` are isomorphic as functors on
presheaves on the small étale site, so the two stalk maps of `v` are conjugate. -/
theorem surjective_moduleStalkSetMap_iff_of_liesOver {x : points B S hS X.1}
    (p q : GeometricPoint B S hS X.1) (hp : p.LiesOver x) (hq : q.LiesOver x)
    {M N : Modules.{u, m} B S hS X.1 X.2} (v : M ⟶ N) :
    Function.Surjective (moduleStalkSetMap B S hS X p v) ↔
      Function.Surjective (moduleStalkSetMap B S hS X q v) := by
  obtain ⟨eM, eN, hcomm⟩ :=
    exists_equiv_comm_moduleStalkSetMap B S hS X p q hp hq v
  refine ⟨fun h z => ?_, fun h z => ?_⟩
  · obtain ⟨w, hw⟩ := h (eN.symm z)
    exact ⟨eM w, by rw [← hcomm w, hw, eN.apply_symm_apply]⟩
  · obtain ⟨w, hw⟩ := h (eN z)
    refine ⟨eM.symm w, eN.injective ?_⟩
    rw [hcomm (eM.symm w), eM.apply_symm_apply, hw]

end Independence

/-! ### Flat pullback on stalks -/

section FlatPullback

variable {X' X : AlgebraicSpaces B S hS}

/-- **The homomorphism of structure-sheaf stalks of a flat morphism is faithfully flat.**  For a
flat morphism `φ : X' ⟶ X` of algebraic spaces and a geometric point `x̄` of `X'`, the
homomorphism `(𝒪_X)_{φ ∘ x̄} ⟶ (𝒪_{X'})_{x̄}` along which Stacks 05V5 extends scalars is
faithfully flat.

It is conjugate, by the comparisons of Stacks 05VQ with the étale local rings, to the
homomorphism `𝒪_{X, φ ∘ x̄} ⟶ 𝒪_{X', x̄}` of étale local rings, which is faithfully flat by
Stacks 03MK. -/
theorem faithfullyFlat_smallEtaleStalkPullbackRingMap (φ : X' ⟶ X)
    (hφ : IsFlat B S hS φ.hom) (x : GeometricPoint B S hS X'.1) :
    (smallEtaleStalkPullbackRingMap B S hS φ x).FaithfullyFlat := by
  have hcomp : ((pointStalkRingEquiv B S hS X' x).toRingHom.comp
      (smallEtaleStalkPullbackRingMap B S hS φ x)).FaithfullyFlat := by
    rw [pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap B S hS φ x]
    exact RingHom.FaithfullyFlat.comp
      (RingHom.FaithfullyFlat.of_bijective
        (pointStalkRingEquiv B S hS X (geometricPointMap φ.hom x)).bijective)
      (faithfullyFlat_etaleLocalRingMap B S hS X'.2 X.2 φ.hom hφ x)
  have heq : (pointStalkRingEquiv B S hS X' x).symm.toRingHom.comp
        ((pointStalkRingEquiv B S hS X' x).toRingHom.comp
          (smallEtaleStalkPullbackRingMap B S hS φ x)) =
      smallEtaleStalkPullbackRingMap B S hS φ x :=
    RingHom.ext fun z => (pointStalkRingEquiv B S hS X' x).symm_apply_apply _
  rw [← heq]
  exact RingHom.FaithfullyFlat.comp hcomp
    (RingHom.FaithfullyFlat.of_bijective (pointStalkRingEquiv B S hS X' x).symm.bijective)

/-- **Stacks 05V5 at a geometric point of the source, as a natural isomorphism.**  The stalk at
`x̄` of the inverse image of `𝒪_X`-modules along `φ : X' ⟶ X` is the stalk at the image point
`φ ∘ x̄` followed by extension of scalars along the homomorphism
`(𝒪_X)_{φ ∘ x̄} ⟶ (𝒪_{X'})_{x̄}` of structure-sheaf stalks, naturally in the module. -/
private def modulePullbackGeometricStalkIso (φ : X' ⟶ X) (x : GeometricPoint B S hS X'.1) :
    modulePullback B S hS φ ⋙ Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X'.1 x X'.2) (smallEtaleRingedTopos B S hS X').O ≅
      Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap φ.hom x) X.2)
          (smallEtaleRingedTopos B S hS X).O ⋙
        ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS φ x) :=
  Stacks.Sheaves.StalkPullback.stalkFunctorIso (smallEtaleRingedToposModulesHom B S hS φ)
    (etaleSitePoint B S hS X'.1 x X'.2)
    (etaleSitePoint B S hS X.1 (geometricPointMap φ.hom x) X.2)
    (smallEtaleInverseImageFiberIso B S hS φ x)

/-- **The stalk map of a flat pullback is a monomorphism exactly when the stalk map at the image
point is.**  For a flat morphism `φ : X' ⟶ X` of algebraic spaces, a geometric point `x̄` of `X'`
and a map `v : M ⟶ N` of `𝒪_X`-modules, the stalk map of `φ^*v` at `x̄` is a monomorphism exactly
when the stalk map of `v` at `φ ∘ x̄` is.

By Stacks 05V5 the first is the base change of the second along the homomorphism of
structure-sheaf stalks, which is faithfully flat by Stacks 03MK. -/
theorem mono_moduleStalk_map_modulePullback_iff_of_isFlat (φ : X' ⟶ X)
    (hφ : IsFlat B S hS φ.hom) (x : GeometricPoint B S hS X'.1)
    {M N : Modules.{u, u} B S hS X.1 X.2} (v : M ⟶ N) :
    Mono ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 x X'.2)
          (smallEtaleRingedTopos B S hS X').O).map ((modulePullback B S hS φ).map v)) ↔
      Mono ((Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap φ.hom x) X.2)
          (smallEtaleRingedTopos B S hS X).O).map v) :=
  (mono_iff_mono_of_comm_sq ((modulePullbackGeometricStalkIso B S hS φ x).app M)
      ((modulePullbackGeometricStalkIso B S hS φ x).app N)
      ((modulePullbackGeometricStalkIso B S hS φ x).hom.naturality v)).trans
    (ModuleCat.mono_extendScalars_map_iff_of_faithfullyFlat
      (faithfullyFlat_smallEtaleStalkPullbackRingMap B S hS φ hφ x) _)

/-- **The stalk map of a flat pullback is an epimorphism exactly when the stalk map at the image
point is.**  For a flat morphism `φ : X' ⟶ X` of algebraic spaces, a geometric point `x̄` of `X'`
and a map `v : M ⟶ N` of `𝒪_X`-modules, the stalk map of `φ^*v` at `x̄` is an epimorphism exactly
when the stalk map of `v` at `φ ∘ x̄` is.

By Stacks 05V5 the first is the base change of the second along the homomorphism of
structure-sheaf stalks, which is faithfully flat by Stacks 03MK. -/
theorem epi_moduleStalk_map_modulePullback_iff_of_isFlat (φ : X' ⟶ X)
    (hφ : IsFlat B S hS φ.hom) (x : GeometricPoint B S hS X'.1)
    {M N : Modules.{u, u} B S hS X.1 X.2} (v : M ⟶ N) :
    Epi ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 x X'.2)
          (smallEtaleRingedTopos B S hS X').O).map ((modulePullback B S hS φ).map v)) ↔
      Epi ((Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap φ.hom x) X.2)
          (smallEtaleRingedTopos B S hS X).O).map v) :=
  (epi_iff_epi_of_comm_sq ((modulePullbackGeometricStalkIso B S hS φ x).app M)
      ((modulePullbackGeometricStalkIso B S hS φ x).app N)
      ((modulePullbackGeometricStalkIso B S hS φ x).hom.naturality v)).trans
    (ModuleCat.epi_extendScalars_map_iff_of_faithfullyFlat
      (faithfullyFlat_smallEtaleStalkPullbackRingMap B S hS φ hφ x) _)

/-- **The stalk map of a flat pullback is injective exactly when the stalk map at the image
point is**, read on the underlying maps of sets. -/
theorem injective_moduleStalk_map_modulePullback_iff_of_isFlat (φ : X' ⟶ X)
    (hφ : IsFlat B S hS φ.hom) (x : GeometricPoint B S hS X'.1)
    {M N : Modules.{u, u} B S hS X.1 X.2} (v : M ⟶ N) :
    Function.Injective (ConcreteCategory.hom
        ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 x X'.2)
          (smallEtaleRingedTopos B S hS X').O).map ((modulePullback B S hS φ).map v))) ↔
      Function.Injective (ConcreteCategory.hom
        ((Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap φ.hom x) X.2)
          (smallEtaleRingedTopos B S hS X).O).map v)) := by
  rw [← ModuleCat.mono_iff_injective, ← ModuleCat.mono_iff_injective]
  exact mono_moduleStalk_map_modulePullback_iff_of_isFlat B S hS φ hφ x v

/-- **The stalk map of a flat pullback is surjective exactly when the stalk map at the image
point is**, read on the underlying maps of sets. -/
theorem surjective_moduleStalk_map_modulePullback_iff_of_isFlat (φ : X' ⟶ X)
    (hφ : IsFlat B S hS φ.hom) (x : GeometricPoint B S hS X'.1)
    {M N : Modules.{u, u} B S hS X.1 X.2} (v : M ⟶ N) :
    Function.Surjective (ConcreteCategory.hom
        ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 x X'.2)
          (smallEtaleRingedTopos B S hS X').O).map ((modulePullback B S hS φ).map v))) ↔
      Function.Surjective (ConcreteCategory.hom
        ((Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap φ.hom x) X.2)
          (smallEtaleRingedTopos B S hS X).O).map v)) := by
  rw [← ModuleCat.epi_iff_surjective, ← ModuleCat.epi_iff_surjective]
  exact epi_moduleStalk_map_modulePullback_iff_of_isFlat B S hS φ hφ x v

end FlatPullback

end AlgebraicGeometry.Space

end
