module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomPrecomposition
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomPrecompositionQuasiIso
public import StacksFrontier.CategoryTheory.Functor.Derived.Absolute
public import StacksCore.Tactic.StacksAttribute

/- Keep the admissible-sequence convention previously supplied by the global instance. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

/-! # Precomposition by a quasi-isomorphism is an isomorphism of derived Hom functors

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let
`f : M → N` be a homomorphism of differential graded `(A, B)`-bimodules whose underlying
homomorphism of right differential graded `B`-modules is a quasi-isomorphism. The induced
transformation of derived Hom functors
`DifferentialGraded.Bimodule.derivedPrecomp : RHom(N, -) ⟹ RHom(M, -)` is then an isomorphism.
This is the last assertion of Tag 0BYV.

## Main results

* `DifferentialGraded.Bimodule.derivedPrecomp_isIso`: **Stacks 0BYV**, the assertion that
  precomposition by a quasi-isomorphism of bimodules induces a natural isomorphism of derived
  Hom functors. Nothing is assumed: the statement holds for an arbitrary pair of right derived
  functors of internal Hom out of the two bimodules.

## Implementation notes

*The shape of the argument.* The transformation is the descent along the localization of
precomposition on the homotopy categories, so it is determined by the comparison square of
`DifferentialGraded.Bimodule.derivedPrecomp_comparison`. At a differential graded `B`-module `I`
whose class in `K(B, d)` is orthogonal on the right to the acyclic modules, all three of the
other maps in that square are invertible:

* the two comparison maps, by
  `CategoryTheory.Functor.LeftExtension.isIso_hom_app_of_bijective` — the localization functor is
  bijective on the morphisms into such an `I`, so the identity of its image is terminal in the
  index category computing the pointwise left Kan extension there;
* precomposition itself, because
  `DifferentialGraded.Bimodule.quasiIso_precompModuleHom` says `Hom^•_B(N, I) ⟶ Hom^•_B(M, I)` is
  a quasi-isomorphism, and the localization inverts those.

Every object of `D(B, d)` is isomorphic to the image of such an `I`, by Tag 09KU
(`DifferentialGradedModule.exists_propertyI_resolution`) together with Tag 09KS, so the
transformation is invertible everywhere. No hypothesis is left over; in particular Tag 09KU is
*not* an assumption here, which is why the tag is bare.

*The conjugation through the two homotopy categories.* Precomposition on homotopy categories,
`DifferentialGraded.Bimodule.precompHomotopyNatTrans`, is the transformation of the differential
graded category conjugated by `DifferentialGradedModule.homotopyCategoryEquivalence`, whose
inverse is built by choice and is therefore opaque. It is the *functor* of that equivalence which
is transparent: it is the identity on objects and sends the homotopy class of a homomorphism to
the cohomology class of the associated cocycle. So the component of `precompHomotopyNatTrans` is
identified with `DifferentialGraded.Bimodule.precompModuleHom` by rewriting with
`CategoryTheory.Equivalence.inv_fun_map`, which expresses `inverse.map (functor.map u)` as `u`
conjugated by the unit, after which only isomorphisms separate the two.

## References

* [Stacks Project, Tag 0BYV](https://stacks.math.columbia.edu/tag/0BYV); the derived Hom functor
  is [Tag 09LI](https://stacks.math.columbia.edu/tag/09LI), the resolutions are
  [Tag 09KU](https://stacks.math.columbia.edu/tag/09KU) and their orthogonality to the acyclic
  modules is [Tag 09KS](https://stacks.math.columbia.edu/tag/09KS).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R} {M N : Bimodule A B}

/-- Conjugating a morphism by an equivalence does not change whether a functor sends it to an
isomorphism: the conjugate is the morphism itself bracketed by two components of the unit. -/
private theorem isIso_map_inv_fun_map {C : Type*} [Category C] {D : Type*} [Category D]
    {E : Type*} [Category E] (e : C ≌ D) {X Y : C} (u : X ⟶ Y) (Q : C ⥤ E)
    (h : IsIso (Q.map u)) :
    IsIso (Q.map (e.inverse.map (e.functor.map u))) := by
  rw [e.inv_fun_map, Q.map_comp, Q.map_comp]
  infer_instance

/-- A natural transformation invertible at one object is invertible at every isomorphic one. -/
private theorem isIso_app_of_iso {C : Type*} [Category C] {D : Type*} [Category D]
    {F G : C ⥤ D} (γ : F ⟶ G) {X Y : C} (e : X ≅ Y) (h : IsIso (γ.app Y)) :
    IsIso (γ.app X) := by
  have hc : IsIso (γ.app X ≫ G.map e.hom) := by
    rw [← γ.naturality e.hom]; infer_instance
  exact IsIso.of_isIso_comp_right (γ.app X) (G.map e.hom)

/-- The functor of the canonical equivalence `K(A, d) ≌ K(dgCategory A)` carries the homotopy
class of `DifferentialGraded.Bimodule.precompModuleHom` to the component of the differential
graded precomposition transformation. Both are the class of the cocycle attached to
precomposition with `f`. -/
private theorem homotopyCategoryEquivalence_functor_map_precompModuleHom
    (f : M ⟶ N) (I : DifferentialGradedModule B) :
    (homotopyCategoryEquivalence A).functor.map
        ((toHomotopyCategory A).map (precompModuleHom f I)) =
      (precompDGNatTrans f).onK.app
        ((homotopyCategoryEquivalence B).functor.obj ((toHomotopyCategory B).obj I)) := by
  rfl

/-- The localization of `K(C, d)` inverts the class of a quasi-isomorphism of differential graded
modules. -/
private theorem isIso_Q_map_toHomotopyCategory_map {C : DifferentialGradedAlgebra R}
    {X Y : DifferentialGradedModule C} (s : X ⟶ Y)
    (hs : QuasiIso ((forgetToCochainComplex C).map s)) :
    IsIso ((quasiIsomorphisms' C).Q.map ((toHomotopyCategory C).map s)) :=
  Localization.inverts (quasiIsomorphisms' C).Q (quasiIsomorphisms' C) _
    ((quasiIsomorphisms_map_iff' C s).2 hs)

/-- Precomposition with a quasi-isomorphism of bimodules becomes invertible in `D(A, d)` at a
differential graded `B`-module whose class in `K(B, d)` is orthogonal on the right to the
acyclic modules. -/
private theorem isIso_precompToDerivedNatTrans_app (f : M ⟶ N)
    (hf : QuasiIso ((forgetToCochainComplex B).map f.rightHom))
    (I : DifferentialGradedModule B)
    (hI : (acyclic' B).rightOrthogonal ((toHomotopyCategory B).obj I)) :
    IsIso ((precompToDerivedNatTrans f).app ((toHomotopyCategory B).obj I)) := by
  -- The component is the conjugate of `precompModuleHom f I` by the equivalence: the
  -- transformation on homotopy categories is the differential graded one read through it, and
  -- `homotopyCategoryEquivalence_functor_map_precompModuleHom` identifies the two.
  exact isIso_map_inv_fun_map (homotopyCategoryEquivalence A)
    ((toHomotopyCategory A).map (precompModuleHom f I)) (quasiIsomorphisms' A).Q
    (isIso_Q_map_toHomotopyCategory_map _ (quasiIso_precompModuleHom f hf I hI))

/-- **Stacks 0BYV**, the last assertion. If a homomorphism `f : M ⟶ N` of differential graded
`(A, B)`-bimodules is a quasi-isomorphism of the underlying right differential graded
`B`-modules, then the induced transformation `RHom(N, -) ⟹ RHom(M, -)` of derived Hom functors
is an isomorphism.

Nothing is assumed: `DN` and `DM` range over all right derived functors of internal Hom out of
the two bimodules, of which the ones of Tag 09LI
(`DifferentialGradedModule.derivedHomData`) are instances. -/
@[stacks 0BYV "quasi-isomorphisms induce natural isomorphisms"]
theorem derivedPrecomp_isIso
    (DN : DerivedHomData A B N.rightModule N.leftAction)
    (DM : DerivedHomData A B M.rightModule M.leftAction)
    (f : M ⟶ N) (hf : QuasiIso ((forgetToCochainComplex B).map f.rightHom)) :
    IsIso (derivedPrecomp DN DM f) := by
  -- Tag 09KU together with Tag 09KS: resolutions by right-orthogonal modules exist.
  have hresDG : ∀ X : DifferentialGradedModule B,
      ∃ (I : DifferentialGradedModule B) (s : X ⟶ I),
        QuasiIso ((forgetToCochainComplex B).map s) ∧
          (acyclic' B).rightOrthogonal ((toHomotopyCategory B).obj I) :=
    exists_quasiIso_rightOrthogonal_acyclic_of_propertyI_resolutions B
      (exists_propertyI_resolution B)
  -- The localization functor is bijective on the morphisms into a right-orthogonal object.
  have hbij : ∀ {I : HomotopyCategory B}, (acyclic' B).rightOrthogonal I →
      ∀ Y : HomotopyCategory B, Function.Bijective ((quasiIsomorphisms' B).Q.map :
        (Y ⟶ I) → ((quasiIsomorphisms' B).Q.obj Y ⟶ (quasiIsomorphisms' B).Q.obj I)) := by
    intro I hI Y
    have : (quasiIsomorphisms' B).Q.IsLocalization (acyclic' B).trW := by
      rw [acyclic_trW_eq_quasiIsomorphisms']; infer_instance
    exact ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated hI
      (quasiIsomorphisms' B).Q Y
  have hcores : ∀ X : HomotopyCategory B, ∃ (I : HomotopyCategory B) (s : X ⟶ I),
      quasiIsomorphisms' B s ∧ ∀ Y : HomotopyCategory B,
        Function.Bijective ((quasiIsomorphisms' B).Q.map :
          (Y ⟶ I) → ((quasiIsomorphisms' B).Q.obj Y ⟶ (quasiIsomorphisms' B).Q.obj I)) := by
    intro X
    obtain ⟨I, s, hs, hI⟩ :=
      exists_trW_rightOrthogonal_of_exists_quasiIso_rightOrthogonal B hresDG X
    refine ⟨I, s, ?_, hbij hI⟩
    rwa [← acyclic_trW_eq_quasiIsomorphisms']
  -- The comparison map of a right derived functor is invertible at a right-orthogonal module.
  have hcomp : ∀ {X : Bimodule A B} (D : DerivedHomData A B X.rightModule X.leftAction)
      (I : DifferentialGradedModule B),
      (acyclic' B).rightOrthogonal ((toHomotopyCategory B).obj I) →
      IsIso (D.comparison.app ((toHomotopyCategory B).obj I)) := by
    intro X D I hI
    have := D.isRightDerived
    have := Functor.hasPointwiseRightDerivedFunctor_of_coresolutions (quasiIsomorphisms' B)
      (homToDerivedCategory A B X.rightModule X.leftAction) hcores
    exact (Functor.LeftExtension.mk D.functor D.comparison).isIso_hom_app_of_bijective
      (Functor.isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor D.functor
        D.comparison (quasiIsomorphisms' B) _) (hbij hI)
  -- The transformation is invertible at the image of a right-orthogonal module.
  have hcore : ∀ I : DifferentialGradedModule B,
      (acyclic' B).rightOrthogonal ((toHomotopyCategory B).obj I) →
      IsIso ((derivedPrecomp DN DM f).app
        ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj I))) := by
    intro I hI
    have hN := hcomp DN I hI
    have hM := hcomp DM I hI
    have hpre := isIso_precompToDerivedNatTrans_app f hf I hI
    have heq := NatTrans.congr_app (derivedPrecomp_comparison DN DM f)
      ((toHomotopyCategory B).obj I)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at heq
    have hcomp : IsIso (DN.comparison.app ((toHomotopyCategory B).obj I) ≫
        (derivedPrecomp DN DM f).app
          ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj I))) := by
      rw [heq]; infer_instance
    exact IsIso.of_isIso_comp_left (DN.comparison.app ((toHomotopyCategory B).obj I))
      ((derivedPrecomp DN DM f).app
        ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj I)))
  -- Every object of the derived category is isomorphic to such an image.
  have := Localization.essSurj (quasiIsomorphisms' B).Q (quasiIsomorphisms' B)
  have happ : ∀ Y, IsIso ((derivedPrecomp DN DM f).app Y) := by
    intro Y
    obtain ⟨I, s, hs, hI⟩ := hresDG ((quasiIsomorphisms' B).Q.objPreimage Y).as
    have hsi := isIso_Q_map_toHomotopyCategory_map s hs
    exact isIso_app_of_iso (derivedPrecomp DN DM f)
      (((quasiIsomorphisms' B).Q.objObjPreimageIso Y).symm ≪≫ @asIso _ _ _ _ _ hsi)
      (hcore I hI)
  exact NatIso.isIso_of_isIso_app (derivedPrecomp DN DM f)

end DifferentialGraded.Bimodule

end
