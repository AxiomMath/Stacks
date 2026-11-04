module

public import StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonArrow
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalIdealRestriction

/-!
# The degree `-1` component of the comparison with the naive cotangent complex is a cokernel

Let `f : A ⟶ B` be a homomorphism of sheaves of commutative rings on a site, let `P_•` be the
standard resolution of `B` over `A` and let `I` be the kernel of the augmentation `P₀ ⟶ B`.
The degree `-1` component of the canonical map `L_{B/A} ⟶ NL_{B/A}` of Tag 08US is the arrow

`c : Ω_{P₁/A} ⊗_{P₁} B ⟶ I/I²`,   `d x ⊗ b ↦ b · [d₀ x - d₁ x]`.

This file proves that `c` is a cokernel of the differential `δ₀ - δ₁ + δ₂` of the cotangent
complex into degree `-1`, and that the degree-zero component
`Ω_{P₀/A} ⊗_{P₀} B ⟶ B ⊗_{P₀} Ω_{P₀/A}` of the canonical map is an isomorphism.

## Main definitions

* `CategoryTheory.Sheaf.augLiftOne`: the canonical lift of a local section of `P₁` to `P₂`, the
  degree-one component of the extra degeneracy of the bar resolution on underlying sheaves of
  sets.
* `CategoryTheory.Sheaf.cocycleRestriction`: the map `I ⟶ M` attached to a morphism
  `h : Ω_{P₁/A} ⊗_{P₁} B ⟶ M` killed by `δ₀ - δ₁ + δ₂`, as a restriction datum of the
  presentation `P₀ ⟶ B`.

## Main results

* `CategoryTheory.Sheaf.faceSectionsTwo_zero_augLiftOne`,
  `CategoryTheory.Sheaf.faceSectionsTwo_one_augLiftOne` and
  `CategoryTheory.Sheaf.faceSectionsTwo_two_augLiftOne`: the three faces of the canonical lift.
* `CategoryTheory.Sheaf.derivation_eq_sub_of_cocycle`: an `A`-derivation `D` of `P₁` annihilated
  by the alternating sum of the faces satisfies `D x = D τ(d₀ x) - D τ(d₁ x)`, with `τ` the
  canonical lift `P₀ ⟶ P₁`.
* `CategoryTheory.Sheaf.naiveComparisonNegOne_cancel`: `c` is an epimorphism.
* `CategoryTheory.Sheaf.isColimitNaiveComparisonNegOne`: `c` is a cokernel of `δ₀ - δ₁ + δ₂`.
* `CategoryTheory.Sheaf.isIso_naiveComparisonZero`: the degree-zero component of the canonical
  map is an isomorphism.

## References

* [Stacks Project, Tag 08US](https://stacks.math.columbia.edu/tag/08US)
* [Stacks Project, Tag 08UP](https://stacks.math.columbia.edu/tag/08UP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-! ### The three faces `P₂ ⟶ P₁` and the canonical lift `P₁ ⟶ P₂` -/

/-- The `k`-th face `P₂ ⟶ P₁` is Godement's face of the counit, evaluated at `f`. -/
private theorem delta_two_eq_face (k : Fin 3) :
    (standardResolution J f).left.δ k =
      eqToHom (resObjEq J f 2) ≫
        (Godement.face (standardResolutionComonad J A).ε 2 k).app (Under.mk f) ≫
        eqToHom (resObjEq J f 1).symm := by
  have h2 := NatTrans.congr_app (standardResolutionFunctor_face J A 1 k) (Under.mk f)
  simp only [NatTrans.comp_app, eqToHom_app] at h2
  exact h2

/-- The zeroth face `P₂ ⟶ P₁` is the counit at `P₁`. -/
theorem delta_two_zero_eq :
    (standardResolution J f).left.δ (0 : Fin 3) =
      eqToHom (resObjEq J f 2) ≫
        (standardResolutionComonad J A).ε.app
          ((standardResolutionComonad J A).obj
            ((standardResolutionComonad J A).obj (Under.mk f))) ≫
        eqToHom (resObjEq J f 1).symm := by
  rw [delta_two_eq_face, Godement.Prep.face_zero]
  rfl

/-- The first face `P₂ ⟶ P₁` is the comonad applied to the counit at `P₀`. -/
theorem delta_two_one_eq :
    (standardResolution J f).left.δ (1 : Fin 3) =
      eqToHom (resObjEq J f 2) ≫
        (((standardResolutionComonad J A : Comonad (Under A)) : Under A ⥤ Under A).map
          ((standardResolutionComonad J A).ε.app
            ((standardResolutionComonad J A).obj (Under.mk f)))) ≫
        eqToHom (resObjEq J f 1).symm := by
  rw [delta_two_eq_face]
  rfl

/-- The second face `P₂ ⟶ P₁` is the comonad applied twice to the counit at `B`. -/
theorem delta_two_two_eq :
    (standardResolution J f).left.δ (2 : Fin 3) =
      eqToHom (resObjEq J f 2) ≫
        (((standardResolutionComonad J A : Comonad (Under A)) : Under A ⥤ Under A).map
          ((((standardResolutionComonad J A : Comonad (Under A)) : Under A ⥤ Under A).map
            ((standardResolutionComonad J A).ε.app (Under.mk f))))) ≫
        eqToHom (resObjEq J f 1).symm := by
  rw [delta_two_eq_face]
  rfl

/-- The `k`-th face `P₂ ⟶ P₁` on local sections. -/
noncomputable abbrev faceSectionsTwo (k : Fin 3) (U : Cᵒᵖ)
    (x : (resolutionTerm J f (op ⦋2⦌)).obj.obj U) : (resolutionTerm J f (op ⦋1⦌)).obj.obj U :=
  ((standardResolution J f).left.δ k).right.hom.app U x

/-- The canonical lift of a local section of `P₁` to `P₂`: the variable `[x]` of the free algebra
`P₂ = A[P₁]`. -/
noncomputable def augLiftOne (U : Cᵒᵖ) (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    (resolutionTerm J f (op ⦋2⦌)).obj.obj U :=
  transportSections (resObjEq J f 2).symm U
    (variableSections J
      (((standardResolutionComonad J A : Comonad (Under A)) : Under A ⥤ Under A).obj
        (((standardResolutionComonad J A : Comonad (Under A)) : Under A ⥤ Under A).obj
          (Under.mk f))) U (transportSections (resObjEq J f 1) U x))

/-- A conjugate of a morphism of sheaves of algebras by two transports, on local sections. -/
theorem conj_transportSections {X X' Y Y' : Under A} (hX : X = X') (hY : Y = Y') (g : X' ⟶ Y')
    (U : Cᵒᵖ) (x : X'.right.obj.obj U) :
    (eqToHom hX ≫ g ≫ eqToHom hY.symm).right.hom.app U (transportSections hX.symm U x) =
      transportSections hY.symm U (g.right.hom.app U x) := by
  subst hX
  subst hY
  simp [transportSections]

/-- The zeroth face sends the canonical lift of `x` back to `x`. -/
theorem faceSectionsTwo_zero_augLiftOne (U : Cᵒᵖ)
    (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    faceSectionsTwo J f 0 U (augLiftOne J f U x) = x := by
  rw [faceSectionsTwo, delta_two_zero_eq J f, augLiftOne,
    conj_transportSections J (resObjEq J f 2) (resObjEq J f 1), counit_variableSections]
  exact transportSections_symm _ U x

/-- The zeroth face `P₁ ⟶ P₀`, on local sections, through the iterate of the comonad. -/
theorem faceSections_zero_eq (U : Cᵒᵖ) (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    faceSections J f 0 U x = transportSections (resObjEq J f 0).symm U
      (((standardResolutionComonad J A).ε.app
        ((standardResolutionComonad J A).obj (Under.mk f))).right.hom.app U
          (transportSections (resObjEq J f 1) U x)) := by
  conv_lhs => rw [← transportSections_symm (resObjEq J f 1) U x]
  rw [faceSections, delta_zero_eq J f,
    conj_transportSections J (resObjEq J f 1) (resObjEq J f 0)]

/-- The first face `P₁ ⟶ P₀`, on local sections, through the iterate of the comonad. -/
theorem faceSections_one_eq (U : Cᵒᵖ) (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    faceSections J f 1 U x = transportSections (resObjEq J f 0).symm U
      (((((standardResolutionComonad J A : Comonad (Under A)) : Under A ⥤ Under A).map
        ((standardResolutionComonad J A).ε.app (Under.mk f)))).right.hom.app U
          (transportSections (resObjEq J f 1) U x)) := by
  conv_lhs => rw [← transportSections_symm (resObjEq J f 1) U x]
  rw [faceSections, delta_one_eq J f,
    conj_transportSections J (resObjEq J f 1) (resObjEq J f 0)]

/-- If the `k`-th face `P₂ ⟶ P₁` is the comonad applied to `g : P₂' ⟶ P₁'`, and the `j`-th face
`P₁ ⟶ P₀` is given by `g` on local sections, then the `k`-th face sends the canonical lift of `x`
to the canonical lift of the `j`-th face of `x`. -/
private theorem faceSectionsTwo_augLiftOne_of_eq (k : Fin 3) (j : Fin 2)
    (g : ((standardResolutionComonad J A : Comonad (Under A)) : Under A ⥤ Under A).obj
      (((standardResolutionComonad J A : Comonad (Under A)) : Under A ⥤ Under A).obj
        (Under.mk f)) ⟶
      ((standardResolutionComonad J A : Comonad (Under A)) : Under A ⥤ Under A).obj
        (Under.mk f))
    (hk : (standardResolution J f).left.δ k =
      eqToHom (resObjEq J f 2) ≫
        (((standardResolutionComonad J A : Comonad (Under A)) : Under A ⥤ Under A).map g) ≫
        eqToHom (resObjEq J f 1).symm)
    (U : Cᵒᵖ) (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U)
    (hj : faceSections J f j U x = transportSections (resObjEq J f 0).symm U
      (g.right.hom.app U (transportSections (resObjEq J f 1) U x))) :
    faceSectionsTwo J f k U (augLiftOne J f U x) = augLift J f U (faceSections J f j U x) := by
  rw [faceSectionsTwo, hk, augLiftOne, conj_transportSections J (resObjEq J f 2) (resObjEq J f 1)]
  refine (congrArg (transportSections (resObjEq J f 1).symm U)
    (variableSections_naturality J _ U _)).trans ?_
  rw [augLift, hj, transportSections_symm']
  rfl

/-- The first face sends the canonical lift of `x` to the canonical lift of `d₀ x`. -/
theorem faceSectionsTwo_one_augLiftOne (U : Cᵒᵖ)
    (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    faceSectionsTwo J f 1 U (augLiftOne J f U x) = augLift J f U (faceSections J f 0 U x) :=
  faceSectionsTwo_augLiftOne_of_eq J f 1 0 _ (delta_two_one_eq J f) U x
    (faceSections_zero_eq J f U x)

/-- The second face sends the canonical lift of `x` to the canonical lift of `d₁ x`. -/
theorem faceSectionsTwo_two_augLiftOne (U : Cᵒᵖ)
    (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    faceSectionsTwo J f 2 U (augLiftOne J f U x) = augLift J f U (faceSections J f 1 U x) :=
  faceSectionsTwo_augLiftOne_of_eq J f 2 1 _ (delta_two_two_eq J f) U x
    (faceSections_one_eq J f U x)

/-! ### The canonical lift of a local section of the kernel -/

/-- The degeneracy `P₀ ⟶ P₁` on local sections. -/
noncomputable abbrev degeneracySections (U : Cᵒᵖ)
    (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) : (resolutionTerm J f (op ⦋1⦌)).obj.obj U :=
  ((standardResolution J f).left.σ 0).right.hom.app U p

/-- Both faces send the degeneracy of `p` back to `p`. -/
theorem faceSections_degeneracySections (k : Fin 2) (U : Cᵒᵖ)
    (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    faceSections J f k U (degeneracySections J f U p) = p := by
  fin_cases k
  · exact congrArg (fun t : (standardResolution J f).left.obj (op ⦋0⦌) ⟶
        (standardResolution J f).left.obj (op ⦋0⦌) => t.right.hom.app U p)
      ((standardResolution J f).left.δ_comp_σ_self (n := 0) (i := 0))
  · exact congrArg (fun t : (standardResolution J f).left.obj (op ⦋0⦌) ⟶
        (standardResolution J f).left.obj (op ⦋0⦌) => t.right.hom.app U p)
      ((standardResolution J f).left.δ_comp_σ_succ (n := 0) (i := 0))

/-- The lift `τ p - τ 0` of a local section `p` of `P₀` to `P₁`, with `τ` the canonical lift. -/
noncomputable def kernelLift (U : Cᵒᵖ) (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    (resolutionTerm J f (op ⦋1⦌)).obj.obj U :=
  augLift J f U p - augLift J f U 0

/-- The zeroth face of the lift of `p` is `p`. -/
theorem faceSections_zero_kernelLift (U : Cᵒᵖ) (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    faceSections J f 0 U (kernelLift J f U p) = p := by
  rw [kernelLift, show faceSections J f 0 U (augLift J f U p - augLift J f U 0) =
      faceSections J f 0 U (augLift J f U p) - faceSections J f 0 U (augLift J f U 0) from
    map_sub _ _ _, faceSections_zero_augLift, faceSections_zero_augLift, sub_zero]

/-- The first face of the lift of a local section of the kernel `I` vanishes. -/
theorem faceSections_one_kernelLift (U : Cᵒᵖ) (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U)
    (hp : augSections J f U p = 0) : faceSections J f 1 U (kernelLift J f U p) = 0 := by
  rw [kernelLift, show faceSections J f 1 U (augLift J f U p - augLift J f U 0) =
      faceSections J f 1 U (augLift J f U p) - faceSections J f 1 U (augLift J f U 0) from
    map_sub _ _ _, faceSections_one_augLift, faceSections_one_augLift, hp, augSections_zero,
    sub_self]

/-- Every local section `i` of the kernel `I` is the difference of the two faces of its lift. -/
theorem faceDifference_kernelLift (U : Cᵒᵖ)
    (i : Stacks.Sites.Conormal.kernelIdeal (resolutionAugmentation J f (op ⦋0⦌)).hom U) :
    faceDifference J f U (kernelLift J f U i) = i := by
  refine Subtype.ext ?_
  rw [faceDifference_coe, faceSections_zero_kernelLift,
    faceSections_one_kernelLift J f U _ (RingHom.mem_ker.mp i.2), sub_zero]

/-! ### Derivations of `P₁` annihilated by the alternating sum of the faces -/

section Cocycle

variable {J f} {M : targetModules J B} (D : resolutionDerivations J f (op ⦋1⦌) M)
  (hD : ∀ (U : Cᵒᵖ) (z : (resolutionTerm J f (op ⦋2⦌)).obj.obj U),
    D.d (faceSectionsTwo J f 0 U z) - D.d (faceSectionsTwo J f 1 U z) +
      D.d (faceSectionsTwo J f 2 U z) = 0)

include hD

/-- An `A`-derivation `D` of `P₁` annihilated by `δ₀ - δ₁ + δ₂` satisfies
`D x = D τ(d₀ x) - D τ(d₁ x)`, with `τ` the canonical lift `P₀ ⟶ P₁`. -/
theorem derivation_eq_sub_of_cocycle (U : Cᵒᵖ) (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    D.d x = D.d (augLift J f U (faceSections J f 0 U x)) -
      D.d (augLift J f U (faceSections J f 1 U x)) := by
  have h := hD U (augLiftOne J f U x)
  rw [faceSectionsTwo_zero_augLiftOne, faceSectionsTwo_one_augLiftOne,
    faceSectionsTwo_two_augLiftOne, sub_add] at h
  exact eq_of_sub_eq_zero h

/-- Such a derivation vanishes on a local section of `P₁` whose two faces agree. -/
theorem derivation_eq_zero_of_faceSections_eq (U : Cᵒᵖ)
    (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U)
    (h : faceSections J f 0 U x = faceSections J f 1 U x) : D.d x = 0 := by
  rw [derivation_eq_sub_of_cocycle D hD, h, sub_self]

/-- Such a derivation depends only on the difference of the two faces. -/
theorem derivation_eq_of_faceDifference (U : Cᵒᵖ)
    (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U)
    (i : Stacks.Sites.Conormal.kernelIdeal (resolutionAugmentation J f (op ⦋0⦌)).hom U)
    (h : faceDifference J f U x = i) : D.d x = D.d (kernelLift J f U i) := by
  subst h
  have hx : faceSections J f 0 U (x - kernelLift J f U (faceDifference J f U x)) =
      faceSections J f 1 U (x - kernelLift J f U (faceDifference J f U x)) := by
    rw [show faceSections J f 0 U (x - kernelLift J f U (faceDifference J f U x)) =
        faceSections J f 0 U x - faceSections J f 0 U
          (kernelLift J f U (faceDifference J f U x)) from map_sub _ _ _,
      show faceSections J f 1 U (x - kernelLift J f U (faceDifference J f U x)) =
        faceSections J f 1 U x - faceSections J f 1 U
          (kernelLift J f U (faceDifference J f U x)) from map_sub _ _ _,
      faceSections_zero_kernelLift,
      faceSections_one_kernelLift J f U _ (RingHom.mem_ker.mp (faceDifference J f U x).2),
      faceDifference_coe]
    ring
  simpa only [map_sub, sub_eq_zero] using derivation_eq_zero_of_faceSections_eq D hD U _ hx

/-- The restriction datum `i ↦ D(τ i - τ 0)` of the presentation `P₀ ⟶ B` attached to an
`A`-derivation `D` of `P₁` annihilated by `δ₀ - δ₁ + δ₂`: it is additive, linear over `P₀` acting
through the augmentation, and natural. -/
noncomputable def cocycleRestriction :
    Stacks.Sites.Conormal.IdealRestriction.{v, u, max u v w, u}
      (resolutionAugmentation J f (op ⦋0⦌)) M where
  app U := AddMonoidHom.mk' (fun i => D.d (kernelLift J f U i)) (fun i j => by
    rw [← derivation_eq_of_faceDifference D hD U (kernelLift J f U i + kernelLift J f U j)
      (i + j) (by rw [faceDifference_add, faceDifference_kernelLift, faceDifference_kernelLift])]
    exact map_add _ _ _)
  app_smul U r g := by
    change D.d (kernelLift J f U ((r • g : Stacks.Sites.Conormal.kernelIdeal
      (resolutionAugmentation J f (op ⦋0⦌)).hom U) :
        (resolutionTerm J f (op ⦋0⦌)).obj.obj U)) =
      Stacks.Sites.Conormal.presentationScalar (resolutionAugmentation J f (op ⦋0⦌)) U r •
        (show M.val.obj U from D.d (kernelLift J f U g))
    rw [← derivation_eq_of_faceDifference D hD U
      (degeneracySections J f U r * kernelLift J f U g) (r • g) (by
        rw [faceDifference_mul, faceDifference_kernelLift, faceSections_degeneracySections,
          faceSections_one_kernelLift J f U _ (RingHom.mem_ker.mp g.2), zero_smul, add_zero]),
      D.d_mul, derivation_eq_zero_of_faceSections_eq D hD U (degeneracySections J f U r)
        ((faceSections_degeneracySections J f 0 U r).trans
          (faceSections_degeneracySections J f 1 U r).symm), smul_zero, add_zero]
    exact presheafRestrictScalars_smul (resolutionAugmentation J f (op ⦋1⦌)).hom M.val U
      (degeneracySections J f U r) _
      ((augSections_faceSections J f 0 U (degeneracySections J f U r)).symm.trans
        (congrArg (augSections J f U) (faceSections_degeneracySections J f 0 U r)))
      (D.d (kernelLift J f U g))
  app_map {X Y} g i := by
    refine (derivation_eq_of_faceDifference D hD Y
      ((resolutionTerm J f (op ⦋1⦌)).obj.map g (kernelLift J f X i)) _ (Subtype.ext (by
        rw [faceDifference_map, faceDifference_kernelLift]))).symm.trans ?_
    exact D.d_map g _

/-- The restriction datum takes the difference `d₀ x - d₁ x` of the two faces to `D x`. -/
theorem cocycleRestriction_app_faceDifference (U : Cᵒᵖ)
    (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    (cocycleRestriction D hD).app U (faceDifference J f U x) = D.d x :=
  (derivation_eq_of_faceDifference D hD U x _ rfl).symm

end Cocycle

/-! ### The cokernel -/

variable {M : targetModules J B}

/-- A morphism out of `Ω_{P₁/A} ⊗_{P₁} B` killed by `δ₀ - δ₁ + δ₂` corresponds to an
`A`-derivation of `P₁` annihilated by the alternating sum of the faces. -/
theorem derivationEquiv_cocycle
    (h : (cotangentSimplicialModule J f).object.obj (op ⦋1⦌) ⟶ M)
    (hh : ((cotangentSimplicialModule J f).object.δ (0 : Fin 3) -
        (cotangentSimplicialModule J f).object.δ (1 : Fin 3) +
        (cotangentSimplicialModule J f).object.δ (2 : Fin 3)) ≫ h = 0)
    (U : Cᵒᵖ) (z : (resolutionTerm J f (op ⦋2⦌)).obj.obj U) :
    ((cotangentSimplicialModule J f).derivationEquiv (op ⦋1⦌) M h).d
        (faceSectionsTwo J f 0 U z) -
      ((cotangentSimplicialModule J f).derivationEquiv (op ⦋1⦌) M h).d
        (faceSectionsTwo J f 1 U z) +
      ((cotangentSimplicialModule J f).derivationEquiv (op ⦋1⦌) M h).d
        (faceSectionsTwo J f 2 U z) = 0 := by
  have e (k : Fin 3) : ((cotangentSimplicialModule J f).derivationEquiv (op ⦋1⦌) M h).d
      (faceSectionsTwo J f k U z) =
        ((cotangentSimplicialModule J f).object.δ k ≫ h).val.app U
          (((cotangentSimplicialModule J f).universalDerivation (op ⦋2⦌)).d z) :=
    (derivationEquiv_delta J f 1 M k h U z).symm.trans
      (derivationEquiv_val_app J f (op ⦋2⦌) M _ U z)
  have h0 : (((cotangentSimplicialModule J f).object.δ (0 : Fin 3) -
        (cotangentSimplicialModule J f).object.δ (1 : Fin 3) +
        (cotangentSimplicialModule J f).object.δ (2 : Fin 3)) ≫ h).val.app U
          (((cotangentSimplicialModule J f).universalDerivation (op ⦋2⦌)).d z) = 0 := by
    rw [hh]
    exact zero_val_app J U _
  rw [Preadditive.add_comp, Preadditive.sub_comp] at h0
  refine Eq.trans ?_ h0
  rw [e 0, e 1, e 2]
  exact ((add_val_app J _ _ U _).trans (congrArg (· + _) (sub_val_app J _ _ U _))).symm

/-- The morphism `I/I² ⟶ M` through which a morphism out of `Ω_{P₁/A} ⊗_{P₁} B` killed by
`δ₀ - δ₁ + δ₂` factors. -/
noncomputable def naiveComparisonNegOneDesc
    (h : (cotangentSimplicialModule J f).object.obj (op ⦋1⦌) ⟶ M)
    (hh : ((cotangentSimplicialModule J f).object.δ (0 : Fin 3) -
        (cotangentSimplicialModule J f).object.δ (1 : Fin 3) +
        (cotangentSimplicialModule J f).object.δ (2 : Fin 3)) ≫ h = 0) :
    (naiveSequence J f).X₁ ⟶ M :=
  Stacks.Sites.Conormal.conormalDesc.{v, u, max u v w, u}
    (resolutionAugmentation J f (op ⦋0⦌)) M
    (cocycleRestriction _ (derivationEquiv_cocycle J f h hh))

/-- The factorisation through `I/I²`. -/
theorem naiveComparisonNegOne_comp_desc
    (h : (cotangentSimplicialModule J f).object.obj (op ⦋1⦌) ⟶ M)
    (hh : ((cotangentSimplicialModule J f).object.δ (0 : Fin 3) -
        (cotangentSimplicialModule J f).object.δ (1 : Fin 3) +
        (cotangentSimplicialModule J f).object.δ (2 : Fin 3)) ≫ h = 0) :
    naiveComparisonNegOne J f ≫ naiveComparisonNegOneDesc J f h hh = h := by
  refine hom_ext_of_derivationEquiv J f (op ⦋1⦌) fun U x => ?_
  refine (derivationEquiv_val_app J f (op ⦋1⦌) M _ U x).trans ?_
  show (naiveComparisonNegOneDesc J f h hh).val.app U
      ((naiveComparisonNegOne J f).val.app U
        (((cotangentSimplicialModule J f).universalDerivation (op ⦋1⦌)).d x)) = _
  rw [naiveComparisonNegOne_conormalClass, conormalClassSection]
  exact (Stacks.Sites.Conormal.conormalDesc_conormalClass _ M A (resolutionBase J f (op ⦋0⦌)) _
    U _).trans (cocycleRestriction_app_faceDifference _ _ U x)

/-- Two morphisms out of `I/I²` agreeing after the degree `-1` component of the comparison are
equal. -/
theorem naiveComparisonNegOne_cancel {m₁ m₂ : (naiveSequence J f).X₁ ⟶ M}
    (hm : naiveComparisonNegOne J f ≫ m₁ = naiveComparisonNegOne J f ≫ m₂) : m₁ = m₂ := by
  refine Stacks.Sites.Conormal.conormal_hom_ext.{v, u, max u v w, u}
    (resolutionAugmentation J f (op ⦋0⦌)) M fun U i => ?_
  have key : (naiveComparisonNegOne J f).val.app U
      (((cotangentSimplicialModule J f).universalDerivation (op ⦋1⦌)).d (kernelLift J f U i)) =
        Stacks.Sites.Conormal.toAssociatedModule.{v, u, max u v w, u} J
          (resolutionTerm J f (op ⦋0⦌)) B (resolutionAugmentation J f (op ⦋0⦌))
          (Stacks.Sites.Conormal.conormalPresheaf (resolutionAugmentation J f (op ⦋0⦌)).hom) U
          ((Stacks.Sites.Conormal.kernelIdeal
            (resolutionAugmentation J f (op ⦋0⦌)).hom U).toCotangent i) := by
    rw [naiveComparisonNegOne_conormalClass, faceDifference_kernelLift]
    rfl
  rw [← key]
  exact congrArg (fun t => t.val.app U
    (((cotangentSimplicialModule J f).universalDerivation (op ⦋1⦌)).d (kernelLift J f U i))) hm

/-- The degree `-1` component of the comparison is an epimorphism. -/
instance naiveComparisonNegOne_epi : Epi (naiveComparisonNegOne J f) :=
  ⟨fun _ _ h => naiveComparisonNegOne_cancel J f h⟩

/-- **The degree `-1` component of the comparison is a cokernel.** The arrow
`Ω_{P₁/A} ⊗_{P₁} B ⟶ I/I²`, `d x ⊗ b ↦ b · [d₀ x - d₁ x]`, is a cokernel of the alternating sum
`δ₀ - δ₁ + δ₂` of the three faces `Ω_{P₂/A} ⊗_{P₂} B ⟶ Ω_{P₁/A} ⊗_{P₁} B`. -/
noncomputable def isColimitNaiveComparisonNegOne :
    IsColimit (CokernelCofork.ofπ (naiveComparisonNegOne J f)
      (naiveComparisonNegOne_faceSum J f)) :=
  CokernelCofork.IsColimit.ofπ _ _ (fun h hh => naiveComparisonNegOneDesc J f h hh)
    (fun h hh => naiveComparisonNegOne_comp_desc J f h hh)
    (fun h hh m hm => naiveComparisonNegOne_cancel J f
      (hm.trans (naiveComparisonNegOne_comp_desc J f h hh).symm))

/-! ### The degree-zero component is an isomorphism -/

/-- The morphism of `P₀`-modules `Ω_{P₀/A} ⟶ Ω_{P₀/A} ⊗_{P₀} B` classifying the universal
derivation of the base-changed differentials in simplicial degree zero. -/
noncomputable def differentialsToCotangentZero :
    AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite.{v, u, max u v w, u} A
        (resolutionTerm J f (op ⦋0⦌)) (resolutionBase J f (op ⦋0⦌)) ⟶
      (SheafOfModules.pushforward
        (Stacks.Sites.Conormal.underlyingRingHomForPullback J (resolutionTerm J f (op ⦋0⦌)) B
          (resolutionAugmentation J f (op ⦋0⦌)))).obj
        ((cotangentSimplicialModule J f).object.obj (op ⦋0⦌)) :=
  Classical.choose (AlgebraicGeometry.SheafOfModules.existsUnique_descDerivation.{v, u,
    max u v w, u} A (resolutionTerm J f (op ⦋0⦌)) (resolutionBase J f (op ⦋0⦌))
    ((SheafOfModules.pushforward
      (Stacks.Sites.Conormal.underlyingRingHomForPullback J (resolutionTerm J f (op ⦋0⦌)) B
        (resolutionAugmentation J f (op ⦋0⦌)))).obj
      ((cotangentSimplicialModule J f).object.obj (op ⦋0⦌)))
    ((cotangentSimplicialModule J f).universalDerivation (op ⦋0⦌)))

/-- `differentialsToCotangentZero` sends the universal differential `d p` to `d p ⊗ 1`. -/
theorem differentialsToCotangentZero_d (U : Cᵒᵖ) (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    (differentialsToCotangentZero J f).val.app U
        ((AlgebraicGeometry.SheafOfModules.universalDerivationOfSite.{v, u, max u v w, u} A
          (resolutionTerm J f (op ⦋0⦌)) (resolutionBase J f (op ⦋0⦌))).d p) =
      ((cotangentSimplicialModule J f).universalDerivation (op ⦋0⦌)).d p :=
  congrArg (fun D : resolutionDerivations J f (op ⦋0⦌)
      ((cotangentSimplicialModule J f).object.obj (op ⦋0⦌)) => D.d (X := U) p)
    (Classical.choose_spec (AlgebraicGeometry.SheafOfModules.existsUnique_descDerivation.{v, u,
      max u v w, u} A (resolutionTerm J f (op ⦋0⦌)) (resolutionBase J f (op ⦋0⦌))
      ((SheafOfModules.pushforward
        (Stacks.Sites.Conormal.underlyingRingHomForPullback J (resolutionTerm J f (op ⦋0⦌)) B
          (resolutionAugmentation J f (op ⦋0⦌)))).obj
        ((cotangentSimplicialModule J f).object.obj (op ⦋0⦌)))
      ((cotangentSimplicialModule J f).universalDerivation (op ⦋0⦌)))).1

/-- The morphism `B ⊗_{P₀} Ω_{P₀/A} ⟶ Ω_{P₀/A} ⊗_{P₀} B`, `b ⊗ d p ↦ d p ⊗ b`, back from the
middle term of the conormal sequence: the extension of scalars of
`CategoryTheory.Sheaf.differentialsToCotangentZero`. -/
noncomputable def naiveComparisonZeroInv :
    (naiveSequence J f).X₂ ⟶ (cotangentSimplicialModule J f).object.obj (op ⦋0⦌) :=
  (Stacks.Sites.Conormal.tensorDifferentialsIso.{v, u, max u v w, u} J A
      (resolutionTerm J f (op ⦋0⦌)) B (resolutionBase J f (op ⦋0⦌))
      (resolutionAugmentation J f (op ⦋0⦌))).hom ≫
    ((SheafOfModules.pullbackPushforwardAdjunction
      (Stacks.Sites.Conormal.underlyingRingHomForPullback J (resolutionTerm J f (op ⦋0⦌)) B
        (resolutionAugmentation J f (op ⦋0⦌)))).homEquiv _ _).symm
      (differentialsToCotangentZero J f)

/-- The inverse sends `1 ⊗ d p` to `d p ⊗ 1`. -/
theorem naiveComparisonZeroInv_tensorDifferential (U : Cᵒᵖ)
    (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    (naiveComparisonZeroInv J f).val.app U (tensorDifferentialSections J f U p) =
      ((cotangentSimplicialModule J f).universalDerivation (op ⦋0⦌)).d p := by
  have hunit := ((SheafOfModules.pullbackPushforwardAdjunction
      (Stacks.Sites.Conormal.underlyingRingHomForPullback J (resolutionTerm J f (op ⦋0⦌)) B
        (resolutionAugmentation J f (op ⦋0⦌)))).homEquiv_unit _ _
      (((SheafOfModules.pullbackPushforwardAdjunction
        (Stacks.Sites.Conormal.underlyingRingHomForPullback J (resolutionTerm J f (op ⦋0⦌)) B
          (resolutionAugmentation J f (op ⦋0⦌)))).homEquiv _ _).symm
        (differentialsToCotangentZero J f))).symm.trans (Equiv.apply_symm_apply _ _)
  show (((SheafOfModules.pullbackPushforwardAdjunction
      (Stacks.Sites.Conormal.underlyingRingHomForPullback J (resolutionTerm J f (op ⦋0⦌)) B
        (resolutionAugmentation J f (op ⦋0⦌)))).homEquiv _ _).symm
      (differentialsToCotangentZero J f)).val.app U
      ((Stacks.Sites.Conormal.tensorDifferentialsIso.{v, u, max u v w, u} J A
        (resolutionTerm J f (op ⦋0⦌)) B (resolutionBase J f (op ⦋0⦌))
        (resolutionAugmentation J f (op ⦋0⦌))).hom.val.app U
          (tensorDifferentialSections J f U p)) = _
  rw [Stacks.Sites.Conormal.tensorDifferentialsIso_d.{v, u, max u v w, u} J A
      (resolutionTerm J f (op ⦋0⦌)) B (resolutionBase J f (op ⦋0⦌))
      (resolutionAugmentation J f (op ⦋0⦌)) U p]
  exact (congrArg (fun t => t.val.app U
    ((AlgebraicGeometry.SheafOfModules.universalDerivationOfSite.{v, u, max u v w, u} A
      (resolutionTerm J f (op ⦋0⦌)) (resolutionBase J f (op ⦋0⦌))).d p)) hunit).trans
    (differentialsToCotangentZero_d J f U p)

/-- The degree-zero component of the comparison, `d p ⊗ b ↦ b ⊗ d p`, is an isomorphism. -/
instance isIso_naiveComparisonZero : IsIso (naiveComparisonZero J f) := by
  refine ⟨naiveComparisonZeroInv J f, ?_, ?_⟩
  · refine hom_ext_of_derivationEquiv J f (op ⦋0⦌) fun U p => ?_
    refine (derivationEquiv_val_app J f (op ⦋0⦌) _ _ U p).trans ?_
    refine Eq.trans ?_ (derivationEquiv_val_app J f (op ⦋0⦌) _ _ U p).symm
    change (naiveComparisonZeroInv J f).val.app U ((naiveComparisonZero J f).val.app U
      (((cotangentSimplicialModule J f).universalDerivation (op ⦋0⦌)).d p)) =
        ((cotangentSimplicialModule J f).universalDerivation (op ⦋0⦌)).d p
    rw [← derivationEquiv_val_app, derivationEquiv_naiveComparisonZero,
      naiveComparisonZeroInv_tensorDifferential]
  · refine Stacks.Sites.Conormal.tensorSheaf_hom_ext.{v, u, max u v w, u} J A
      (resolutionTerm J f (op ⦋0⦌)) B (resolutionBase J f (op ⦋0⦌))
      (resolutionAugmentation J f (op ⦋0⦌)) _ fun U p => ?_
    change (naiveComparisonZero J f).val.app U ((naiveComparisonZeroInv J f).val.app U
      (tensorDifferentialSections J f U p)) = tensorDifferentialSections J f U p
    rw [naiveComparisonZeroInv_tensorDifferential, ← derivationEquiv_val_app,
      derivationEquiv_naiveComparisonZero]

end CategoryTheory.Sheaf

end
