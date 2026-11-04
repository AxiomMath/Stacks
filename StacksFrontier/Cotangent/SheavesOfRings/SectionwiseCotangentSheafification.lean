module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsSheafification
public import StacksFrontier.Cotangent.SheavesOfRings.ResolutionSectionsLocalIso
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseCotangentModules

/-!
# The base-changed differentials of `A ⟶ B` are the sheafification of the sectionwise ones

Let `A ⟶ B` be a homomorphism of sheaves of commutative rings on a site. In simplicial degree
`n` the cotangent complex of `A ⟶ B` has the base-changed sheaf of differentials
`Ω_{P_n/A} ⊗_{P_n} B` of the standard resolution of `A ⟶ B`, while the sectionwise cotangent
complex of Tag 08SW has, over an object `U` of the site, the base-changed module
`Ω_{P'_n(U)/A(U)} ⊗_{P'_n(U)} B(U)` of the standard resolution of `A(U) → B(U)`. This file proves
that the first is the sheafification of the second.

## Main definitions

* `CategoryTheory.Sheaf.sheafifiedSectionwiseModules`: the sheaf of `B`-modules associated to
  the degree-`-n` term of the sectionwise cotangent complex.
* `CategoryTheory.Sheaf.resolutionDerivationsEquiv`: restricting an `A`-derivation of the sheaf
  `P_n` along the comparison `P'_n ⟶ P_n` is a bijection onto the `A`-derivations of the
  presheaf `P'_n`.
* `CategoryTheory.Sheaf.cotangentTermSheafifiedComparison` and
  `CategoryTheory.Sheaf.cotangentTermSheafifiedIso`: the comparison and **the isomorphism**
  `(L_{B(•)/A(•)}^{-n})^# ≅ Ω_{P_n/A} ⊗_{P_n} B`.

## Main results

* `CategoryTheory.Sheaf.sectionsResolutionComparison_eq`: the comparison of standard resolutions
  of Tag 08SX, in degree `n`, is the comparison `CategoryTheory.Sheaf.towerComparison` of the
  stage-`n + 1` towers, conjugated by the two identifications of a resolution term with a tower
  stage.
* `CategoryTheory.Sheaf.W_sectionsResolutionComparison`: consequently **the comparison
  `P'_n ⟶ P_n` is inverted by sheafification**, and so is locally injective and locally
  surjective.
* `CategoryTheory.Sheaf.isIso_cotangentTermSheafifiedComparison`: the comparison
  `(L_{B(•)/A(•)}^{-n})^# ⟶ Ω_{P_n/A} ⊗_{P_n} B` is an isomorphism.

## References

* [Stacks Project, Tag 08SW](https://stacks.math.columbia.edu/tag/08SW)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08TP](https://stacks.math.columbia.edu/tag/08TP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

attribute [local instance] moduleOfSections

/-! ## The comparison of standard resolutions is the comparison of towers -/

/-- Transport of a sheaf of `A`-algebras along an equality, on sections over an object of the
site, is the transport of its sections. -/
theorem sectionsAlgebraFunctor_map_eqToHom (U : Cᵒᵖ) {X Y : Under A} (hXY : X = Y)
    (x : (sectionsAlgebraFunctor J U (A := A)).obj X) :
    ((sectionsAlgebraFunctor J U).map (eqToHom hXY)).hom x =
      (eqToHom (congrArg (fun Z : Under A => Z.right.obj) hXY)).app U x := by
  subst hXY
  rfl

/-- The degree-`n` term of the standard resolution of `A(U) → B(U)` is the stage `n + 1` of the
tower of iterated polynomial algebras, as presheaves of commutative rings on the site. -/
noncomputable def sectionsResolutionTowerHom (n : ℕ) :
    sectionsResolutionPresheaf J f (op ⦋n⦌) ⟶ towerPresheaf J f (n + 1) where
  app U := CommRingCat.ofHom
    (eqToHom (CommAlgCat.standardResolution_obj_eq_standardTower.{max u v w, max u v w}
      (A.obj.obj U) (sectionsAlgebra J f U) n)).hom.toRingHom
  naturality U V g := by
    refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
    refine Eq.trans ?_ (CommAlgCat.eqToHom_eqToHom_apply.{max u v w, max u v w}
      (CommAlgCat.standardResolution_obj_eq_standardTower.{max u v w, max u v w}
        (A.obj.obj V) (sectionsAlgebra J f V) n).symm
      (CommAlgCat.standardResolution_obj_eq_standardTower.{max u v w, max u v w}
        (A.obj.obj V) (sectionsAlgebra J f V) n) _)
    exact congrArg (fun z => (eqToHom
        (CommAlgCat.standardResolution_obj_eq_standardTower.{max u v w, max u v w}
          (A.obj.obj V) (sectionsAlgebra J f V) n)) z)
      (CommAlgCat.standardResolutionSquareMap_apply.{max u v w, max u v w, max u v w}
        (sectionsRestrictionSquare J f g) n p)

/-- On each object of the site, the identification of a resolution term with a tower stage is an
isomorphism of commutative rings. -/
instance isIso_sectionsResolutionTowerHom_app (n : ℕ) (U : Cᵒᵖ) :
    IsIso ((sectionsResolutionTowerHom J f n).app U) :=
  ⟨⟨CommRingCat.ofHom
      (eqToHom (CommAlgCat.standardResolution_obj_eq_standardTower.{max u v w, max u v w}
        (A.obj.obj U) (sectionsAlgebra J f U) n).symm).hom.toRingHom,
    CommRingCat.hom_ext (RingHom.ext fun p =>
      CommAlgCat.eqToHom_eqToHom_apply.{max u v w, max u v w} _ _ p),
    CommRingCat.hom_ext (RingHom.ext fun p =>
      CommAlgCat.eqToHom_eqToHom_apply.{max u v w, max u v w} _ _ p)⟩⟩

/-- The identification of the degree-`n` resolution term with the stage `n + 1` of the tower is an
isomorphism of presheaves of rings. -/
instance isIso_sectionsResolutionTowerHom (n : ℕ) :
    IsIso (sectionsResolutionTowerHom J f n) :=
  NatIso.isIso_of_isIso_app _

/-- The stage `n + 1` of the tower of free algebra sheaves is the degree-`n` term of the
standard resolution of `A ⟶ B`, on underlying presheaves of rings. -/
noncomputable def sectionsTowerTermIso (n : ℕ) :
    (sheafTower J f (n + 1)).right.obj ≅ (resolutionTerm J f (op ⦋n⦌)).obj :=
  eqToIso (congrArg (fun Z : Under A => Z.right.obj)
    (standardResolution_obj.{v, u, w} J f n).symm)

/-- **The comparison of standard resolutions of Tag 08SX is the comparison of towers**,
conjugated by the two identifications of a resolution term with a tower stage. -/
theorem sectionsResolutionComparison_eq (n : ℕ) :
    sectionsResolutionComparison J f (op ⦋n⦌) =
      sectionsResolutionTowerHom J f n ≫ towerComparison J f (n + 1) ≫
        (sectionsTowerTermIso J f n).hom := by
  refine NatTrans.ext (funext fun U => CommRingCat.hom_ext (RingHom.ext fun p => ?_))
  exact (resolutionSectionsComparisonApp_apply J f U n p).trans
    (sectionsAlgebraFunctor_map_eqToHom J U (standardResolution_obj.{v, u, w} J f n).symm _)

/-- **The comparison `P'_n ⟶ P_n` of Tag 08SX is inverted by sheafification.** -/
theorem W_sectionsResolutionComparison (n : ℕ) :
    J.W (sectionsResolutionComparison J f (op ⦋n⦌)) := by
  rw [sectionsResolutionComparison_eq, J.W_iff, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- The comparison `P'_n ⟶ P_n` is locally injective. -/
instance isLocallyInjective_sectionsResolutionComparison (n : ℕ) :
    Presheaf.IsLocallyInjective J (sectionsResolutionComparison J f (op ⦋n⦌)) :=
  (W_sectionsResolutionComparison J f n).isLocallyInjective

/-- The comparison `P'_n ⟶ P_n` is locally surjective. -/
instance isLocallySurjective_sectionsResolutionComparison (n : ℕ) :
    Presheaf.IsLocallySurjective J (sectionsResolutionComparison J f (op ⦋n⦌)) :=
  (W_sectionsResolutionComparison J f n).isLocallySurjective

/-- The augmentation of the standard resolution of `A(U) → B(U)` is the augmentation of the
standard resolution of `A ⟶ B` read through the comparison. -/
theorem resolutionAugmentation_sectionsResolutionComparison (i : SimplexCategoryᵒᵖ) (U : Cᵒᵖ)
    (p : (sectionsResolutionPresheaf J f i).obj U) :
    (resolutionAugmentation J f i).hom.app U
        (((sectionsResolutionComparison J f i).app U).hom p) =
      ((sectionsResolutionAugmentation J f i).app U).hom p :=
  resolutionAugmentation_resolutionSectionsComparison J f U i p

/-! ## Descent of derivations along the comparison -/

/-- Restricting an `A`-derivation of the sheaf `P_n` along the comparison `P'_n ⟶ P_n` gives an
`A`-derivation of the presheaf `P'_n`. -/
noncomputable def restrictResolutionDerivation (n : ℕ) (M : targetModules J B)
    (D : resolutionDerivations J f (op ⦋n⦌) M) :
    sectionsResolutionDerivations J f (op ⦋n⦌) M where
  d {U} := (D.d (X := U)).comp
    ((sectionsResolutionComparison J f (op ⦋n⦌)).app U).hom.toAddMonoidHom
  d_mul {U} x y := by
    change D.d (((sectionsResolutionComparison J f (op ⦋n⦌)).app U).hom (x * y)) =
      ((sectionsResolutionAugmentation J f (op ⦋n⦌)).app U).hom x •
          (show M.val.obj U from
            D.d (((sectionsResolutionComparison J f (op ⦋n⦌)).app U).hom y)) +
        ((sectionsResolutionAugmentation J f (op ⦋n⦌)).app U).hom y •
          (show M.val.obj U from
            D.d (((sectionsResolutionComparison J f (op ⦋n⦌)).app U).hom x))
    rw [map_mul ((sectionsResolutionComparison J f (op ⦋n⦌)).app U).hom, D.d_mul]
    change (resolutionAugmentation J f (op ⦋n⦌)).hom.app U
            (((sectionsResolutionComparison J f (op ⦋n⦌)).app U).hom x) •
          (show M.val.obj U from
            D.d (((sectionsResolutionComparison J f (op ⦋n⦌)).app U).hom y)) +
        (resolutionAugmentation J f (op ⦋n⦌)).hom.app U
            (((sectionsResolutionComparison J f (op ⦋n⦌)).app U).hom y) •
          (show M.val.obj U from
            D.d (((sectionsResolutionComparison J f (op ⦋n⦌)).app U).hom x)) = _
    rw [resolutionAugmentation_sectionsResolutionComparison,
      resolutionAugmentation_sectionsResolutionComparison]
  d_map {U V} g x :=
    (congrArg D.d (NatTrans.naturality_apply (sectionsResolutionComparison J f (op ⦋n⦌))
      g x)).trans (D.d_map g _)
  d_app {U} a :=
    (congrArg D.d
      (congrArg (fun k : A.obj ⟶ (resolutionTerm J f (op ⦋n⦌)).obj => (k.app U).hom a)
        (sectionsResolutionBase_comp_comparison J f (op ⦋n⦌)))).trans (D.d_app a)

/-- The restriction of a derivation `D` of `P_n` sends a section `p` of `P'_n` to `D` applied to
the image of `p` under the comparison. -/
@[simp]
theorem restrictResolutionDerivation_d (n : ℕ) (M : targetModules J B)
    (D : resolutionDerivations J f (op ⦋n⦌) M) (U : Cᵒᵖ)
    (p : (sectionsResolutionPresheaf J f (op ⦋n⦌)).obj U) :
    (restrictResolutionDerivation J f n M D).d p =
      D.d (((sectionsResolutionComparison J f (op ⦋n⦌)).app U).hom p) :=
  rfl

/-- **Every `A`-derivation of the presheaf `P'_n` extends uniquely to the sheaf `P_n`**, the
comparison `P'_n ⟶ P_n` being locally bijective. -/
theorem existsUnique_resolutionDerivation (n : ℕ) (M : targetModules J B)
    (d : sectionsResolutionDerivations J f (op ⦋n⦌) M) :
    ∃! D : resolutionDerivations J f (op ⦋n⦌) M,
      ∀ (U : Cᵒᵖ) (p : (sectionsResolutionPresheaf J f (op ⦋n⦌)).obj U),
        D.d (((sectionsResolutionComparison J f (op ⦋n⦌)).app U).hom p) = d.d p := by
  have : Presheaf.IsLocallySurjective J (𝟙 A.obj) :=
    Presheaf.isLocallySurjective_of_surjective J _ fun _ x => ⟨x, rfl⟩
  exact AlgebraicGeometry.SheafOfModules.existsUnique_derivation_extension.{max u v w} J
    (sectionsResolutionComparison J f (op ⦋n⦌)) (sectionsResolutionBase J f (op ⦋n⦌))
    (resolutionBase J f (op ⦋n⦌)).hom (𝟙 A.obj)
    (fun U s => congrArg
      (fun k : A.obj ⟶ (resolutionTerm J f (op ⦋n⦌)).obj => (k.app U).hom s)
      (sectionsResolutionBase_comp_comparison J f (op ⦋n⦌)))
    (M := ((SheafOfModules.restrictScalars
      (resolutionAugmentationRing J f (op ⦋n⦌))).obj M).val)
    ((SheafOfModules.restrictScalars (resolutionAugmentationRing J f (op ⦋n⦌))).obj M).isSheaf
    (fun {_} => d.d)
    (fun {U} x y => by
      show d.d (x * y) =
        (resolutionAugmentation J f (op ⦋n⦌)).hom.app U
            (((sectionsResolutionComparison J f (op ⦋n⦌)).app U).hom x) •
          (show M.val.obj U from d.d y) +
        (resolutionAugmentation J f (op ⦋n⦌)).hom.app U
            (((sectionsResolutionComparison J f (op ⦋n⦌)).app U).hom y) •
          (show M.val.obj U from d.d x)
      rw [resolutionAugmentation_sectionsResolutionComparison,
        resolutionAugmentation_sectionsResolutionComparison]
      exact d.d_mul x y)
    (fun g x => d.d_map g x) (fun s => d.d_app s)

/-- **Restriction along the comparison `P'_n ⟶ P_n` is a bijection on derivations.** The
`A`-derivations of the sheaf `P_n` with values in a sheaf of `B`-modules are exactly the
`A`-derivations of the presheaf `P'_n` with values in it. -/
noncomputable def resolutionDerivationsEquiv (n : ℕ) (M : targetModules J B) :
    resolutionDerivations J f (op ⦋n⦌) M ≃ sectionsResolutionDerivations J f (op ⦋n⦌) M where
  toFun := restrictResolutionDerivation J f n M
  invFun d := (existsUnique_resolutionDerivation J f n M d).choose
  left_inv D :=
    ((existsUnique_resolutionDerivation J f n M
      (restrictResolutionDerivation J f n M D)).choose_spec.2 D fun _ _ => rfl).symm
  right_inv d :=
    PresheafOfModules.Derivation.ext (funext fun U => AddMonoidHom.ext fun p =>
      (existsUnique_resolutionDerivation J f n M d).choose_spec.1 U p)

/-! ## The sheafification of the sectionwise base-changed differentials -/

/-- Sheafification of presheaves of `B`-modules. -/
noncomputable abbrev moduleSheafification :
    PresheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj ⥤
      targetModules J B :=
  PresheafOfModules.sheafification
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)

/-- The sheaf of `B`-modules associated to the degree-`-n` term of the sectionwise cotangent
complex. -/
noncomputable abbrev sheafifiedSectionwiseModules (n : ℕ) : targetModules J B :=
  (moduleSheafification J (B := B)).obj (sectionwiseCotangentModules J f (-(n : ℤ)))

/-- Morphisms out of the sheafification of the degree-`-n` term of the sectionwise cotangent
complex are the `A`-derivations of the presheaf `P'_n`. -/
noncomputable def sheafifiedSectionwiseModulesHomEquiv (n : ℕ) (M : targetModules J B) :
    (sheafifiedSectionwiseModules J f n ⟶ M) ≃ sectionsResolutionDerivations J f (op ⦋n⦌) M :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).homEquiv
    (sectionwiseCotangentModules J f (-(n : ℤ))) M).trans
    (sectionwiseCotangentModulesHomEquiv J f n M)

/-- The derivation attached to a composite `k ≫ h` is the derivation attached to `k` followed
by `h`. -/
theorem sheafifiedSectionwiseModulesHomEquiv_d (n : ℕ) {M N : targetModules J B}
    (k : sheafifiedSectionwiseModules J f n ⟶ M) (h : M ⟶ N) (U : Cᵒᵖ)
    (p : (sectionsResolutionPresheaf J f (op ⦋n⦌)).obj U) :
    (sheafifiedSectionwiseModulesHomEquiv J f n N (k ≫ h)).d p =
      h.val.app U ((sheafifiedSectionwiseModulesHomEquiv J f n M k).d p) :=
  congrArg (fun φ => (φ.app U).hom (sectionwiseDifferential J f n U p))
    (Adjunction.homEquiv_naturality_right
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)) k h)

/-- Morphisms out of the base-changed differentials `Ω_{P_n/A} ⊗_{P_n} B` of `A ⟶ B` correspond to
morphisms out of the sheafification of the sectionwise base-changed differentials. -/
noncomputable def cotangentTermSheafifiedHomEquiv (n : ℕ) (M : targetModules J B) :
    ((cotangentSimplicialModule J f).object.obj (op ⦋n⦌) ⟶ M) ≃
      (sheafifiedSectionwiseModules J f n ⟶ M) :=
  ((cotangentSimplicialModule J f).derivationEquiv (op ⦋n⦌) M).trans
    ((resolutionDerivationsEquiv J f n M).trans
      (sheafifiedSectionwiseModulesHomEquiv J f n M).symm)

/-- The canonical map from the sheafification of the sectionwise base-changed differentials. -/
noncomputable def cotangentTermSheafifiedComparison (n : ℕ) :
    sheafifiedSectionwiseModules J f n ⟶
      (cotangentSimplicialModule J f).object.obj (op ⦋n⦌) :=
  cotangentTermSheafifiedHomEquiv J f n _ (𝟙 _)

/-- `cotangentTermSheafifiedHomEquiv` is natural in the target module: it commutes with
postcomposition by a morphism `h : M ⟶ N`. -/
theorem cotangentTermSheafifiedHomEquiv_comp (n : ℕ) {M N : targetModules J B}
    (g : (cotangentSimplicialModule J f).object.obj (op ⦋n⦌) ⟶ M) (h : M ⟶ N) :
    cotangentTermSheafifiedHomEquiv J f n N (g ≫ h) =
      cotangentTermSheafifiedHomEquiv J f n M g ≫ h := by
  apply (sheafifiedSectionwiseModulesHomEquiv J f n N).injective
  dsimp only [cotangentTermSheafifiedHomEquiv, Equiv.trans_apply]
  rw [Equiv.apply_symm_apply]
  refine PresheafOfModules.Derivation.ext (funext fun U => AddMonoidHom.ext fun p => ?_)
  rw [sheafifiedSectionwiseModulesHomEquiv_d, Equiv.apply_symm_apply]
  exact congrArg (fun D : resolutionDerivations J f (op ⦋n⦌) N =>
      D.d (((sectionsResolutionComparison J f (op ⦋n⦌)).app U).hom p))
    ((cotangentSimplicialModule J f).naturality (op ⦋n⦌) g h)

/-- The comparison `(L_{B(•)/A(•)}^{-n})^# ⟶ Ω_{P_n/A} ⊗_{P_n} B` is an isomorphism. -/
instance isIso_cotangentTermSheafifiedComparison (n : ℕ) :
    IsIso (cotangentTermSheafifiedComparison J f n) := by
  apply isIso_of_coyoneda_map_bijective
  intro M
  have h : (fun k : (cotangentSimplicialModule J f).object.obj (op ⦋n⦌) ⟶ M =>
        cotangentTermSheafifiedComparison J f n ≫ k) =
      fun k => cotangentTermSheafifiedHomEquiv J f n M k := by
    funext k
    exact (cotangentTermSheafifiedHomEquiv_comp J f n (𝟙 _) k).symm.trans
      (congrArg (cotangentTermSheafifiedHomEquiv J f n M) (Category.id_comp k))
  rw [h]
  exact (cotangentTermSheafifiedHomEquiv J f n M).bijective

/-- The base-changed sheaf of differentials `Ω_{P_n/A} ⊗_{P_n} B` in simplicial degree `n` of the
cotangent complex of `A ⟶ B` is the sheafification of the presheaf of base-changed modules
`U ↦ Ω_{P'_n(U)/A(U)} ⊗_{P'_n(U)} B(U)` of the standard resolutions of the section maps. -/
noncomputable def cotangentTermSheafifiedIso (n : ℕ) :
    sheafifiedSectionwiseModules J f n ≅
      (cotangentSimplicialModule J f).object.obj (op ⦋n⦌) :=
  asIso (cotangentTermSheafifiedComparison J f n)

end CategoryTheory.Sheaf

end
