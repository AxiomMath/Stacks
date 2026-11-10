module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionTwistCompat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleBaseChangeAbIntegral
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars
public import StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategories
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleExtForgetPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting

/-!
# Base change of a direct image of sheaves of modules along an integral morphism

Let
```
Z' --g'--> Z
|i'        |i
v          v
X' --g---> X
```
be a cartesian square of schemes with `i` integral (for instance finite) and `Λ` a ring.  The
base change map `g^{-1} i_* M ⟶ i'_* g'^{-1} M` of
`Stacks.EtaleCohomology.etaleModuleBaseChange` is an isomorphism for every sheaf `M` of
`Λ`-modules on `Z_étale` ([Stacks, Tag 0959], [Stacks, Tag 0EYP]).

## Main results

* `Stacks.EtaleCohomology.etaleModuleBaseChange_eq_mateEquiv_symm`: the base change map is the
  mate, along the adjunctions `g^{-1} ⊣ g_*` and `g'^{-1} ⊣ g'_*`, of the comparison of the two
  composite direct images around the square.
* `Stacks.EtaleCohomology.isIso_etaleModuleBaseChange_of_isIntegralHom`: for `i` integral the
  base change map is an isomorphism.

## References

* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.CategoryTheory.BaseChange

variable {A : Type*} {B : Type*} {A' : Type*} {B' : Type*}
  [Category* A] [Category* B] [Category* A'] [Category* B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'} {Lg : A ⥤ A'} {Rg : A' ⥤ A}
  {Lg' : B ⥤ B'} {Rg' : B' ⥤ B} {Lc : A ⥤ B'} {Rc : B' ⥤ A}

/-- If the two comparisons of composite left adjoints are conjugate to comparisons `df`, `dg` of
composite right adjoints, then the mate along the vertical adjunctions is the mate along the
horizontal adjunctions of `df ≫ dg⁻¹`. -/
theorem twoSquare_eq_mateEquiv_symm (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (adjg : Lg ⊣ Rg)
    (adjg' : Lg' ⊣ Rg') (adjc : Lc ⊣ Rc) (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
    (dg : Rf' ⋙ Rg ≅ Rc) (df : Rg' ⋙ Rf ≅ Rc)
    (hg : conjugateEquiv adjc (adjg.comp adjf') eg.hom = dg.inv)
    (hf : conjugateEquiv (adjf.comp adjg') adjc ef.inv = df.hom) :
    twoSquare adjf adjf' eg ef =
      (mateEquiv adjg' adjg).symm (TwoSquare.mk _ _ _ _ (df.hom ≫ dg.inv)) := by
  refine (Equiv.eq_symm_apply _).2 ?_
  refine (iterated_mateEquiv_conjugateEquiv adjf adjf' adjg adjg' _).trans ?_
  change conjugateEquiv (adjf.comp adjg') (adjg.comp adjf') (eg.hom ≫ ef.inv) = df.hom ≫ dg.inv
  rw [← conjugateEquiv_comp _ adjc, hf, hg]

end Stacks.CategoryTheory.BaseChange

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-- The composition isomorphism of the inverse images, precomposed with `eqToHom`, is conjugate
to the composition isomorphism of the direct images. -/
theorem conjugateEquiv_eqToHom_comp_etaleModuleInverseImageCompIso_hom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (h : fg = f ≫ g) :
    conjugateEquiv ((etaleModuleInverseImageAdj.{u, r} Λ g).comp
        (etaleModuleInverseImageAdj.{u, r} Λ f)) (etaleModuleInverseImageAdj.{u, r} Λ fg)
        (eqToHom (congrArg (fun m => etaleModuleInverseImage.{u, r} Λ m) h) ≫
          (etaleModuleInverseImageCompIso.{u, r} Λ f g).hom) =
      (etaleModuleDirectImageComp.{u, r} Λ f g fg h).hom := by
  subst h
  rw [eqToHom_refl, Category.id_comp]
  have h1 := conjugateEquiv_etaleModuleInverseImageCompIso_inv.{u, r} Λ f g
  have h2 := conjugateEquiv_comp ((etaleModuleInverseImageAdj.{u, r} Λ g).comp
      (etaleModuleInverseImageAdj.{u, r} Λ f)) (etaleModuleInverseImageAdj.{u, r} Λ (f ≫ g))
    ((etaleModuleInverseImageAdj.{u, r} Λ g).comp (etaleModuleInverseImageAdj.{u, r} Λ f))
    (etaleModuleInverseImageCompIso.{u, r} Λ f g).hom
    (etaleModuleInverseImageCompIso.{u, r} Λ f g).inv
  rw [Iso.inv_hom_id, conjugateEquiv_id, h1] at h2
  exact (Iso.comp_inv_eq_id _).1 h2

variable {Z Z' X X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X' ⟶ X) (g' : Z' ⟶ Z)
  (w : i' ≫ g = g' ≫ i)

/-- The base change map is the mate, along the horizontal adjunctions, of the comparison of the
two composite direct images around the square. -/
theorem etaleModuleBaseChange_eq_mateEquiv_symm :
    etaleModuleBaseChange Λ i i' g g' w =
      (mateEquiv (etaleModuleInverseImageAdj.{u, r} Λ g')
          (etaleModuleInverseImageAdj.{u, r} Λ g)).symm
        (TwoSquare.mk _ _ _ _ ((etaleModuleDirectImageComp.{u, r} Λ g' i (i' ≫ g) w).hom ≫
          (etaleModuleDirectImageComp.{u, r} Λ i' g (i' ≫ g) rfl).inv)) :=
  Stacks.CategoryTheory.BaseChange.twoSquare_eq_mateEquiv_symm _ _ _ _
    (etaleModuleInverseImageAdj.{u, r} Λ (i' ≫ g)) _ _ _ _
    (conjugateEquiv_etaleModuleInverseImageCompIso_inv.{u, r} Λ i' g)
    (conjugateEquiv_eqToHom_comp_etaleModuleInverseImageCompIso_hom.{u, r} Λ g' i (i' ≫ g) w)

section Integral

variable (Λ : Type) [Ring Λ]

local instance (Z : Scheme.{u}) : Z.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ Z.smallEtaleTopology

local instance (Z : Scheme.{u}) : Z.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  ModuleSheaf.preservesSheafification_forget₂.{u + 1} Λ Z.smallEtaleTopology

variable {Z Z' X X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X' ⟶ X) (g' : Z' ⟶ Z)

/-- Direct image commutes with forgetting the module structure, on the nose. -/
private abbrev directImageForget {S T : Scheme.{u}} (k : T ⟶ S) :
    etaleModuleDirectImage.{u, 0} Λ k ⋙ etaleModuleUnderlyingAbelian (X := S) Λ ⟶
      etaleModuleUnderlyingAbelian (X := T) Λ ⋙ smallEtalePushforwardAb k :=
  𝟙 _

private instance isIso_directImageForget {S T : Scheme.{u}} (k : T ⟶ S) :
    IsIso (directImageForget Λ k) := by
  change IsIso (𝟙 (etaleModuleDirectImage.{u, 0} Λ k ⋙ etaleModuleUnderlyingAbelian (X := S) Λ))
  infer_instance

/-- `directImageForget` read in the other direction. -/
private abbrev directImageForget' {S T : Scheme.{u}} (k : T ⟶ S) :
    etaleModuleUnderlyingAbelian (X := T) Λ ⋙ smallEtalePushforwardAb k ⟶
      etaleModuleDirectImage.{u, 0} Λ k ⋙ etaleModuleUnderlyingAbelian (X := S) Λ :=
  𝟙 _

private instance isIso_directImageForget' {S T : Scheme.{u}} (k : T ⟶ S) :
    IsIso (directImageForget' Λ k) := by
  change IsIso (𝟙 (etaleModuleDirectImage.{u, 0} Λ k ⋙ etaleModuleUnderlyingAbelian (X := S) Λ))
  infer_instance

/-- For a cartesian square `i' ≫ g = g' ≫ i` with `i` integral, the base change map
`g^{-1} i_* ⟶ i'_* g'^{-1}` of sheaves of `Λ`-modules is an isomorphism. -/
theorem isIso_etaleModuleBaseChange_of_isIntegralHom (sq : IsPullback i' g' g i)
    [IsIntegralHom i] : IsIso (etaleModuleBaseChange Λ i i' g g' sq.w) := by
  have hAb := isIso_smallEtaleBaseChangeAb_of_isIntegralHom g i i' g' sq
  rw [show smallEtaleBaseChangeAb g i i' g' sq.w = _ from
    Stacks.Cohomology.BaseChange.mate_eq_mateEquiv_symm _ _ _ _ _] at hAb
  have hhom : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (ab : A ⟶ C) (hab : ab = a ≫ b),
      (etaleAbelianDirectImageCompIso'.{u, 0} a b ab hab).hom =
        (etaleAbelianDirectImageCompIso'.{u, 0} a b (a ≫ b) rfl).hom ≫
          eqToHom (congrArg (fun m : A ⟶ C => etaleAbelianDirectImage.{u, 0} m) hab.symm) := by
    rintro A B C a b _ rfl
    simp
  have hcell : (smallEtalePushforwardAbCompIso g' i ≪≫
      eqToIso (congrArg smallEtalePushforwardAb sq.w.symm) ≪≫
        (smallEtalePushforwardAbCompIso i' g).symm).hom =
      (etaleAbelianDirectImageCompIso'.{u, 0} g' i (i' ≫ g) sq.w).hom ≫
        (etaleAbelianDirectImageCompIso'.{u, 0} i' g (i' ≫ g) rfl).inv := by
    rw [hhom, etaleAbelianDirectImageCompIso'_rfl, etaleAbelianDirectImageCompIso'_rfl]
    simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc]
    rfl
  rw [hcell] at hAb
  have hAb' : IsIso ((mateEquiv (smallEtaleAdjunctionAb g') (smallEtaleAdjunctionAb g)).symm
      (TwoSquare.mk (smallEtalePushforwardAb g') (smallEtalePushforwardAb i')
        (smallEtalePushforwardAb i) (smallEtalePushforwardAb g)
        ((etaleAbelianDirectImageCompIso'.{u, 0} g' i (i' ≫ g) sq.w).hom ≫
          (etaleAbelianDirectImageCompIso'.{u, 0} i' g (i' ≫ g) rfl).inv))) := hAb
  rw [etaleModuleBaseChange_eq_mateEquiv_symm]
  refine Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms
    (etaleModuleInverseImageAdj.{u, 0} Λ g') (etaleModuleInverseImageAdj.{u, 0} Λ g)
    (smallEtaleAdjunctionAb g') (smallEtaleAdjunctionAb g)
    (coefficientSheafPullbackTwoSquare (smallEtaleBaseChange g') Z.smallEtaleTopology
      Z'.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
    (coefficientSheafPullbackTwoSquare (smallEtaleBaseChange g) X.smallEtaleTopology
      X'.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
    (directImageForget Λ i) (directImageForget' Λ i') _
    (TwoSquare.mk (smallEtalePushforwardAb g') (smallEtalePushforwardAb i')
      (smallEtalePushforwardAb i) (smallEtalePushforwardAb g)
      ((etaleAbelianDirectImageCompIso'.{u, 0} g' i (i' ≫ g) sq.w).hom ≫
        (etaleAbelianDirectImageCompIso'.{u, 0} i' g (i' ≫ g) rfl).inv)) ?_
  have hmate : ∀ {S T : Scheme.{u}} (k : T ⟶ S),
      mateEquiv (etaleModuleInverseImageAdj.{u, 0} Λ k) (smallEtaleAdjunctionAb k)
        (coefficientSheafPullbackTwoSquare (smallEtaleBaseChange k) S.smallEtaleTopology
          T.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) =
      coefficientPushforwardTwoSquare (smallEtaleBaseChange k) S.smallEtaleTopology
        T.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    fun _ => Equiv.apply_symm_apply _ _
  rw [hmate g', hmate g]
  exact NatTrans.ext (funext fun _ => Sheaf.hom_ext (NatTrans.ext (funext fun _ => rfl)))

end Integral

end Stacks.EtaleCohomology

end
