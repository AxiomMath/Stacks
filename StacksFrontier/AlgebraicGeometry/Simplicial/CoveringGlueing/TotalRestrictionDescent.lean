module

public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.GlobalSummandIdentification
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleCohomology

/-!
# Descent along the Čech hypercovering of a covering

Let `(C, O_C)` be a ringed site with fibre products, given by a pretopology, and `{U_i ⟶ X}` a
covering of an object `X`. Its Čech object `K` is a hypercovering of `X` (Stacks 01G6), so by
Stacks 0DA5 the restriction `D(O_X) ⟶ D(O)` to the total site of `K` is fully faithful, and by
Stacks 0D7S every bounded below object of `D(O)` whose cohomology modules are cartesian is the
restriction of an object of `D(O_X)`.

## Main results

* `AlgebraicGeometry.RingedSite.CoveringGlueing.isHypercovering_cechObject`: the Čech object of a
  covering is a hypercovering.
* `AlgebraicGeometry.RingedSite.CoveringGlueing.cechTotalRestrictionFullyFaithful`: restriction
  to the total site is fully faithful on derived categories.
* `AlgebraicGeometry.RingedSite.CoveringGlueing.exists_cechTotalRestriction_iso`: bounded below
  objects with cartesian cohomology are restrictions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.CategoryTheory.Hypercovering

universe u

namespace CategoryTheory

/-- A morphism which becomes an isomorphism after composing with images of isomorphisms on both
sides is an isomorphism. -/
theorem isIso_of_isIso_map_comp_comp {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (Φ : 𝒞 ⥤ 𝒟)
    {a a' : 𝒞} {b b' : 𝒟} (e : a ≅ a') (e' : b ≅ b') (t : Φ.obj a ⟶ b)
    (h : IsIso (Φ.map e.inv ≫ t ≫ e'.hom)) : IsIso t := by
  have ht : t = Φ.map e.hom ≫ (Φ.map e.inv ≫ t ≫ e'.hom) ≫ e'.inv := by
    simp [← Functor.map_comp_assoc]
  rw [ht]
  infer_instance

end CategoryTheory

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The two presentations of the cartesian condition on a sheaf of modules agree: if the
transitions `f_φ^*F_m ⟶ F_n` of the literal restrictions are isomorphisms, so are those of the
pullback presentation. -/
theorem isModuleFiberTransitionIso_of_isCartesianModule
    (F : SheafOfModules.{u} (S.totalRingSheaf O)) (hF : IsCartesianModule S O F) :
    S.IsModuleFiberTransitionIso O F := by
  intro m n φ
  have hF' := hF φ
  rw [← S.moduleFiberTransition_comp_restrictionIso O φ F] at hF'
  exact isIso_of_isIso_map_comp_comp (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
    ((componentPullbackModulesRestrictionIso S O m).app F)
    ((componentPullbackModulesRestrictionIso S O n).app F) ((S.moduleFiberTransition O φ).app F) hF'

end CategoryTheory.SimplicialSiteSituation

namespace AlgebraicGeometry.RingedSite.CoveringGlueing

open CategoryTheory.SimplicialSemiRepresentable

attribute [local instance] HasDerivedCategory.standard pretopologyRingedSite_over_hasPullbacks

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (OC : Sheaf P.toGrothendieck CommRingCat.{u}) {ι : Type u} {U : ι → C} (f : ∀ i, U i ⟶ X)

/-- **The Čech object of a covering family is a hypercovering** (Stacks 01G6). -/
theorem isHypercovering_cechObject (hf : Presieve.ofArrows U f ∈ P X) :
    IsHypercovering P (cechObject P OC f) :=
  isHypercovering_cech_of_isCoveringOver P (family (X := pretopologyRingedSite P OC) f)
    (isCoveringOver_terminal_from_of_mem P _ hf)

variable {P OC f} in
/-- **Stacks 0DA5 for the Čech hypercovering of a covering**: restriction of derived objects
from `C/X` to the total site of the Čech object is fully faithful. -/
def cechTotalRestrictionFullyFaithful (hf : Presieve.ofArrows U f ∈ P X) :
    (cechTotalRestriction P OC f).mapDerivedCategory.FullyFaithful :=
  haveI : IsIso (AlgebraicGeometry.RingedToposHom.derivedAdjunctionOfIsIsoFSharp
      (structureSheafAugmentation P (cechObject P OC f) OC).totalRingedHom).unit :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun E => isIso_derivedUnit_structureSheafAugmentation
      (isHypercovering_cechObject P OC f hf) E
  (Adjunction.fullyFaithfulLOfIsIsoUnit
      (AlgebraicGeometry.RingedToposHom.derivedAdjunctionOfIsIsoFSharp
        (structureSheafAugmentation P (cechObject P OC f) OC).totalRingedHom)).ofIso
    (derivedPullbackIsoTotalRestriction P (cechObject P OC f) OC)

variable {P OC f} in
/-- **Stacks 0D7S for the Čech hypercovering of a covering**: a bounded below cartesian object of
the derived category of modules on the total site is the restriction of an object of
`D(O_X)`. -/
theorem exists_cechTotalRestriction_iso (hf : Presieve.ofArrows U f ∈ P X)
    (M : DerivedCategory ((situation (overRingedSite P OC (X := X)).J
      (cechObject P OC f)).totalRingedTopos
        (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f))).Modules)
    (hM : (situation (overRingedSite P OC (X := X)).J (cechObject P OC f)).IsCartesianDerivedModule
      (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f)) M)
    (hb : DerivedCategoryB.IsBoundedBelow M) :
    ∃ N : LocalDerivedCategory.{0} (pretopologyRingedSite P OC) X,
      Nonempty ((cechTotalRestriction P OC f).mapDerivedCategory.obj N ≅ M) := by
  have hM' : (situation (P.toGrothendieck.over X) (cechObject P OC f)).IsCartesianDerivedModule
      (structureSheafAugmentation P (cechObject P OC f) OC).O M := hM
  have hc := ((situation (P.toGrothendieck.over X)
    (cechObject P OC f)).isCartesianDerivedModule_iff_forall_isCartesianModule_homology
      (structureSheafAugmentation P (cechObject P OC f) OC).O
      (fun _ _ => cech_transitionRingedToposHom_isFlat P OC f _) M).1 hM'
  have h2 : IsIso _ := isIso_derivedCounit_structureSheafAugmentation
    (isHypercovering_cechObject P OC f hf) M ⟨hb, fun q ↦
      SimplicialSiteSituation.isModuleFiberTransitionIso_of_isCartesianModule _ _ _ (hc q)⟩
  exact ⟨_, ⟨(derivedPullbackIsoTotalRestriction P (cechObject P OC f) OC).symm.app _ ≪≫
    @asIso _ _ _ _ ((AlgebraicGeometry.RingedToposHom.derivedAdjunctionOfIsIsoFSharp
      (structureSheafAugmentation P (cechObject P OC f) OC).totalRingedHom).counit.app M) h2⟩⟩

end AlgebraicGeometry.RingedSite.CoveringGlueing

end
