module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Product
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientSystem
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The adic quotient tower commutes with restriction to an open subscheme

Let `f : Y ⟶ X` be an open immersion of schemes, let `I` be a quasi-coherent ideal sheaf on `X`
and let `M` be a quasi-coherent `𝒪_X`-module. The tower
`Stacks.Algebraization.adicQuotientSystem I M` is `n ↦ M / Iⁿ M`. Restricting it to `Y` term by
term gives the tower of `M|_Y` along `I|_Y`.

Term by term this is `Stacks.Algebraization.restrictIdealPowerQuotientIso`; those identifications
are natural in `n`, so they assemble into an isomorphism of inverse systems. Variants allow an
ideal sheaf on `Y` merely equal to the restriction of `I`, an identification of the tower upstairs
with another tower, and a module on `Y` presented as a restriction only up to isomorphism.

## Main definitions

* `Stacks.Algebraization.adicQuotientSystemMapIso` — an isomorphism of modules carried to the
  adic quotient towers.
* `Stacks.Algebraization.adicQuotientRestrictOpenIso` — the comparison
  `(M|_Y) / (I|_Y)ⁿ (M|_Y) ≅ (M / Iⁿ M)|_Y` as an isomorphism of towers.
* `Stacks.Algebraization.adicQuotientRestrictOpenIsoOfEq` — the same for an ideal sheaf on `Y`
  merely equal to `I|_Y`.
* `Stacks.Algebraization.adicQuotientRestrictOpenTowerIso` and
  `Stacks.Algebraization.adicQuotientRestrictOpenTowerIsoOfIso` — the comparison composed with an
  identification of the tower upstairs, and with an identification of the module downstairs.

## Main results

* `Stacks.Algebraization.π_comp_adicQuotientRestrictOpenIso_hom_app` and the corresponding
  statements for the three variants — every comparison here respects the quotient projections.

## References

* [Stacks Project, Tag 0EI8](https://stacks.math.columbia.edu/tag/0EI8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-! ### Transporting the tower along an isomorphism of modules -/

/-- An isomorphism of modules induces an isomorphism of adic quotient towers. -/
public noncomputable def adicQuotientSystemMapIso {X : Scheme.{u}} (I : X.IdealSheafData)
    {M N : X.Modules} (e : M ≅ N) :
    adicQuotientSystem I M ≅ adicQuotientSystem I N := by
  refine NatIso.ofComponents
    (fun n => (idealPowerQuotientFunctor I n.unop).mapIso e) ?_
  intro i j g
  apply (cancel_epi (cokernel.π (C := X.Modules) (idealPowerMultiple I i.unop M).ι)).mp
  have hleft : cokernel.π (C := X.Modules) (idealPowerMultiple I i.unop M).ι ≫
      ((adicQuotientSystem I M).map g ≫
        ((idealPowerQuotientFunctor I j.unop).mapIso e).hom) =
      e.hom ≫ cokernel.π (C := X.Modules) (idealPowerMultiple I j.unop N).ι := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg
      (fun q => q ≫ ((idealPowerQuotientFunctor I j.unop).mapIso e).hom)
      (quotientMapOfLE_π (idealPowerMultiple_antitone I M (leOfHom g.unop)))) ?_
    exact idealPowerQuotientMap_π I I j.unop j.unop le_rfl e.hom
  have hright : cokernel.π (C := X.Modules) (idealPowerMultiple I i.unop M).ι ≫
      (((idealPowerQuotientFunctor I i.unop).mapIso e).hom ≫
        (adicQuotientSystem I N).map g) =
      e.hom ≫ cokernel.π (C := X.Modules) (idealPowerMultiple I j.unop N).ι := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun q => q ≫ (adicQuotientSystem I N).map g)
      (idealPowerQuotientMap_π I I i.unop i.unop le_rfl e.hom)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact congrArg (fun q => e.hom ≫ q)
      (quotientMapOfLE_π (idealPowerMultiple_antitone I N (leOfHom g.unop)))
  exact hleft.trans hright.symm

/-- The components of the transport along an isomorphism of modules. -/
public lemma adicQuotientSystemMapIso_hom_app {X : Scheme.{u}} (I : X.IdealSheafData)
    {M N : X.Modules} (e : M ≅ N) (n : ℕᵒᵖ) :
    (adicQuotientSystemMapIso I e).hom.app n =
      idealPowerQuotientMap I I n.unop n.unop le_rfl e.hom :=
  rfl

/-- The transport along an isomorphism of modules respects the quotient projections. -/
public lemma π_comp_adicQuotientSystemMapIso_hom_app {X : Scheme.{u}} (I : X.IdealSheafData)
    {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι ≫
        (adicQuotientSystemMapIso I e).hom.app ⟨n⟩ =
      e.hom ≫ cokernel.π (C := X.Modules) (idealPowerMultiple I n N).ι := by
  rw [adicQuotientSystemMapIso_hom_app]
  exact idealPowerQuotientMap_π I I n n le_rfl e.hom

/-! ### Restriction to an open subscheme -/

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (I : X.IdealSheafData)
  (M : X.Modules) [M.IsQuasicoherent]

/-- **The adic quotient tower commutes with restriction to an open subscheme.** For an open
immersion `f : Y ⟶ X`, a quasi-coherent ideal sheaf `I` on `X` and a quasi-coherent module `M`,
the tower `n ↦ (M|_Y) / (I|_Y)ⁿ (M|_Y)` is the termwise restriction of the tower `n ↦ M / Iⁿ M`,
compatibly with every transition map. -/
@[ega "III 5.2.6" "partial"]
public noncomputable def adicQuotientRestrictOpenIso :
    adicQuotientSystem (I.comap f) ((Scheme.Modules.restrictFunctor f).obj M) ≅
      adicQuotientSystem I M ⋙ Scheme.Modules.restrictFunctor f := by
  refine NatIso.ofComponents
    (fun n => restrictIdealPowerQuotientIso f I n.unop M) ?_
  intro i j g
  apply (cancel_epi (cokernel.π (C := Y.Modules)
    (idealPowerMultiple (I.comap f) i.unop
      ((Scheme.Modules.restrictFunctor f).obj M)).ι)).mp
  have hleft : cokernel.π (C := Y.Modules)
      (idealPowerMultiple (I.comap f) i.unop
        ((Scheme.Modules.restrictFunctor f).obj M)).ι ≫
      ((adicQuotientSystem (I.comap f)
          ((Scheme.Modules.restrictFunctor f).obj M)).map g ≫
        (restrictIdealPowerQuotientIso f I j.unop M).hom) =
      (Scheme.Modules.restrictFunctor f).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I j.unop M).ι) := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun q => q ≫ (restrictIdealPowerQuotientIso f I j.unop M).hom)
      (quotientMapOfLE_π (idealPowerMultiple_antitone (I.comap f)
        ((Scheme.Modules.restrictFunctor f).obj M) (leOfHom g.unop)))) ?_
    exact cokernel_π_comp_restrictIdealPowerQuotientIso f I j.unop M
  have hright : cokernel.π (C := Y.Modules)
      (idealPowerMultiple (I.comap f) i.unop
        ((Scheme.Modules.restrictFunctor f).obj M)).ι ≫
      ((restrictIdealPowerQuotientIso f I i.unop M).hom ≫
        (Scheme.Modules.restrictFunctor f).map
          ((adicQuotientSystem I M).map g)) =
      (Scheme.Modules.restrictFunctor f).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I j.unop M).ι) := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun q => q ≫ (Scheme.Modules.restrictFunctor f).map
      ((adicQuotientSystem I M).map g))
      (cokernel_π_comp_restrictIdealPowerQuotientIso f I i.unop M)) ?_
    refine Eq.trans ((Scheme.Modules.restrictFunctor f).map_comp _ _).symm ?_
    exact congrArg (Scheme.Modules.restrictFunctor f).map
      (quotientMapOfLE_π (idealPowerMultiple_antitone I M (leOfHom g.unop)))
  exact hleft.trans hright.symm

/-- The isomorphism of towers acts levelwise as
`Stacks.Algebraization.restrictIdealPowerQuotientIso`. -/
public lemma adicQuotientRestrictOpenIso_hom_app (n : ℕᵒᵖ) :
    (adicQuotientRestrictOpenIso f I M).hom.app n =
      (restrictIdealPowerQuotientIso f I n.unop M).hom :=
  rfl

/-- The isomorphism of towers respects the quotient projections. -/
public lemma π_comp_adicQuotientRestrictOpenIso_hom_app (n : ℕ) :
    cokernel.π (C := Y.Modules)
        (idealPowerMultiple (I.comap f) n
          ((Scheme.Modules.restrictFunctor f).obj M)).ι ≫
      (adicQuotientRestrictOpenIso f I M).hom.app ⟨n⟩ =
      (Scheme.Modules.restrictFunctor f).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι) :=
  cokernel_π_comp_restrictIdealPowerQuotientIso f I n M

/-! ### The tower upstairs, identified and then restricted -/

/-- Restriction of the adic quotient tower to an open subscheme, for an ideal sheaf on the open
presented as something *equal* to the restriction of one on the ambient scheme. -/
public noncomputable def adicQuotientRestrictOpenIsoOfEq {K : Y.IdealSheafData}
    (hK : K = I.comap f) :
    adicQuotientSystem K ((Scheme.Modules.restrictFunctor f).obj M) ≅
      adicQuotientSystem I M ⋙ Scheme.Modules.restrictFunctor f := by
  subst hK
  exact adicQuotientRestrictOpenIso f I M

/-- At the restricted ideal sheaf itself the comparison is
`Stacks.Algebraization.adicQuotientRestrictOpenIso`. -/
public lemma adicQuotientRestrictOpenIsoOfEq_rfl :
    adicQuotientRestrictOpenIsoOfEq f I M rfl = adicQuotientRestrictOpenIso f I M :=
  rfl

/-- The comparison respects the quotient projections. -/
public lemma π_comp_adicQuotientRestrictOpenIsoOfEq_hom_app {K : Y.IdealSheafData}
    (hK : K = I.comap f) (n : ℕ) :
    cokernel.π (C := Y.Modules)
        (idealPowerMultiple K n ((Scheme.Modules.restrictFunctor f).obj M)).ι ≫
        (adicQuotientRestrictOpenIsoOfEq f I M hK).hom.app ⟨n⟩ =
      (Scheme.Modules.restrictFunctor f).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι) := by
  subst hK
  rw [adicQuotientRestrictOpenIsoOfEq_rfl]
  exact π_comp_adicQuotientRestrictOpenIso_hom_app f I M n

/-- **A tower identified upstairs and then restricted.** Given an identification
`α : M / Iⁿ M ≅ T` of the adic quotient tower of `M` on `X` with a tower `T`, and an ideal sheaf
`K` on `Y` equal to `I|_Y`, the adic quotient tower of `M|_Y` along `K` is `T` restricted to
`Y`. -/
public noncomputable def adicQuotientRestrictOpenTowerIso {K : Y.IdealSheafData}
    (hK : K = I.comap f) {T : ℕᵒᵖ ⥤ X.Modules} (α : adicQuotientSystem I M ≅ T) :
    adicQuotientSystem K ((Scheme.Modules.restrictFunctor f).obj M) ≅
      T ⋙ Scheme.Modules.restrictFunctor f :=
  adicQuotientRestrictOpenIsoOfEq f I M hK ≪≫
    Functor.isoWhiskerRight α (Scheme.Modules.restrictFunctor f)

/-- The components of `Stacks.Algebraization.adicQuotientRestrictOpenTowerIso` are those of
`Stacks.Algebraization.adicQuotientRestrictOpenIsoOfEq` followed by the restriction of `α`. -/
public lemma adicQuotientRestrictOpenTowerIso_hom_app {K : Y.IdealSheafData}
    (hK : K = I.comap f) {T : ℕᵒᵖ ⥤ X.Modules} (α : adicQuotientSystem I M ≅ T) (n : ℕᵒᵖ) :
    (adicQuotientRestrictOpenTowerIso f I M hK α).hom.app n =
      (adicQuotientRestrictOpenIsoOfEq f I M hK).hom.app n ≫
        (Scheme.Modules.restrictFunctor f).map (α.hom.app n) :=
  rfl

/-- **The comparison respects the quotient projections.** -/
public lemma π_comp_adicQuotientRestrictOpenTowerIso_hom_app {K : Y.IdealSheafData}
    (hK : K = I.comap f) {T : ℕᵒᵖ ⥤ X.Modules} (α : adicQuotientSystem I M ≅ T) (n : ℕ) :
    cokernel.π (C := Y.Modules)
        (idealPowerMultiple K n ((Scheme.Modules.restrictFunctor f).obj M)).ι ≫
        (adicQuotientRestrictOpenTowerIso f I M hK α).hom.app ⟨n⟩ =
      (Scheme.Modules.restrictFunctor f).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι ≫ α.hom.app ⟨n⟩) := by
  rw [adicQuotientRestrictOpenTowerIso_hom_app]
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [π_comp_adicQuotientRestrictOpenIsoOfEq_hom_app]
  exact ((Scheme.Modules.restrictFunctor f).map_comp _ _).symm

/-- **A tower identified upstairs and then restricted, for a module on `Y` presented as `M|_Y`
only up to isomorphism.** -/
public noncomputable def adicQuotientRestrictOpenTowerIsoOfIso {K : Y.IdealSheafData}
    (hK : K = I.comap f) {T : ℕᵒᵖ ⥤ X.Modules} (α : adicQuotientSystem I M ≅ T)
    {F : Y.Modules} (e : F ≅ (Scheme.Modules.restrictFunctor f).obj M) :
    adicQuotientSystem K F ≅ T ⋙ Scheme.Modules.restrictFunctor f :=
  adicQuotientSystemMapIso K e ≪≫ adicQuotientRestrictOpenTowerIso f I M hK α

/-- The components of `Stacks.Algebraization.adicQuotientRestrictOpenTowerIsoOfIso` are those of
`Stacks.Algebraization.adicQuotientSystemMapIso` followed by those of
`Stacks.Algebraization.adicQuotientRestrictOpenTowerIso`. -/
public lemma adicQuotientRestrictOpenTowerIsoOfIso_hom_app {K : Y.IdealSheafData}
    (hK : K = I.comap f) {T : ℕᵒᵖ ⥤ X.Modules} (α : adicQuotientSystem I M ≅ T)
    {F : Y.Modules} (e : F ≅ (Scheme.Modules.restrictFunctor f).obj M) (n : ℕᵒᵖ) :
    (adicQuotientRestrictOpenTowerIsoOfIso f I M hK α e).hom.app n =
      (adicQuotientSystemMapIso K e).hom.app n ≫
        (adicQuotientRestrictOpenTowerIso f I M hK α).hom.app n :=
  rfl

/-- **The comparison for a presented module respects the quotient projections.** -/
public lemma π_comp_adicQuotientRestrictOpenTowerIsoOfIso_hom_app {K : Y.IdealSheafData}
    (hK : K = I.comap f) {T : ℕᵒᵖ ⥤ X.Modules} (α : adicQuotientSystem I M ≅ T)
    {F : Y.Modules} (e : F ≅ (Scheme.Modules.restrictFunctor f).obj M) (n : ℕ) :
    cokernel.π (C := Y.Modules) (idealPowerMultiple K n F).ι ≫
        (adicQuotientRestrictOpenTowerIsoOfIso f I M hK α e).hom.app ⟨n⟩ =
      e.hom ≫ (Scheme.Modules.restrictFunctor f).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι ≫ α.hom.app ⟨n⟩) := by
  rw [adicQuotientRestrictOpenTowerIsoOfIso_hom_app]
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [π_comp_adicQuotientSystemMapIso_hom_app]
  exact (Category.assoc _ _ _).trans
    (congrArg (e.hom ≫ ·) (π_comp_adicQuotientRestrictOpenTowerIso_hom_app f I M hK α n))

end Stacks.Algebraization

end
