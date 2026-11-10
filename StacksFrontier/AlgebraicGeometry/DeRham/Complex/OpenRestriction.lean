module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.MapCommutesWithDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.BaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianLocalCohomologyExcision

/-!
# The de Rham complex on an open subscheme

Let `a : X ⟶ S` be a morphism of schemes, `U ⊆ X` an open subscheme and
```
U → X
↓    ↓
S' → S
```
a commutative square with left vertical arrow `a' : U ⟶ S'` such that the canonical maps
`ι^*Ω^n_{X/S} ⟶ Ω^n_{U/S'}` are isomorphisms (for instance a cartesian square, [Stacks, Tag 0FL5],
or one whose horizontal arrows are étale, [Stacks, Tag 0FLV]). Then the restriction to `U` of the
relative forms of `a` is isomorphic to the relative forms of `a'`, compatibly with the de Rham
differentials, which are additive but not `𝒪`-linear. Consequently the de Rham differential of
`a` restricted to `U` and that of `a'` are carried to each other by any additive functor on
sheaves of abelian groups on `U`, and in particular one vanishes on cohomology exactly when the
other does.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.restrictFormsIso`: `(Ω^n_{X/S})|_U ≅ Ω^n_{U/S'}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.restrictFormsIso_hom_app`: on sections over `W ⊆ U`, the
  isomorphism is the pullback of forms along `U ⟶ X`.
* `AlgebraicGeometry.Scheme.Hom.restrictFormsIso_hom_app_deRham_d`: it commutes with the de Rham
  differentials.
* `AlgebraicGeometry.Scheme.Hom.functor_map_restrict_deRham_d_eq_zero_iff`: an additive functor
  kills the restricted de Rham differential of `a` exactly when it kills that of `a'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Tag01VSPullbackTensor
open Stacks.Cohomology.SupportedComplexes (abelianRestrictOpen)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S S' : Scheme.{u}} (U : X.Opens) (a : X ⟶ S) (a' : U.toScheme ⟶ S') (t : S' ⟶ S)
  (hcomm : U.ι ≫ a = a' ≫ t)

/-- A morphism of modules commutes with restriction of sections along `V ≤ W`. -/
private theorem modules_hom_app_presheaf_map {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N)
    {V W : Y.Opens} (h : V ≤ W) (z : Γ(M, W)) :
    φ.app V (M.presheaf.map (homOfLE h).op z) = N.presheaf.map (homOfLE h).op (φ.app W z) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) z

/-- **The restriction of the unit of `ι^* ⊣ ι_*` along an open immersion.** For an open `W` of
`U`, the comparison `M|_U ≅ ι^*M` carries a section `x` of `M` over `ι(W)` to the image of `x`
under the unit of `ι^* ⊣ ι_*`, restricted from `ι⁻¹(ι(W))` to `W`. -/
theorem restrictFunctorIsoPullback_hom_app_app (M : X.Modules) (W : U.toScheme.Opens)
    (x : Γ(M, U.ι ''ᵁ W)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app M) W x =
      ((Scheme.Modules.pullback U.ι).obj M).presheaf.map
        (homOfLE (U.ι.preimage_image_eq W).ge).op (modulesPullbackUnit U.ι M (U.ι ''ᵁ W) x) := by
  let O := U.ι ''ᵁ W
  let ψ := (Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app M
  let z : Γ(M.restrict U.ι, U.ι ⁻¹ᵁ O) :=
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) O x
  have h1 : Scheme.Modules.Hom.app ψ (U.ι ⁻¹ᵁ O) z = modulesPullbackUnit U.ι M O x :=
    ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ O)
      (Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction U.ι)
        (Scheme.Modules.pullbackPushforwardAdjunction U.ι) M)) x
  have hge := (U.ι.preimage_image_eq W).ge
  have h3 : (M.restrict U.ι).presheaf.map (homOfLE hge).op z = x := by
    change M.presheaf.map (homOfLE (U.ι.image_mono hge)).op
      (M.presheaf.map (homOfLE (U.ι.image_preimage_le O)).op x) = x
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      Subsingleton.elim ((homOfLE (U.ι.image_preimage_le O)).op ≫
        (homOfLE (U.ι.image_mono hge)).op) (𝟙 _), M.presheaf.map_id]
    rfl
  rw [← h1, ← h3]
  exact modules_hom_app_presheaf_map ψ hge z

variable (hiso : ∀ n : ℤ, IsIso (relativeDifferentialFormsMap U.ι a a' t hcomm n))

/-- **The relative forms of `a` restricted to `U` are the relative forms of `a'`**: the
restriction is the inverse image along the open immersion `U ⟶ X`, followed by the canonical map
`ι^*Ω^n_{X/S} ⟶ Ω^n_{U/S'}`. -/
def restrictFormsIso (n : ℤ) :
    (relativeDifferentialForms a n).restrict U.ι ≅ relativeDifferentialForms a' n :=
  (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
    @asIso _ _ _ _ (relativeDifferentialFormsMap U.ι a a' t hcomm n) (hiso n)

/-- **`restrictFormsIso` on sections is the pullback of forms**: a form over `ι(W)` is carried to
its pullback along `U ⟶ X`, restricted from `ι⁻¹(ι(W))` to `W`. -/
theorem restrictFormsIso_hom_app (n : ℤ) (W : U.toScheme.Opens)
    (x : Γ(relativeDifferentialForms a n, U.ι ''ᵁ W)) :
    Scheme.Modules.Hom.app (restrictFormsIso U a a' t hcomm hiso n).hom W x =
      (relativeDifferentialForms a' n).presheaf.map (homOfLE (U.ι.preimage_image_eq W).ge).op
        (relativeDifferentialFormsPullback U.ι a a' t hcomm n (U.ι ''ᵁ W) x) := by
  change Scheme.Modules.Hom.app (relativeDifferentialFormsMap U.ι a a' t hcomm n) W
      (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app _) W x) = _
  rw [restrictFunctorIsoPullback_hom_app_app]
  exact modules_hom_app_presheaf_map _ (U.ι.preimage_image_eq W).ge _

/-- **`restrictFormsIso` commutes with the de Rham differentials.** -/
theorem restrictFormsIso_hom_app_deRham_d (p : ℕ) (W : U.toScheme.Opens)
    (x : Γ(relativeDifferentialForms a (p : ℤ), U.ι ''ᵁ W)) :
    Scheme.Modules.Hom.app (restrictFormsIso U a a' t hcomm hiso ((p + 1 : ℕ) : ℤ)).hom W
        (((deRhamComplex a).d p (p + 1)).val.app (op (U.ι ''ᵁ W)) x) =
      ((deRhamComplex a').d p (p + 1)).val.app (op W)
        (Scheme.Modules.Hom.app (restrictFormsIso U a a' t hcomm hiso (p : ℤ)).hom W x) := by
  have hd := deRhamComplex_d_relativeDifferentialFormsPullback U.ι a a' t hcomm p
    (U.ι ''ᵁ W) x
  have hnat := PresheafOfModules.naturality_apply ((deRhamComplex a').d p (p + 1)).val
    (homOfLE (U.ι.preimage_image_eq W).ge).op
    (relativeDifferentialFormsPullback U.ι a a' t hcomm (p : ℤ) (U.ι ''ᵁ W) x)
  refine (restrictFormsIso_hom_app U a a' t hcomm hiso ((p + 1 : ℕ) : ℤ) W _).trans ?_
  refine Eq.trans ?_ (congrArg (((deRhamComplex a').d p (p + 1)).val.app (op W))
    (restrictFormsIso_hom_app U a a' t hcomm hiso (p : ℤ) W x)).symm
  exact (congrArg _ hd.symm).trans hnat.symm

/-- **The restricted de Rham differential of `a` is that of `a'`**, as morphisms of sheaves of
abelian groups on `U`, up to the isomorphisms `restrictFormsIso`. -/
theorem toSheaf_restrict_deRham_d_comp_restrictFormsIso (p : ℕ) :
    (abelianRestrictOpen U).map
        ((SheafOfModules.toSheaf _).map ((deRhamComplex a).d p (p + 1))) ≫
      (SheafOfModules.toSheaf U.toScheme.ringCatSheaf).map
        (restrictFormsIso U a a' t hcomm hiso ((p + 1 : ℕ) : ℤ)).hom =
    (SheafOfModules.toSheaf U.toScheme.ringCatSheaf).map
        (restrictFormsIso U a a' t hcomm hiso (p : ℤ)).hom ≫
      (_root_.SheafOfModules.toSheaf (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} a'.base).obj S'.sheaf))).map
        ((deRhamComplex a').d p (p + 1)) := by
  ext W x
  exact restrictFormsIso_hom_app_deRham_d U a a' t hcomm hiso p W.unop x

include hcomm hiso in
/-- **A functor kills the restricted de Rham differential of `a` exactly when it kills that of
`a'`.** -/
theorem functor_map_restrict_deRham_d_eq_zero_iff {E : Type*} [Category* E]
    [HasZeroMorphisms E]
    (F : Sheaf (Opens.grothendieckTopology U.toScheme.carrier) AddCommGrpCat.{u} ⥤ E) (p : ℕ) :
    F.map ((abelianRestrictOpen U).map
        ((SheafOfModules.toSheaf _).map ((deRhamComplex a).d p (p + 1)))) = 0 ↔
      F.map ((_root_.SheafOfModules.toSheaf (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} a'.base).obj S'.sheaf))).map
        ((deRhamComplex a').d p (p + 1))) = 0 := by
  have hsq := (F.map_comp _ _).symm.trans ((congrArg F.map
    (toSheaf_restrict_deRham_d_comp_restrictFormsIso U a a' t hcomm hiso p)).trans
      (F.map_comp _ _))
  let e₀ := F.mapIso ((SheafOfModules.toSheaf U.toScheme.ringCatSheaf).mapIso
    (restrictFormsIso U a a' t hcomm hiso (p : ℤ)))
  let e₁ := F.mapIso ((SheafOfModules.toSheaf U.toScheme.ringCatSheaf).mapIso
    (restrictFormsIso U a a' t hcomm hiso ((p + 1 : ℕ) : ℤ)))
  constructor
  · intro h
    have h0 := hsq.symm.trans ((congrArg (· ≫ e₁.hom) h).trans zero_comp)
    exact (Iso.cancel_iso_hom_left e₀ _ _).1 (h0.trans comp_zero.symm)
  · intro h
    have h0 := hsq.trans ((congrArg (e₀.hom ≫ ·) h).trans comp_zero)
    exact (Iso.cancel_iso_hom_right _ _ e₁).1 (h0.trans zero_comp.symm)

end AlgebraicGeometry.Scheme.Hom
