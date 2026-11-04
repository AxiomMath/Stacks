module

public import StacksFrontier.Algebra.Category.ModuleCat.ExactLinearFunctorFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKer
public import StacksFrontier.AlgebraicGeometry.ProEtale.AdicQuotientSystemOfSize
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstantCoefficientModules
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteInverseLimitSliceTesting
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteProetale
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.FiniteTypeGlobalGenerators
public import StacksFrontier.Homology.DerivedComplete.FlatAdicCompletionExtension
public import StacksFrontier.Homology.DerivedComplete.PrincipalRecurrence

/-!
# Maps from the completed constant sheaf into derived complete sheaves

Let `X` be a scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal. The completed constant sheaf
`\underline{Λ}^∧ = lim \underline{Λ/Iⁿ}` on `X_proét` is the derived completion of the constant
sheaf `\underline{Λ}` (Stacks 099M): every map `\underline{Λ} → F` into a sheaf of `Λ`-modules
whose sections over the affine objects with w-contractible ring of global sections are derived
complete extends uniquely to `\underline{Λ}^∧`. Over such an object `W` the functor
`M ↦ Γ(W, \underline{M})` is exact and `Λ`-linear, so `A = Γ(W, \underline{Λ})` is a flat
`Λ`-module and `Γ(W, \underline{Λ}^∧)` is the `I`-adic completion of `A`; there the extension is
the one of a map from a flat module along its completion. These affines are cover-dense in
`X_proét`, so the extensions over them glue.

## Main definitions

* `AlgebraicGeometry.ProEtale.completedConstantSheafMap`: the map
  `\underline{Λ} → \underline{Λ}^∧`.
* `AlgebraicGeometry.ProEtale.shiftCone`: a cone over a tower `F` as a cone over a tower
  isomorphic to `n ↦ F(n + 1)`.
* `AlgebraicGeometry.ProEtale.moduleSheafOverConstantCoefficientsSectionsEquiv`: the sections
  of a sheaf of `Λ`-modules are those of the sheaf of `\underline{Λ}`-modules it defines.

## Main results

* `AlgebraicGeometry.ProEtale.bijective_comp_of_isLimit_adicQuotientModuleSystem`: for an exact
  `Λ`-linear endofunctor `G` of `Λ`-modules, maps from `lim G(Λ/Iⁿ)` into a derived complete
  module are the maps from `G(Λ)`.
* `AlgebraicGeometry.ProEtale.existsUnique_completedConstantSheafMap_comp`: maps from
  `\underline{Λ}` into a sheaf of `Λ`-modules with derived complete sections over the
  w-contractible affines extend uniquely along `\underline{Λ} → \underline{Λ}^∧`.
* `AlgebraicGeometry.ProEtale.exists_comp_eq_of_isDerivedComplete`: the same for derived complete
  sheaves of modules over `\underline{Λ}`.
* `AlgebraicGeometry.ProEtale.isDerivedComplete_completedConstantCoefficientSheaf`: completed
  constant sheaves are derived complete.
* `AlgebraicGeometry.RingedSite.idealPowerProductOfSize_cokernel_eq_top_of_epi`: the cokernel `Q`
  of a map which is surjective modulo `I` satisfies `IQ = Q`.
* `AlgebraicGeometry.ProEtale.exists_epi_biproduct_completedConstantCoefficientSheaf`: over a
  weakly contractible affine scheme, a derived complete sheaf `F` with `F/IF` of finite type is a
  quotient of `(\underline{Λ}^∧)^{⊕ t}` for some `t`.

## Implementation notes

The source assumes that `F/IF` is a locally constant sheaf of `Λ/I`-modules of finite type; the
proof uses only that `F/IF`, as a sheaf of modules over `\underline{Λ}`, is of finite type, which
is what Stacks 09BZ is stated with here. The coefficient ring lies in the universe `max (u + 1) w`
of the module sections, as in `AlgebraicGeometry.ProEtale.IsConstructibleViaDerivedReduction`.

The maps out of `\underline{Λ}^∧` are built on the sheaf-of-`Λ`-modules side, where
`Γ(W, \underline{Λ}^∧)` is the limit of the `Γ(W, \underline{Λ/Iⁿ})`, and then transported to
sheaves of modules over `\underline{Λ}` through
`AlgebraicGeometry.ProEtale.constantCoefficientModuleEquiv`, whose sections are identified by the
unit of sheafification.

## References

* [Stacks Project, Tag 099M](https://stacks.math.columbia.edu/tag/099M)
* [Stacks Project, Tag 09BZ](https://stacks.math.columbia.edu/tag/09BZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite DerivedCompleteRecurrence
open scoped IsMulCommutative

universe u v w u' v'

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, max u v w}) [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  (I : SheafOfModules.Submodule (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- **A cokernel of a map which is surjective modulo `I`.** If `L ⟶ F ⟶ F/IF` is an
epimorphism, then the cokernel `Q` of `L ⟶ F` satisfies `IQ = Q`. -/
theorem idealPowerProductOfSize_cokernel_eq_top_of_epi
    {L F : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (f : L ⟶ F) [Epi (f ≫ cokernel.π (idealPowerProductOfSize X I F 1).ι)] :
    idealPowerProductOfSize X I (cokernel f) 1 = ⊤ := by
  let : CompleteLattice (cokernel f).Submodule := SheafOfModules.Submodule.instCompleteLattice
  unfold idealPowerProductOfSize
  refine sInf_eq_top.mpr fun N hN => ?_
  let p := cokernel.π N.ι
  let φ := cokernel.π f ≫ p
  have hle : idealPowerProductOfSize X I F 1 ≤ SheafOfModules.Submodule.ker φ := by
    let : CompleteLattice F.Submodule := SheafOfModules.Submodule.instCompleteLattice
    unfold idealPowerProductOfSize
    refine sInf_le fun U a ha m => ?_
    rw [SheafOfModules.Submodule.mem_ker]
    have hx := hN U a ha ((cokernel.π f).val.app U m)
    have h0 : (N.ι ≫ p).val.app U ⟨_, hx⟩ = 0 := by
      rw [cokernel.condition]
      rfl
    change p.val.app U ((cokernel.π f).val.app U (a • m)) = 0
    rw [show (cokernel.π f).val.app U (a • m) = a • (cokernel.π f).val.app U m from
      ((cokernel.π f).val.app U).hom.map_smul a m]
    exact h0
  have hφ : (idealPowerProductOfSize X I F 1).ι ≫ φ = 0 := by
    rw [← SheafOfModules.Submodule.homOfLE_ι hle, Category.assoc,
      SheafOfModules.Submodule.ker_ι_comp, comp_zero]
  have hd : cokernel.desc _ φ hφ = 0 := by
    rw [← cancel_epi (f ≫ cokernel.π (idealPowerProductOfSize X I F 1).ι), comp_zero,
      Category.assoc, cokernel.π_desc]
    change f ≫ cokernel.π f ≫ p = 0
    rw [cokernel.condition_assoc, zero_comp]
  have hp : p = 0 := by
    rw [← cancel_epi (cokernel.π f), comp_zero]
    change φ = 0
    rw [← cokernel.π_desc _ φ hφ, hd, comp_zero]
  have : Epi N.ι := Abelian.epi_of_cokernel_π_eq_zero _ hp
  have : IsIso N.ι := isIso_of_mono_of_epi _
  refine eq_top_iff.mpr (SheafOfModules.Submodule.le_iff.mpr
    (PresheafOfModules.Submodule.le_iff.mpr fun U x _ => ?_))
  have e : (N.ι.val.app U) ((inv N.ι).val.app U x) = x :=
    congrArg (fun g => (PresheafOfModules.Hom.app g.val U) x) (IsIso.inv_hom_id N.ι)
  rw [← e]
  exact ((inv N.ι).val.app U x).2

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

/-- The derived category of modules over a ring has `ℕ`-indexed products. Named explicitly: the
anonymous instance name collides with the one in `ProEtale/Cohomology/CompletedProperBaseChange`. -/
local instance hasProductsOfShape_nat_derivedCategory_moduleCat_of_ring (R : Type v) [Ring R] :
    HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} R)) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

section ModuleLevel

/-- Bijectivity of the recurrence operator transfers along an additive isomorphism intertwining
the two scalar multiplications. -/
theorem bijective_recurrence_of_addEquiv {A B : Type*} [CommRing A] [CommRing B] {M N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N] (e : M ≃+ N) (f : A) (g : B)
    (h : ∀ x, e (f • x) = g • e x) (hg : Function.Bijective (recurrence (M := N) g)) :
    Function.Bijective (recurrence (M := M) f) := by
  let Ψ : (ℕ → M) ≃ (ℕ → N) := Equiv.arrowCongr (Equiv.refl ℕ) e.toEquiv
  have key : (recurrence (M := M) f : (ℕ → M) → ℕ → M) =
      Ψ.symm ∘ (recurrence (M := N) g) ∘ Ψ := by
    funext a n
    apply e.injective
    simp [Ψ, Equiv.arrowCongr_apply, recurrence_apply, h]
  rw [key]
  exact (Equiv.bijective _).comp (hg.comp (Equiv.bijective _))

/-- The recurrence operator of a scalar acting nilpotently is bijective. -/
theorem bijective_recurrence_of_pow_smul_eq_zero {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (f : A) (n : ℕ) (h : ∀ m : M, f ^ n • m = 0) :
    Function.Bijective (recurrence (M := M) f) := by
  have hN : IsNilpotent (f • LinearMap.funLeft A M Nat.succ) := by
    refine ⟨n, ?_⟩
    rw [smul_pow]
    ext a k
    simp [h]
  exact (Module.End.isUnit_iff _).mp hN.isUnit_one_sub

variable {Λ : Type v} [CommRing Λ] (I : Ideal Λ)

/-- The quotient maps `M → M/IⁿM` form a cone over the tower of adic quotients of `M`. -/
def adicQuotientModuleCone (M : ModuleCat.{v} Λ) : Cone (adicQuotientModuleSystem Λ I M) where
  pt := M
  π := NatTrans.ofOpSequence (fun n => ModuleCat.ofHom (I ^ n • ⊤ : Submodule Λ M).mkQ)
    (fun n => by
      simp only [adicQuotientModuleSystem, Functor.ofOpSequence_map_homOfLE_succ]
      ext x
      rfl)

/-- The `n`-th leg of `adicQuotientModuleCone I M` is the quotient map `M → M/IⁿM`. -/
@[simp]
theorem adicQuotientModuleCone_π_app (M : ModuleCat.{v} Λ) (n : ℕ) :
    (adicQuotientModuleCone I M).π.app (op n) =
      ModuleCat.ofHom (I ^ n • ⊤ : Submodule Λ M).mkQ :=
  rfl

variable (G : ModuleCat.{v} Λ ⥤ ModuleCat.{v} Λ) [G.Additive] [G.Linear Λ]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- For an exact `Λ`-linear endofunctor `G` of `Λ`-modules, `G(Λ/IⁿΛ) ≅ G(Λ)/IⁿG(Λ)`. -/
def mapAdicQuotientIso (n : ℕ) (hn : (I ^ n).FG) :
    G.obj ((adicQuotientModuleSystem Λ I (Functor.unitModule Λ)).obj (op n)) ≅
      ModuleCat.of Λ (G.obj (Functor.unitModule Λ) ⧸
        (I ^ n • ⊤ : Submodule Λ (G.obj (Functor.unitModule Λ)))) :=
  (((LinearMap.quotKerEquivOfSurjective _ (G.surjective_map_mkQ _)).symm).trans
    (Submodule.quotEquivOfEq _ _ (G.ker_map_mkQ (I ^ n) hn))).toModuleIso

/-- Under `mapAdicQuotientIso`, the image by `G` of the quotient map `Λ → Λ/Iⁿ` is the quotient
map `G(Λ) → G(Λ)/IⁿG(Λ)`. -/
theorem map_mkQ_comp_mapAdicQuotientIso_hom (n : ℕ) (hn : (I ^ n).FG) :
    G.map (ModuleCat.ofHom (I ^ n • ⊤ : Submodule Λ (Functor.unitModule Λ)).mkQ) ≫
        (mapAdicQuotientIso I G n hn).hom =
      ModuleCat.ofHom (I ^ n • ⊤ : Submodule Λ (G.obj (Functor.unitModule Λ))).mkQ := by
  ext y
  simp [mapAdicQuotientIso, LinearMap.quotKerEquivOfSurjective_symm_apply]

/-- `mapAdicQuotientIso` sends the image of `y ∈ G(Λ)` in `G(Λ/Iⁿ)` to the class of `y` in
`G(Λ)/IⁿG(Λ)`. -/
theorem mapAdicQuotientIso_hom_apply (n : ℕ) (hn : (I ^ n).FG)
    (y : G.obj (Functor.unitModule Λ)) :
    (mapAdicQuotientIso I G n hn).hom
        ((G.map (ModuleCat.ofHom (I ^ n • ⊤ : Submodule Λ (Functor.unitModule Λ)).mkQ)).hom y) =
      Submodule.Quotient.mk y :=
  congrArg (fun g => g.hom y) (map_mkQ_comp_mapAdicQuotientIso_hom I G n hn)

/-- The successor functor of `ℕ`. -/
abbrev succFunctor : ℕ ⥤ ℕ :=
  Monotone.functor (f := fun n : ℕ => n + 1) fun _ _ h => Nat.add_le_add_right h 1

/-- The successor functor of `ℕ` is final. -/
instance : succFunctor.Final :=
  Functor.final_of_exists_of_isFiltered _ (fun d => ⟨d, ⟨homOfLE (Nat.le_succ d)⟩⟩)
    (fun _ _ => ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)

section Shift

variable {C : Type u'} [Category.{v'} C] {F F' : ℕᵒᵖ ⥤ C}

/-- A cone over a tower `F` gives a cone over any tower `F'` isomorphic to the shifted tower
`n ↦ F(n + 1)`, with the same point. -/
@[simps]
def shiftCone (e : succFunctor.op ⋙ F ≅ F') (c : Cone F) : Cone F' where
  pt := c.pt
  π :=
    { app n := c.π.app (op (n.unop + 1)) ≫ e.hom.app n
      naturality n m f := by
        have h := e.hom.naturality f
        dsimp at h ⊢
        rw [Category.id_comp, Category.assoc, ← h, ← Category.assoc]
        congr 1
        exact (c.w _).symm }

/-- The shifted cone of a limit cone is a limit cone. -/
def isLimitShiftCone (e : succFunctor.op ⋙ F ≅ F') {c : Cone F} (hc : IsLimit c) :
    IsLimit (shiftCone e c) :=
  IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv e _).symm
      ((Functor.Initial.isLimitWhiskerEquiv succFunctor.op c).symm hc))
    (Cone.ext (Iso.refl _) (fun _ => (Category.id_comp _).symm))

end Shift

variable [IsNoetherianRing Λ]

/-- The tower `n ↦ G(Λ/Iⁿ⁺¹)` is the tower of adic quotients of `G(Λ)`. -/
def mapAdicQuotientSystemIso :
    succFunctor.op ⋙ adicQuotientModuleSystem Λ I (Functor.unitModule Λ) ⋙ G ≅
      AdicCompletionTor.adicQuotientSystem I (G.obj (Functor.unitModule Λ)) :=
  NatIso.ofComponents
    (fun n => mapAdicQuotientIso I G (n.unop + 1) (IsNoetherian.noetherian _))
    (fun {n m} f => by
      obtain ⟨n⟩ := n
      obtain ⟨m⟩ := m
      have hnm : m + 1 ≤ n + 1 := Nat.add_le_add_right (leOfHom f.unop) 1
      have h : ModuleCat.ofHom (I ^ (n + 1) • ⊤ : Submodule Λ (Functor.unitModule Λ)).mkQ ≫
          (adicQuotientModuleSystem Λ I (Functor.unitModule Λ)).map (homOfLE hnm).op =
          ModuleCat.ofHom (I ^ (m + 1) • ⊤ : Submodule Λ (Functor.unitModule Λ)).mkQ :=
        (adicQuotientModuleCone I (Functor.unitModule Λ)).w (homOfLE hnm).op
      have h' : G.map (ModuleCat.ofHom (I ^ (n + 1) • ⊤ :
            Submodule Λ (Functor.unitModule Λ)).mkQ) ≫
          G.map ((adicQuotientModuleSystem Λ I (Functor.unitModule Λ)).map (homOfLE hnm).op) =
          G.map (ModuleCat.ofHom (I ^ (m + 1) • ⊤ : Submodule Λ (Functor.unitModule Λ)).mkQ) :=
        (G.map_comp _ _).symm.trans (congrArg G.map h)
      ext z
      obtain ⟨y, rfl⟩ := G.surjective_map_mkQ (I ^ (n + 1) • ⊤ :
        Submodule Λ (Functor.unitModule Λ)) z
      change (mapAdicQuotientIso I G (m + 1) (IsNoetherian.noetherian _)).hom
          ((G.map ((adicQuotientModuleSystem Λ I (Functor.unitModule Λ)).map (homOfLE hnm).op)).hom
            ((G.map (ModuleCat.ofHom
              (I ^ (n + 1) • ⊤ : Submodule Λ (Functor.unitModule Λ)).mkQ)).hom y)) =
        (AdicCompletionTor.adicQuotientSystem I (G.obj (Functor.unitModule Λ))).map f
          ((mapAdicQuotientIso I G (n + 1) (IsNoetherian.noetherian _)).hom ((G.map (ModuleCat.ofHom
          (I ^ (n + 1) • ⊤ : Submodule Λ (Functor.unitModule Λ)).mkQ)).hom y))
      have e1 := congrArg (fun φ => φ.hom y) h'
      have e2 := mapAdicQuotientIso_hom_apply I G (m + 1) (IsNoetherian.noetherian _) y
      have e3 := mapAdicQuotientIso_hom_apply I G (n + 1) (IsNoetherian.noetherian _) y
      calc _ = (mapAdicQuotientIso I G (m + 1) (IsNoetherian.noetherian _)).hom
            ((G.map (ModuleCat.ofHom (I ^ (m + 1) • ⊤ :
              Submodule Λ (Functor.unitModule Λ)).mkQ)).hom y) := congrArg _ e1
        _ = Submodule.Quotient.mk y := e2
        _ = _ := by
          rw [e3]
          rfl)

/-- If `φ : G(Λ) ⟶ c.pt` is compatible with the images by `G` of the quotient maps `Λ → Λ/Iⁿ`,
then its composite with the `n`-th leg of the shifted cone is the quotient map
`G(Λ) → G(Λ)/Iⁿ⁺¹G(Λ)`. -/
theorem comp_shiftCone_π_app
    (c : Cone (adicQuotientModuleSystem Λ I (Functor.unitModule Λ) ⋙ G))
    (φ : G.obj (Functor.unitModule Λ) ⟶ c.pt)
    (hφ : ∀ n : ℕ, φ ≫ c.π.app (op n) =
      G.map (ModuleCat.ofHom (I ^ n • ⊤ : Submodule Λ (Functor.unitModule Λ)).mkQ)) (n : ℕ) :
    φ ≫ (shiftCone (mapAdicQuotientSystemIso I G) c).π.app (op n) =
      ModuleCat.ofHom (I ^ (n + 1) • ⊤ : Submodule Λ (G.obj (Functor.unitModule Λ))).mkQ := by
  rw [shiftCone_π_app, ← Category.assoc, hφ]
  exact map_mkQ_comp_mapAdicQuotientIso_hom I G (n + 1) (IsNoetherian.noetherian _)

/-- **Maps from `lim G(Λ/Iⁿ)` into a derived complete module.** Let `Λ` be a Noetherian ring,
`I ⊆ Λ` an ideal and `G` an exact `Λ`-linear endofunctor of `Λ`-modules. For a limit cone `c` of
the tower `n ↦ G(Λ/Iⁿ)` and the map `φ : G(Λ) ⟶ c.pt` induced by the quotient maps, every map
`G(Λ) ⟶ M` into a derived complete module extends uniquely along `φ` to a map `c.pt ⟶ M`. -/
theorem bijective_comp_of_isLimit_adicQuotientModuleSystem
    (c : Cone (adicQuotientModuleSystem Λ I (Functor.unitModule Λ) ⋙ G)) (hc : IsLimit c)
    (φ : G.obj (Functor.unitModule Λ) ⟶ c.pt)
    (hφ : ∀ n : ℕ, φ ≫ c.π.app (op n) =
      G.map (ModuleCat.ofHom (I ^ n • ⊤ : Submodule Λ (Functor.unitModule Λ)).mkQ))
    (M : ModuleCat.{v} Λ) (hM : IsDerivedCompleteModule I M) :
    Function.Bijective (fun g : c.pt ⟶ M => φ ≫ g) :=
  have := G.flat_obj_unitModule
  NoetherianAdicCompletion.bijective_comp_of_flat_of_isLimit I _ _
    (isLimitShiftCone (mapAdicQuotientSystemIso I G) hc) φ (comp_shiftCone_π_app I G c φ hφ) M hM

end ModuleLevel


section CompletedConstantSheaf

/-- **The affines with w-contractible ring of global sections are cover-dense in `X_proét`**
(Stacks 098I). -/
instance _root_.AlgebraicGeometry.Scheme.ProEt.isCoverDense_isAffineWContractible
    (X : Scheme.{u}) :
    (Scheme.ProEt.IsAffineWContractible (S := X)).ι.IsCoverDense (Scheme.ProEt.topology X) := by
  refine ⟨fun U => ?_⟩
  obtain ⟨K, Ui, f, hf, hP⟩ := Scheme.ProEt.hasEnoughObjects_isAffineWContractible U
  refine (Scheme.ProEt.topology X).superset_covering ?_ hf
  rintro V g ⟨W, h, _, ⟨i⟩, rfl⟩
  exact ⟨⟨⟨Ui i, hP i⟩, h, f i, rfl⟩⟩

open Stacks.ConstantSheaf

variable (X : Scheme.{u}) {Λ : Type (max (u + 1) w)} [CommRing Λ] (I : Ideal Λ)

open ProetaleWContractible

/-- The functor `M ↦ Γ(W, \underline{M})` of sections over `W` of constant sheaves of
`Λ`-modules on `X_proét`. -/
abbrev proetaleConstantSections (W : X.ProEt) :
    ModuleCat.{max (u + 1) w} Λ ⥤ ModuleCat.{max (u + 1) w} Λ :=
  constantSections.{u + 1, u, max (u + 1) w, max (u + 1) w} (Scheme.ProEt.topology X) W

/-- **Sections of constant sheaves on `X_proét` are right exact.** The functor
`M ↦ Γ(W, \underline{M})` preserves finite colimits: it preserves epimorphisms (Stacks 093J)
and finite limits. -/
instance constantSections_preservesFiniteColimits (W : X.ProEt) :
    PreservesFiniteColimits (proetaleConstantSections X W (Λ := Λ)) := by
  have h₁ : (proetaleConstantSections X W (Λ := Λ)).PreservesEpimorphisms :=
    ⟨fun f hf => (ModuleCat.epi_iff_surjective _).2
      (surjective_constantSections_map.{u + 1, u, max (u + 1) w, max (u + 1) w} _ f
        ((ModuleCat.epi_iff_surjective f).1 hf) W)⟩
  have h₃ : (proetaleConstantSections X W (Λ := Λ)).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- The map `\underline{Λ} → \underline{Λ}^∧` from the constant sheaf to the completed constant
sheaf, induced by the quotient maps `Λ → Λ/Iⁿ`. -/
def completedConstantSheafMap :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj
        (Functor.unitModule Λ) ⟶ completedConstantSheaf X Λ I (Functor.unitModule Λ) :=
  limit.lift _ ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).mapCone
    (adicQuotientModuleCone I (Functor.unitModule Λ)))

/-- The composite of `\underline{Λ} → \underline{Λ}^∧` with the projection to `\underline{Λ/Iⁿ}`
is the map induced by the quotient map `Λ → Λ/Iⁿ`. -/
@[reassoc (attr := simp)]
theorem completedConstantSheafMap_π (n : ℕ) :
    completedConstantSheafMap X I ≫ limit.π _ (op n) =
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).map
        (ModuleCat.ofHom (I ^ n • ⊤ : Submodule Λ (Functor.unitModule Λ)).mkQ) :=
  limit.lift_π _ _

/-- Taking sections over `W` of sheaves of `Λ`-modules on `X_proét` preserves `ℕᵒᵖ`-indexed
limits. -/
instance sheafSections_preservesLimitsOfShape_nat (W : X.ProEt) :
    PreservesLimitsOfShape ℕᵒᵖ ((sheafSections (Scheme.ProEt.topology X)
      (ModuleCat.{max (u + 1) w} Λ)).obj (op W)) :=
  preservesLimitsOfShape_of_natIso (sheafSectionsNatIsoEvaluation _ _).symm

/-- The sections over `W` of the completed constant sheaf, as a limit cone of the tower
`n ↦ Γ(W, \underline{Λ/Iⁿ})`. -/
def completedConstantSectionsCone (W : X.ProEt) :
    Cone (adicQuotientModuleSystem Λ I (Functor.unitModule Λ) ⋙
      proetaleConstantSections X W (Λ := Λ)) :=
  (Cone.postcompose (Functor.associator _ _ _).hom).obj
    (((sheafSections (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj (op W)).mapCone
      (limit.cone (adicQuotientModuleSystem Λ I (Functor.unitModule Λ) ⋙
        constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))))

/-- `Γ(W, \underline{Λ}^∧)` is the limit of the `Γ(W, \underline{Λ/Iⁿ})`. -/
def isLimitCompletedConstantSectionsCone (W : X.ProEt) :
    IsLimit (completedConstantSectionsCone X I W) :=
  (IsLimit.postcomposeHomEquiv _ _).symm (isLimitOfPreserves _ (limit.isLimit _))

/-- The ring of sections over `W` of the structure sheaf of the constant coefficient site is
commutative. -/
private instance isMulCommutative_sections_constantCoefficientRingedSite (W : X.ProEt) :
    IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O).obj.obj (op W)) := by
  change IsMulCommutative ((constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O.obj.obj
    (op W))
  infer_instance

variable [IsNoetherianRing Λ]

/-- **Maps from `Γ(W, \underline{Λ}^∧)` into a derived complete module.** For every object `W`
of `X_proét` and every derived complete `Λ`-module `M`, restriction along
`Γ(W, \underline{Λ}) → Γ(W, \underline{Λ}^∧)` is a bijection of `Λ`-linear maps into `M`. -/
theorem bijective_comp_completedConstantSheafMap_app (W : X.ProEt) (M : ModuleCat.{max (u + 1) w} Λ)
    (hM : IsDerivedCompleteModule I M) :
    Function.Bijective (fun g : (completedConstantSheaf X Λ I (Functor.unitModule Λ)).obj.obj
        (op W) ⟶ M => (completedConstantSheafMap X I).hom.app (op W) ≫ g) :=
  bijective_comp_of_isLimit_adicQuotientModuleSystem I (proetaleConstantSections X W (Λ := Λ))
    (completedConstantSectionsCone X I W) (isLimitCompletedConstantSectionsCone X I W)
    ((completedConstantSheafMap X I).hom.app (op W))
    (fun n => congrArg (fun g => g.hom.app (op W)) (completedConstantSheafMap_π X I n)) M hM

/-- **Maps from `\underline{Λ}` into a sheaf with derived complete sections extend to
`\underline{Λ}^∧`.** Let `Λ` be a Noetherian ring, `I ⊆ Λ` an ideal and `F` a sheaf of
`Λ`-modules on `X_proét` whose module of sections over every affine object with w-contractible
ring of global sections is derived complete. Every map `\underline{Λ} ⟶ F` factors uniquely
through `\underline{Λ} ⟶ \underline{Λ}^∧`. -/
theorem existsUnique_completedConstantSheafMap_comp
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (hF : ∀ W : X.ProEt, Scheme.ProEt.IsAffineWContractible W →
      IsDerivedCompleteModule I (F.obj.obj (op W)))
    (s : (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj
      (Functor.unitModule Λ) ⟶ F) :
    ∃! t : completedConstantSheaf X Λ I (Functor.unitModule Λ) ⟶ F,
      completedConstantSheafMap X I ≫ t = s := by
  let P : ObjectProperty X.ProEt := Scheme.ProEt.IsAffineWContractible
  have hbij : ∀ (W : P.FullSubcategory) (W' : P.FullSubcategory), Function.Bijective
      (fun g : (completedConstantSheaf X Λ I (Functor.unitModule Λ)).obj.obj (op W.obj) ⟶
        F.obj.obj (op W'.obj) => (completedConstantSheafMap X I).hom.app (op W.obj) ≫ g) :=
    fun W W' => bijective_comp_completedConstantSheafMap_app X I W.obj _ (hF W'.obj W'.property)
  choose τ hτ using fun W : P.FullSubcategory => (hbij W W).2 (s.hom.app (op W.obj))
  let α : P.ι.op ⋙ (completedConstantSheaf X Λ I (Functor.unitModule Λ)).obj ⟶
      P.ι.op ⋙ F.obj :=
    { app W := τ W.unop
      naturality W W' g := by
        apply (hbij W.unop W'.unop).1
        dsimp only [Functor.comp_obj, Functor.comp_map, Functor.op_obj, Functor.op_map,
          ObjectProperty.ι_obj]
        rw [reassoc_of% (hτ W.unop), ← s.hom.naturality, ← hτ W'.unop,
          ← (completedConstantSheafMap X I).hom.naturality_assoc] }
  have hext : ∀ {G : X.ProEtᵒᵖ ⥤ ModuleCat.{max (u + 1) w} Λ} (f g : G ⟶ F.obj),
      Functor.whiskerLeft P.ι.op f = Functor.whiskerLeft P.ι.op g → f = g :=
    fun f g h => (Functor.IsCoverDense.sheafHom_eq P.ι f).symm.trans
      ((congrArg Functor.IsCoverDense.sheafHom h).trans (Functor.IsCoverDense.sheafHom_eq P.ι g))
  have hα : ∀ W : P.FullSubcategory,
      (Functor.IsCoverDense.sheafHom α).app (op W.obj) = τ W := fun W =>
    congrArg (fun β => β.app (op W)) (Functor.IsCoverDense.sheafHom_restrict_eq α)
  refine ⟨⟨Functor.IsCoverDense.sheafHom α⟩, ?_, fun t ht => ?_⟩
  · refine Sheaf.hom_ext (hext _ _ ?_)
    ext W : 2
    change (completedConstantSheafMap X I).hom.app (op W.unop.obj) ≫
      (Functor.IsCoverDense.sheafHom α).app (op W.unop.obj) = s.hom.app (op W.unop.obj)
    rw [hα]
    exact hτ W.unop
  · have hw : Functor.whiskerLeft P.ι.op t.hom = α := by
      ext W : 2
      apply (hbij W.unop W.unop).1
      change (completedConstantSheafMap X I).hom.app (op W.unop.obj) ≫
          t.hom.app (op W.unop.obj) =
        (completedConstantSheafMap X I).hom.app (op W.unop.obj) ≫ τ W.unop
      exact (congrArg (fun β => β.hom.app (op W.unop.obj)) ht).trans (hτ W.unop).symm
    exact Sheaf.hom_ext ((Functor.IsCoverDense.sheafHom_eq P.ι t.hom).symm.trans
      (congrArg Functor.IsCoverDense.sheafHom hw))

section DerivedCompleteSections

attribute [local instance] SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

/-- The coefficient ring of a sheaf of `Λ`-modules lifted to `ULift Λ`. -/
abbrev uliftCoefficients (P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} (ULift.{max (u + 1) w} Λ)) :=
  (Sheaf.coefficientEquivalence (Scheme.ProEt.topology X)
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max (u + 1) w}
      (ULift.ringEquiv.{max (u + 1) w, max (u + 1) w} (R := Λ)))).functor.obj P

/-- A sheaf of `Λ`-modules on `X_proét` and the sheaf of modules over `\underline{Λ}` it defines
are compared, as presheaves of modules over the constant presheaf of rings, by the unit of
sheafification. -/
def moduleSheafOverConstantCoefficientsUnit
    (P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) :=
  (PresheafOfModules.sheafificationAdjunction
    (constantCoefficientRingMap.{u, max (u + 1) w, w} X Λ)).unit.app
      ((Stacks.PresheafOfModules.ofFunctor (ULift.{max (u + 1) w} Λ)).obj
        (uliftCoefficients X P).obj)

/-- The comparison `moduleSheafOverConstantCoefficientsUnit X P` is an isomorphism. -/
instance (P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) :
    IsIso (moduleSheafOverConstantCoefficientsUnit X P) :=
  Stacks.ConstantRingModules.isIso_sheafificationAdjunction_unit_app_ofFunctor
    _ _ (constantCoefficientRingMap.{u, max (u + 1) w, w} X Λ) (uliftCoefficients X P)

/-- The sections over `W` of a sheaf of `Λ`-modules are those of the sheaf of modules over
`\underline{Λ}` it defines. -/
def moduleSheafOverConstantCoefficientsSectionsEquiv
    (P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) (W : X.ProEt) :
    P.obj.obj (op W) ≃+
      ((constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.obj P).val.obj
        (op W) :=
  have : IsIso ((moduleSheafOverConstantCoefficientsUnit X P).app (op W)) :=
    inferInstanceAs (IsIso ((PresheafOfModules.evaluation _ (op W)).map
      (moduleSheafOverConstantCoefficientsUnit X P)))
  ((asIso ((moduleSheafOverConstantCoefficientsUnit X P).app (op W))).toLinearEquiv).toAddEquiv

omit [IsNoetherianRing Λ] in
/-- The identification of sections is the component over `W` of the unit of sheafification. -/
theorem moduleSheafOverConstantCoefficientsSectionsEquiv_apply
    (P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) (W : X.ProEt)
    (y : P.obj.obj (op W)) :
    moduleSheafOverConstantCoefficientsSectionsEquiv X P W y =
      ((moduleSheafOverConstantCoefficientsUnit X P).app (op W)).hom y :=
  rfl

omit [IsNoetherianRing Λ] in
/-- The identification of sections carries the action of `Λ` to that of `Γ(W, \underline{Λ})`. -/
theorem moduleSheafOverConstantCoefficientsSectionsEquiv_smul
    (P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) (W : X.ProEt) (f : Λ)
    (y : P.obj.obj (op W)) :
    moduleSheafOverConstantCoefficientsSectionsEquiv X P W (f • y) =
      coefficientSectionsMap.{u, max (u + 1) w, w} X Λ W f •
        moduleSheafOverConstantCoefficientsSectionsEquiv X P W y :=
  ((moduleSheafOverConstantCoefficientsUnit X P).app (op W)).hom.map_smul (ULift.up f) y

omit [IsNoetherianRing Λ] in
/-- The identification of sections is natural in the sheaf. -/
theorem moduleSheafOverConstantCoefficientsSectionsEquiv_naturality
    {P P' : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)} (g : P ⟶ P')
    (W : X.ProEt) (y : P.obj.obj (op W)) :
    moduleSheafOverConstantCoefficientsSectionsEquiv X P' W ((g.hom.app (op W)).hom y) =
      ((constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.map g).val.app
        (op W) (moduleSheafOverConstantCoefficientsSectionsEquiv X P W y) :=
  congrArg (fun φ => (φ.app (op W)).hom y)
    ((PresheafOfModules.sheafificationAdjunction
      (constantCoefficientRingMap.{u, max (u + 1) w, w} X Λ)).unit.naturality
      ((Stacks.PresheafOfModules.ofFunctor (ULift.{max (u + 1) w} Λ)).map
        ((sheafToPresheaf _ _).map ((Sheaf.coefficientEquivalence (Scheme.ProEt.topology X)
          (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max (u + 1) w}
            (ULift.ringEquiv.{max (u + 1) w, max (u + 1) w} (R := Λ)))).functor.map g))))

omit [IsNoetherianRing Λ] in
/-- **The sections of a derived complete sheaf of `Λ`-modules over a w-contractible affine are
derived complete.** Let `F` be a sheaf of `Λ`-modules on `X_proét` whose sheaf of modules over
`\underline{Λ}` is derived complete along `I·\underline{Λ}`. Then its module of sections over
every affine object with w-contractible ring of global sections is a derived complete
`Λ`-module. -/
theorem isDerivedCompleteModule_obj_of_isDerivedComplete
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (G : RingedSite.Modules.{u + 1, u, max (u + 1) w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ))
    (hG : RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj G))
    (e : (constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.obj F ≅ G)
    (W : X.ProEt) (hW : Scheme.ProEt.IsAffineWContractible W) :
    IsDerivedCompleteModule I (F.obj.obj (op W)) := by
  have h :=
    (RingedSite.isDerivedComplete_sheaf_single_iff_sections_of_sliceTestingFamily.{u + 1, u, w}
      _ (Scheme.ProEt.testingFamily.{max (u + 1) w} X) _ _).mp hG W hW
  rw [isDerivedCompleteModule_iff_forall_bijective_recurrence] at h ⊢
  intro f hf
  let eW : F.obj.obj (op W) ≃+ G.val.obj (op W) :=
    (moduleSheafOverConstantCoefficientsSectionsEquiv X F W).trans
      ((asIso ((SheafOfModules.evaluation _ (op W)).map e.hom)).toLinearEquiv.toAddEquiv)
  refine bijective_recurrence_of_addEquiv eW f
    (coefficientSectionsMap.{u, max (u + 1) w, w} X Λ W f) (fun x => ?_)
    (h _ (coefficientSectionsMap_mem_constantCoefficientIdealSheaf X Λ I W hf))
  change (e.hom.val.app (op W)).hom (moduleSheafOverConstantCoefficientsSectionsEquiv X F W
    (f • x)) = _
  rw [moduleSheafOverConstantCoefficientsSectionsEquiv_smul]
  exact (e.hom.val.app (op W)).hom.map_smul _ _

omit [IsNoetherianRing Λ] in
/-- **Constant sheaves of modules killed by a power of `I` are derived complete.** -/
theorem isDerivedComplete_constantSheaf_of_pow_smul_eq_zero (hI : I.FG)
    (M : ModuleCat.{max (u + 1) w} Λ) (n : ℕ) (hM : ∀ a ∈ I ^ n, ∀ m : M, a • m = 0) :
    RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.obj
          ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj M))) := by
  refine (RingedSite.isDerivedComplete_sheaf_single_iff_sections_of_sliceTestingFamily.{u + 1, u, w}
    _ (Scheme.ProEt.testingFamily.{max (u + 1) w} X) _ _).mpr fun W hW => ?_
  rw [isDerivedCompleteModule_iff_forall_bijective_recurrence]
  intro g hg
  let P := (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj M
  have hg' : g ∈ I.map (coefficientSectionsMap.{u, max (u + 1) w, w} X Λ W) := by
    rwa [← constantCoefficientIdealSheaf_obj_eq_map X Λ I W hW hI]
  have hann : I ^ n ≤ (Module.annihilator _ (((constantCoefficientModuleEquiv.{u, max (u + 1) w, w}
      X Λ).functor.obj P).val.obj (op W))).comap
      (coefficientSectionsMap.{u, max (u + 1) w, w} X Λ W) := by
    intro a ha
    rw [Ideal.mem_comap, Module.mem_annihilator]
    intro z
    obtain ⟨y, rfl⟩ := (moduleSheafOverConstantCoefficientsSectionsEquiv X P W).surjective z
    rw [← moduleSheafOverConstantCoefficientsSectionsEquiv_smul]
    have hy : a • y = 0 := by
      have h0 : a • 𝟙 M = 0 := by
        ext m
        exact hM a ha m
      have := ((proetaleConstantSections X W (Λ := Λ)).map_smul_id_apply a y)
      rw [h0, Functor.map_zero] at this
      exact this.symm
    rw [hy, map_zero]
  have hgn : g ^ n ∈ Module.annihilator _ (((constantCoefficientModuleEquiv.{u, max (u + 1) w, w}
      X Λ).functor.obj P).val.obj (op W)) := by
    have := Ideal.pow_mem_pow hg' n
    rw [← Ideal.map_pow] at this
    exact Ideal.map_le_iff_le_comap.mpr hann this
  exact bijective_recurrence_of_pow_smul_eq_zero g n (Module.mem_annihilator.mp hgn)

omit [IsNoetherianRing Λ] in
/-- **The completed constant sheaf `\underline{Λ}^∧` is derived complete**, as a sheaf of
modules over `\underline{Λ}`: it is the inverse limit of the constant sheaves
`\underline{Λ/Iⁿ}`, each killed by `Iⁿ`. -/
theorem isDerivedComplete_completedConstantCoefficientSheaf (hI : I.FG)
    (M : ModuleCat.{max (u + 1) w} Λ) :
    RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj
        ((completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} X Λ I).obj M)) := by
  let E := constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ
  let D := adicQuotientModuleSystem Λ I M ⋙
    constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)
  have hD : ∀ n : ℕ, RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj ((D ⋙ E.functor).obj ⟨n⟩)) := by
    intro n
    refine isDerivedComplete_constantSheaf_of_pow_smul_eq_zero X I hI _ n fun a ha m => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    change Submodule.Quotient.mk (a • x) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul ha Submodule.mem_top)
  have hlim := RingedSite.isDerivedComplete_limit_of_sliceTestingFamily.{u + 1, u, w} _
    (Scheme.ProEt.testingFamily.{max (u + 1) w} X) _ (D ⋙ E.functor) hD
  let e : (completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} X Λ I).obj
      M ≅ limit (D ⋙ E.functor) :=
    ((constantCoefficientModuleEquivFunctorIso.{u, max (u + 1) w, w} X Λ).app
      (limit D)).symm ≪≫ preservesLimitIso E.functor D
  exact (RingedSite.isDerivedComplete_iff_of_iso _ _
    ((DerivedCategory.singleFunctor _ 0).mapIso e)).mpr hlim

/-- **Maps from `\underline{Λ}` into a derived complete sheaf factor through
`\underline{Λ}^∧`.** Let `Λ` be a Noetherian ring and `I ⊆ Λ` an ideal. For a sheaf `F` of
modules over `\underline{Λ}` on `X_proét` which is derived complete along `I·\underline{Λ}`,
every map `\underline{Λ} ⟶ F` factors through `\underline{Λ}^∧`. -/
theorem exists_comp_eq_of_isDerivedComplete
    (F : RingedSite.Modules.{u + 1, u, max (u + 1) w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ))
    (hF : RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj F))
    (s : SheafOfModules.unit _ ⟶ F) :
    ∃ (c : SheafOfModules.unit _ ⟶ (completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w}
        X Λ I).obj (Functor.unitModule Λ))
      (t : (completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} X Λ I).obj
        (Functor.unitModule Λ) ⟶ F), c ≫ t = s := by
  let E := constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ
  obtain ⟨P, ⟨ε⟩⟩ : ∃ P, Nonempty (E.functor.obj P ≅ F) := ⟨_, ⟨E.counitIso.app F⟩⟩
  let T : X.ProEt := Scheme.ProEt.mk (𝟙 X)
  let adj := constantSheafAdj (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)
    (IsTerminal.ofUniqueHom (fun V => Scheme.ProEt.toMkId V)
      (fun _ _ => Scheme.ProEt.hom_ext_mkId _ _) : IsTerminal T)
  let σ := F.unitHomEquiv s
  let uP := moduleSheafOverConstantCoefficientsSectionsEquiv X P T
  let y : P.obj.obj (op T) := uP.symm ((ε.inv.val.app (op T)).hom (σ.val (op T)))
  let s' : (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj
      (Functor.unitModule Λ) ⟶ P :=
    (adj.homEquiv _ _).symm (ModuleCat.ofHom (LinearMap.toSpanSingleton Λ (P.obj.obj (op T)) y))
  obtain ⟨t, ht, -⟩ := existsUnique_completedConstantSheafMap_comp X I P
    (isDerivedCompleteModule_obj_of_isDerivedComplete X I P F hF ε) s'
  let ι := (constantCoefficientModuleEquivFunctorIso.{u, max (u + 1) w, w} X Λ).app
    (completedConstantSheaf X Λ I (Functor.unitModule Λ))
  let w₀ := (completedConstantSheafMap X I).hom.app (op T)
    ((adj.unit.app (Functor.unitModule Λ)).hom (1 : Λ))
  let z := (ι.hom.val.app (op T)).hom
    (moduleSheafOverConstantCoefficientsSectionsEquiv X _ T w₀)
  let t' : (completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} X Λ I).obj
      (Functor.unitModule Λ) ⟶ F := ι.inv ≫ E.functor.map t ≫ ε.hom
  have hs' : (s'.hom.app (op T)).hom ((adj.unit.app (Functor.unitModule Λ)).hom (1 : Λ)) = y := by
    have h := adj.homEquiv_unit (Functor.unitModule Λ) P s'
    rw [Equiv.apply_symm_apply] at h
    exact (congrArg (fun g => g.hom (1 : Λ)) h).symm.trans (one_smul Λ y)
  have key : (t'.val.app (op T)).hom z = σ.val (op T) := by
    have h1 : (ι.inv.val.app (op T)).hom z =
        moduleSheafOverConstantCoefficientsSectionsEquiv X _ T w₀ :=
      congrArg (fun g => (g.val.app (op T)).hom
        (moduleSheafOverConstantCoefficientsSectionsEquiv X _ T w₀)) ι.hom_inv_id
    have h2 : (t.hom.app (op T)).hom w₀ = y := by
      rw [← hs', ← ht]
      rfl
    change (ε.hom.val.app (op T)).hom (((E.functor.map t).val.app (op T)).hom
      ((ι.inv.val.app (op T)).hom z)) = _
    rw [h1, ← moduleSheafOverConstantCoefficientsSectionsEquiv_naturality, h2]
    change (ε.hom.val.app (op T)).hom (uP (uP.symm _)) = _
    rw [AddEquiv.apply_symm_apply]
    exact congrArg (fun g => (g.val.app (op T)).hom (σ.val (op T))) ε.inv_hom_id
  refine ⟨(SheafOfModules.unitHomEquiv _).symm (Scheme.ProEt.sectionsOfMkId _ z), t', ?_⟩
  apply F.unitHomEquiv.injective
  rw [SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply]
  refine PresheafOfModules.sections_ext _ _ fun V => ?_
  have e1 : (t'.val.app V).hom ((Scheme.ProEt.sectionsOfMkId _ z).eval V) =
      F.val.map (Scheme.ProEt.toMkId V.unop).op ((t'.val.app (op T)).hom z) := by
    rw [Scheme.ProEt.sectionsOfMkId_eval _ z (Scheme.ProEt.toMkId V.unop)]
    exact PresheafOfModules.naturality_apply t'.val _ z
  refine e1.trans ?_
  rw [key]
  exact σ.property (Scheme.ProEt.toMkId V.unop).op

/-- **Derived complete sheaves are quotients of finite sums of `\underline{Λ}^∧`.** Let `X` be a
weakly contractible affine scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal. Let `F` be a
derived complete sheaf of `Λ`-modules on `X_proét` with `F/IF` of finite type, for instance
locally constant of finite type. Then there are an integer `t` and a surjection
`(\underline{Λ}^∧)^{⊕ t} → F`. -/
@[stacks 09BZ "`F/IF` is only assumed of finite type, which a locally constant sheaf of finite \
  type is"]
theorem exists_epi_biproduct_completedConstantCoefficientSheaf [IsAffine X]
    (hX : IsWeaklyContractibleObj X)
    (F : RingedSite.Modules.{u + 1, u, max (u + 1) w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ))
    (hF : RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj F))
    (hFI : (cokernel (RingedSite.idealPowerProductOfSize.{u + 1, u, w} _
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I) F 1).ι).IsFiniteType) :
    ∃ (t : ℕ) (α : (⨁ fun _ : Fin t =>
        (completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} X Λ I).obj
          (Functor.unitModule Λ)) ⟶ F), Epi α := by
  classical
  have hI : I.FG := IsNoetherian.noetherian I
  let π := cokernel.π (RingedSite.idealPowerProductOfSize.{u + 1, u, w} _
    (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I) F 1).ι
  obtain ⟨n, α, hα⟩ := Scheme.ProEt.exists_epi_comp_of_isFiniteType hX π
  let L := (completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} X Λ I).obj
    (Functor.unitModule Λ)
  choose c t hct using fun i : ULift.{max (u + 1) w} (Fin n) =>
    exists_comp_eq_of_isDerivedComplete X I F hF
      ((SheafOfModules.unitHomEquiv _).symm (F.freeHomEquiv α i))
  let ŝ : (⨁ fun _ : Fin n => L) ⟶ F := biproduct.desc fun i => t ⟨i⟩
  let β : SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O))
      (ULift.{max (u + 1) w} (Fin n)) ⟶ ⨁ fun _ : Fin n => L :=
    (⨁ fun _ : Fin n => L).freeHomEquiv.symm fun i =>
      (⨁ fun _ : Fin n => L).unitHomEquiv (c i ≫ biproduct.ι (fun _ : Fin n => L) i.down)
  have hβ : β ≫ ŝ = α := by
    apply F.freeHomEquiv.injective
    funext i
    have h1 := SheafOfModules.freeHomEquiv_comp_apply β ŝ i
    have h2 : (⨁ fun _ : Fin n => L).freeHomEquiv β i =
        (⨁ fun _ : Fin n => L).unitHomEquiv (c i ≫ biproduct.ι (fun _ : Fin n => L) i.down) :=
      congrFun ((⨁ fun _ : Fin n => L).freeHomEquiv.apply_symm_apply _) i
    have h3 := SheafOfModules.unitHomEquiv_comp_apply
      (c i ≫ biproduct.ι (fun _ : Fin n => L) i.down) ŝ
    have h4 : (c i ≫ biproduct.ι (fun _ : Fin n => L) i.down) ≫ ŝ =
        (SheafOfModules.unitHomEquiv _).symm (F.freeHomEquiv α i) := by
      rw [Category.assoc, biproduct.ι_desc]
      exact hct i
    refine h1.trans ((congrArg _ h2).trans (h3.symm.trans ?_))
    rw [h4, Equiv.apply_symm_apply]
  have hŝ : Epi (ŝ ≫ π) := by
    have : Epi (β ≫ ŝ ≫ π) := by rwa [← Category.assoc, hβ]
    exact epi_of_epi β _
  have hP := derivedCompleteSheaves_isWeakSerreClass.{u, max (u + 1) w, w} X Λ
    (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
  have hsum : RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj (⨁ fun _ : Fin n => L)) :=
    (RingedSite.isDerivedComplete_iff_of_iso _ _ ((DerivedCategory.singleFunctor _ 0).mapIso
      ((completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} X Λ I).mapBiproduct
        (fun _ : Fin n => Functor.unitModule Λ)))).mp
      (isDerivedComplete_completedConstantCoefficientSheaf X I hI _)
  have hQ : IsZero (cokernel ŝ) :=
    isZero_of_isDerivedComplete_of_constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I hI _
      (@ObjectProperty.prop_cokernel _ _ _ _ hP.toIsClosedUnderCokernels _ _ ŝ _ hsum hF)
      (@RingedSite.idealPowerProductOfSize_cokernel_eq_top_of_epi _ _ _ _ _ _ ŝ hŝ)
  exact ⟨n, ŝ, Preadditive.epi_of_cokernel_zero (hQ.eq_of_tgt _ _)⟩

end DerivedCompleteSections

end CompletedConstantSheaf

end AlgebraicGeometry.ProEtale

end
