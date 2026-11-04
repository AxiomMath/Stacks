module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.Coherent
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroup
public import StacksFrontier.CategoryTheory.Abelian.GrothendieckGroup
public import StacksFrontier.RingTheory.HilbertFunction

/-!
# The coherent Grothendieck group of an affine Noetherian scheme

For a Noetherian commutative ring `R`, the Grothendieck group `K'₀(Spec R)` of coherent sheaves
on `Spec R` agrees with the Grothendieck group `K'₀(R)` of finite `R`-modules, through the
equivalence `M ↦ M̃` between finitely generated `R`-modules and coherent `𝒪_{Spec R}`-modules.

## Main definitions

* `AffineQuasicoherentModules R` and `AffineCoherentQuasicoherentModules R`: the quasi-coherent
  `𝒪_{Spec R}`-modules, and the coherent ones among them, as full subcategories.
* `coherentModulesEquivCoherentQuasicoherent R`: coherent `𝒪_{Spec R}`-modules form the same
  category whether coherence is imposed directly or on top of quasi-coherence.
* `fgModuleCatEquivCoherentQuasicoherent R` and `coherentModulesEquivFGModuleCat R`: the
  equivalence `M ↦ M̃` between finitely generated `R`-modules and coherent `𝒪_{Spec R}`-modules.
* `kZeroMapOfEquivalence e` and `kZeroEquivOfEquivalence e`: the homomorphism and the isomorphism
  of Grothendieck groups induced by an equivalence of abelian categories.
* `finModuleOfFG M`: a finitely generated module, viewed as a bundled finite module.
* `kZeroClassOfFinModule R N`, `kZeroToKPrime0 R`, `kPrime0ToKZero R` and `kZeroEquivKPrime0 R`:
  the mutually inverse comparison homomorphisms between `K₀(FGModuleCat R)` and `K'₀(R)`.
* `affineCoherentKZeroEquiv R`: the identification `K'₀(Spec R) ≃+ K'₀(R)`.

## Main results

* `isCoherent_iff_isCoherent'`: the two coherence predicates in the library agree.
* `tilde_isCoherent_iff`: for `R` Noetherian, `M̃` is coherent exactly when `M` is finite.
* `kZeroMapOfEquivalence_mk` and `kZeroEquivOfEquivalence_mk`: the induced maps on Grothendieck
  groups send the class of an object to the class of its image.
* `kZeroClassOfFinModule_congr` and `kZeroClassOfFinModule_add_of_shortExact`: the class of a
  finite module in `K₀(FGModuleCat R)` is invariant under isomorphism and additive along short
  exact sequences, which is what the universal property of `K'₀(R)` consumes.
* `kPrime0ToKZero_cls` and `kZeroEquivKPrime0_mk`: the comparison homomorphisms on classes.
* `affineCoherentKZeroEquiv_mk`: the identification sends the class of a coherent sheaf
  isomorphic to `M̃` to the class of `M`.

## Implementation notes

The equality of groups in the source is expressed here as an additive equivalence.

Coherent `𝒪_{Spec R}`-modules are the full subcategory of *all* modules cut out by coherence,
whereas the equivalence `M ↦ M̃` lands in the full subcategory of quasi-coherent modules; the two
spellings of "coherent module" are compared by `coherentModulesEquivCoherentQuasicoherent`.
Coherence of `M̃` is transported using that on a locally Noetherian scheme coherence is
equivalent to quasi-coherence together with finite type (Stacks, Tag 01XZ) and that finite type
of `M̃` is finiteness of `M` (Stacks, Tag 01PB).

Coherence of a sheaf of modules on a ringed space is available under two names,
`Stacks.SheafOfModules.IsCoherent` and a root-level `SheafOfModules.IsCoherent`; they are the
same two-field class and `isCoherent_iff_isCoherent'` converts between them. The category of
coherent modules is cut out by the first, while the results quoted above are stated over the
second.

## References

* [Stacks Project, Tag 0FDH](https://stacks.math.columbia.edu/tag/0FDH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.GrothendieckGroupAffine

/-! ### Coherent modules on `Spec R` and finitely generated `R`-modules -/

/-- Quasi-coherent `𝒪_{Spec R}`-modules, as a full subcategory of all `𝒪_{Spec R}`-modules. -/
abbrev AffineQuasicoherentModules (R : Type u) [CommRing R] :=
  ObjectProperty.FullSubcategory
    (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of R)).ringCatSheaf)

/-- Coherent `𝒪_{Spec R}`-modules, as a full subcategory of the quasi-coherent ones. -/
abbrev AffineCoherentQuasicoherentModules (R : Type u) [CommRing R] :=
  ObjectProperty.FullSubcategory
    (fun F : AffineQuasicoherentModules R => Stacks.SheafOfModules.IsCoherent F.obj)

/-- The library carries two coherence predicates for a sheaf of modules on a ringed space:
`Stacks.SheafOfModules.IsCoherent`, which cuts out the category of coherent modules, and the
root-level `SheafOfModules.IsCoherent`, over which [Stacks, Tag 01BV] and [Stacks, Tag 01BW] are
stated. They are the same two-field class under two names, and are converted into each other
field by field. The primed side of the name is the root-level one. -/
theorem isCoherent_iff_isCoherent' {X : Type u} [TopologicalSpace X]
    {R : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (M : SheafOfModules.{u} R) :
    Stacks.SheafOfModules.IsCoherent M ↔ _root_.SheafOfModules.IsCoherent M :=
  ⟨fun h => ⟨h.isFiniteType, h.kernel_isFiniteType⟩,
    fun h => ⟨h.isFiniteType, h.kernel_isFiniteType⟩⟩

/-- For a Noetherian ring `R`, the `𝒪_{Spec R}`-module `M̃` associated with an `R`-module `M` is
coherent exactly when `M` is a finite `R`-module. -/
theorem tilde_isCoherent_iff (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} (CommRingCat.of R)) :
    Stacks.SheafOfModules.IsCoherent (AlgebraicGeometry.tilde M) ↔ Module.Finite R M := by
  refine (isCoherent_iff_isCoherent' (AlgebraicGeometry.tilde M)).trans
    (((CoherentTFAE.coherent_tfae (Spec (CommRingCat.of R))
      (AlgebraicGeometry.tilde M)).out 1 2).trans ?_)
  exact ⟨fun h => (AlgebraicGeometry.tilde_isFiniteType_iff M).mp h.2,
    fun h => ⟨inferInstance, (AlgebraicGeometry.tilde_isFiniteType_iff M).mpr h⟩⟩

/-- Coherence may equivalently be imposed on all `𝒪_{Spec R}`-modules or on the quasi-coherent
ones: a coherent module is quasi-coherent, so the two full subcategories agree. -/
def coherentModulesEquivCoherentQuasicoherent (R : Type u) [CommRing R] :
    Stacks.SheafOfModules.CoherentModules (Spec (CommRingCat.of R)).ringCatSheaf ≌
      AffineCoherentQuasicoherentModules R := by
  let C : ObjectProperty ((Spec (CommRingCat.of R)).Modules) :=
    fun F => Stacks.SheafOfModules.IsCoherent F
  let Q : ObjectProperty ((Spec (CommRingCat.of R)).Modules) :=
    SheafOfModules.isQuasicoherent (Spec (CommRingCat.of R)).ringCatSheaf
  let Cq : ObjectProperty (ObjectProperty.FullSubcategory Q) :=
    fun F => Stacks.SheafOfModules.IsCoherent F.obj
  let F₁ : ObjectProperty.FullSubcategory C ⥤ ObjectProperty.FullSubcategory Cq :=
    Cq.lift (Q.lift C.ι (fun F => by
      have : _root_.SheafOfModules.IsCoherent F.obj :=
        (isCoherent_iff_isCoherent' F.obj).mp F.property
      exact isQuasicoherent_of_isCoherent F.obj))
      (fun F => F.property)
  let G₁ : ObjectProperty.FullSubcategory Cq ⥤ ObjectProperty.FullSubcategory C :=
    C.lift (Cq.ι ⋙ Q.ι) (fun F => F.property)
  let unit : 𝟭 (ObjectProperty.FullSubcategory C) ≅ F₁ ⋙ G₁ :=
    NatIso.ofComponents (fun F => C.isoMk (Iso.refl F.obj)) (fun _ => C.hom_ext rfl)
  let counit : G₁ ⋙ F₁ ≅ 𝟭 (ObjectProperty.FullSubcategory Cq) :=
    NatIso.ofComponents (fun F => Cq.isoMk (Q.isoMk (Iso.refl F.obj.obj)))
      (fun _ => Cq.hom_ext rfl)
  exact
    { functor := F₁
      inverse := G₁
      unitIso := unit
      counitIso := counit
      functor_unitIso_comp := fun F => Cq.hom_ext rfl }

/-- The equivalence `M ↦ M̃` between `R`-modules and quasi-coherent `𝒪_{Spec R}`-modules
restricts, for `R` Noetherian, to an equivalence between finitely generated `R`-modules and
coherent `𝒪_{Spec R}`-modules. -/
def fgModuleCatEquivCoherentQuasicoherent (R : Type u) [CommRing R] [IsNoetherianRing R] :
    FGModuleCat.{u} R ≌ AffineCoherentQuasicoherentModules R := by
  let E := AlgebraicGeometry.tildeEquiv (R := CommRingCat.of R)
  let P : ObjectProperty (ModuleCat.{u} (CommRingCat.of R)) := ModuleCat.isFG R
  let Q : ObjectProperty (AffineQuasicoherentModules R) :=
    fun F => Stacks.SheafOfModules.IsCoherent F.obj
  have hPQ : Q.inverseImage E.functor = P := by
    ext M
    change Stacks.SheafOfModules.IsCoherent (AlgebraicGeometry.tilde M) ↔ Module.Finite R M
    exact tilde_isCoherent_iff R M
  have : Q.IsClosedUnderIsomorphisms := ⟨by
    intro X Y e hX
    refine (isCoherent_iff_isCoherent' Y.obj).mpr
      (((CoherentTFAE.coherent_tfae (Spec (CommRingCat.of R)) Y.obj).out 1 2).mpr ?_)
    have : X.obj.IsFiniteType := hX.isFiniteType
    let e' : X.obj ≅ Y.obj :=
      (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of R)).ringCatSheaf).ι.mapIso e
    exact ⟨Y.property,
      Stacks.SheafOfModules.isFiniteType_of_iso.{u} (M := X.obj) (N := Y.obj) e'⟩⟩
  exact Equivalence.congrFullSubcategory E hPQ

/-- For a Noetherian ring `R`, taking `M` to `M̃` is an equivalence from finitely generated
`R`-modules to coherent `𝒪_{Spec R}`-modules. -/
def coherentModulesEquivFGModuleCat (R : Type u) [CommRing R] [IsNoetherianRing R] :
    Stacks.SheafOfModules.CoherentModules (Spec (CommRingCat.of R)).ringCatSheaf ≌
      FGModuleCat.{u} R :=
  (coherentModulesEquivCoherentQuasicoherent R).trans
    (fgModuleCatEquivCoherentQuasicoherent R).symm

/-! ### Grothendieck groups along an equivalence of abelian categories -/

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]

/-- The homomorphism `K₀(C) →+ K₀(D)` induced by an equivalence of abelian categories. -/
def kZeroMapOfEquivalence (e : C ≌ D) : KZero C →+ KZero D :=
  KZero.lift (fun X => KZero.mk D (e.functor.obj X))
    (fun S hS => KZero.mk_of_shortExact (S.map e.functor) (hS.map_of_exact e.functor))

/-- `kZeroMapOfEquivalence e` sends the class of `X` to the class of `e.functor.obj X`. -/
@[simp]
theorem kZeroMapOfEquivalence_mk (e : C ≌ D) (X : C) :
    kZeroMapOfEquivalence e (KZero.mk C X) = KZero.mk D (e.functor.obj X) :=
  KZero.lift_mk _ _ X

/-- An equivalence of abelian categories induces an isomorphism of Grothendieck groups. -/
def kZeroEquivOfEquivalence (e : C ≌ D) : KZero C ≃+ KZero D :=
  have h₁ : (kZeroMapOfEquivalence e.symm).comp (kZeroMapOfEquivalence e)
      = AddMonoidHom.id (KZero C) :=
    KZero.hom_ext fun X => by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, kZeroMapOfEquivalence_mk,
        Equivalence.symm_functor]
      exact (KZero.mk_eq_of_iso (e.unitIso.app X)).symm
  have h₂ : (kZeroMapOfEquivalence e).comp (kZeroMapOfEquivalence e.symm)
      = AddMonoidHom.id (KZero D) :=
    KZero.hom_ext fun Y => by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, kZeroMapOfEquivalence_mk,
        Equivalence.symm_functor]
      exact KZero.mk_eq_of_iso (e.counitIso.app Y)
  have hleft : Function.LeftInverse (kZeroMapOfEquivalence e.symm)
      (kZeroMapOfEquivalence e) := fun x => by
    simpa using DFunLike.congr_fun h₁ x
  have hright : Function.RightInverse (kZeroMapOfEquivalence e.symm)
      (kZeroMapOfEquivalence e) := fun y => by
    simpa using DFunLike.congr_fun h₂ y
  AddEquiv.ofBijective (kZeroMapOfEquivalence e) ⟨hleft.injective, hright.surjective⟩

/-- `kZeroEquivOfEquivalence e` sends the class of `X` to the class of `e.functor.obj X`. -/
@[simp]
theorem kZeroEquivOfEquivalence_mk (e : C ≌ D) (X : C) :
    kZeroEquivOfEquivalence e (KZero.mk C X) = KZero.mk D (e.functor.obj X) :=
  kZeroMapOfEquivalence_mk e X

/-! ### The Grothendieck group of finitely generated modules -/

/-- A finitely generated `R`-module, viewed as a bundled finite `R`-module. -/
def finModuleOfFG {R : Type u} [CommRing R] (M : FGModuleCat.{u} R) : FinModule R :=
  ⟨M.carrier⟩

/-- The comparison homomorphism `K₀(FGModuleCat R) →+ K'₀(R)`, sending the class of a finitely
generated module to its class as a finite module. -/
def kZeroToKPrime0 (R : Type u) [CommRing R] [IsNoetherianRing R] :
    KZero (FGModuleCat.{u} R) →+ KPrime0 R :=
  KZero.lift (fun M => (finModuleOfFG M).cls) fun S hS => by
    let S' := S.map (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R))
    have hS' : S'.ShortExact := hS.map_of_exact _
    exact FinModule.cls_add_of_ses (finModuleOfFG S.X₂) (finModuleOfFG S.X₁)
      (finModuleOfFG S.X₃) S'.f.hom S'.g.hom hS'.moduleCat_injective_f
      hS'.moduleCat_surjective_g hS'.exact.moduleCat_range_eq_ker

/-- The class in `K₀(FGModuleCat R)` of a bundled finite `R`-module. -/
def kZeroClassOfFinModule (R : Type u) [CommRing R] [IsNoetherianRing R] (N : FinModule R) :
    KZero (FGModuleCat.{u} R) :=
  KZero.mk _ (FGModuleCat.of R N.carrier)

/-- Linearly equivalent finite modules have the same class in `K₀(FGModuleCat R)`. -/
theorem kZeroClassOfFinModule_congr (R : Type u) [CommRing R] [IsNoetherianRing R]
    (N N' : FinModule R) (e : N.carrier ≃ₗ[R] N'.carrier) :
    kZeroClassOfFinModule R N = kZeroClassOfFinModule R N' :=
  KZero.mk_eq_of_iso e.toFGModuleCatIso

/-- A short exact sequence `0 → N' → N → N'' → 0` of finite `R`-modules gives
`[N] = [N'] + [N'']` in `K₀(FGModuleCat R)`. -/
theorem kZeroClassOfFinModule_add_of_shortExact (R : Type u) [CommRing R] [IsNoetherianRing R]
    (N N' N'' : FinModule R) (f : N'.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] N''.carrier)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hexact : LinearMap.range f = LinearMap.ker g) :
    kZeroClassOfFinModule R N = kZeroClassOfFinModule R N' + kZeroClassOfFinModule R N'' := by
  have hfg : g.comp f = 0 := LinearMap.range_le_ker_iff.mp (le_of_eq hexact)
  let S₀ := ShortComplex.moduleCatMk f g hfg
  have hS₀ : S₀.ShortExact :=
    ModuleCat.shortComplex_shortExact S₀ (LinearMap.exact_iff.2 hexact.symm) hf hg
  let S := ShortComplex.mk (FGModuleCat.ofHom f) (FGModuleCat.ofHom g) (FGModuleCat.hom_ext hfg)
  have hS : S.ShortExact := by
    apply (CategoryTheory.ShortExact.shortExact_map_iff
      (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R))).mp
    have heq : S.map (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)) ≅ S₀ :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by rfl) (by rfl)
    exact ShortComplex.shortExact_of_iso heq.symm hS₀
  exact KZero.mk_of_shortExact S hS

/-- The comparison homomorphism `K'₀(R) →+ K₀(FGModuleCat R)`, obtained from the universal
property of `K'₀(R)`. -/
def kPrime0ToKZero (R : Type u) [CommRing R] [IsNoetherianRing R] :
    KPrime0 R →+ KZero (FGModuleCat.{u} R) :=
  Classical.choose <| KPrime0.universalProperty_existence (kZeroClassOfFinModule R)
    (kZeroClassOfFinModule_congr R) (kZeroClassOfFinModule_add_of_shortExact R)

/-- `kPrime0ToKZero` sends the class of a finite module to the class of that module. -/
theorem kPrime0ToKZero_cls (R : Type u) [CommRing R] [IsNoetherianRing R] (N : FinModule R) :
    kPrime0ToKZero R N.cls = kZeroClassOfFinModule R N :=
  Classical.choose_spec (KPrime0.universalProperty_existence (kZeroClassOfFinModule R)
    (kZeroClassOfFinModule_congr R) (kZeroClassOfFinModule_add_of_shortExact R)) N

/-- The Grothendieck group of finitely generated `R`-modules is `K'₀(R)`. -/
def kZeroEquivKPrime0 (R : Type u) [CommRing R] [IsNoetherianRing R] :
    KZero (FGModuleCat.{u} R) ≃+ KPrime0 R :=
  have h₁ : (kZeroToKPrime0 R).comp (kPrime0ToKZero R) = AddMonoidHom.id (KPrime0 R) :=
    KPrime0.hom_ext _ _ fun N => by
      rw [AddMonoidHom.comp_apply, kPrime0ToKZero_cls, AddMonoidHom.id_apply]
      change (finModuleOfFG (FGModuleCat.of R N.carrier)).cls = N.cls
      exact FinModule.cls_eq_of_linearEquiv _ N (LinearEquiv.refl R N.carrier)
  have h₂ : (kPrime0ToKZero R).comp (kZeroToKPrime0 R)
      = AddMonoidHom.id (KZero (FGModuleCat.{u} R)) :=
    KZero.hom_ext fun M => by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
      change kPrime0ToKZero R (finModuleOfFG M).cls = KZero.mk _ M
      rw [kPrime0ToKZero_cls]
      change KZero.mk _ (FGModuleCat.of R (finModuleOfFG M).carrier) = KZero.mk _ M
      have eM : ModuleCat.of R M.carrier ≅ M.obj :=
        { hom := ModuleCat.ofHom LinearMap.id
          inv := ModuleCat.ofHom LinearMap.id
          hom_inv_id := by ext x; rfl
          inv_hom_id := by ext x; rfl }
      exact KZero.mk_eq_of_iso ((ModuleCat.isFG R).fullyFaithfulι.preimageIso eM)
  have hleft : Function.LeftInverse (kPrime0ToKZero R) (kZeroToKPrime0 R) := fun x => by
    simpa using DFunLike.congr_fun h₂ x
  have hright : Function.RightInverse (kPrime0ToKZero R) (kZeroToKPrime0 R) := fun y => by
    simpa using DFunLike.congr_fun h₁ y
  AddEquiv.ofBijective (kZeroToKPrime0 R) ⟨hleft.injective, hright.surjective⟩

/-- `kZeroEquivKPrime0 R` sends the class of a finitely generated module to its class as a finite
module. -/
@[simp]
theorem kZeroEquivKPrime0_mk (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : FGModuleCat.{u} R) :
    kZeroEquivKPrime0 R (KZero.mk _ M) = (finModuleOfFG M).cls := by
  show kZeroToKPrime0 R (KZero.mk _ M) = _
  rw [kZeroToKPrime0, KZero.lift_mk]

/-! ### The comparison for `Spec R` -/

/-- The coherent Grothendieck group of `Spec R` is canonically isomorphic to
the Grothendieck group of finite `R`-modules. -/
@[stacks 0FDH "affine_k0_prime"]
def affineCoherentKZeroEquiv (R : Type u) [CommRing R] [IsNoetherianRing R] :
    AlgebraicGeometry.CoherentKZero (Spec (CommRingCat.of R)) ≃+ KPrime0 R :=
  (kZeroEquivOfEquivalence (coherentModulesEquivFGModuleCat R)).trans (kZeroEquivKPrime0 R)

/-- The affine comparison sends the class of a coherent sheaf associated to a
finite module to the class of that module. -/
@[stacks 0FDH "affine_k0_prime"]
theorem affineCoherentKZeroEquiv_mk (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : FinModule R)
    (F : Stacks.SheafOfModules.CoherentModules (Spec (CommRingCat.of R)).ringCatSheaf)
    (hF : Nonempty (F.obj ≅
      AlgebraicGeometry.tilde (ModuleCat.of (CommRingCat.of R) M.carrier))) :
    affineCoherentKZeroEquiv R (KZero.mk _ F) = M.cls := by
  let E₂ := coherentModulesEquivCoherentQuasicoherent R
  let E₃ := fgModuleCatEquivCoherentQuasicoherent R
  let N : FGModuleCat.{u} R := FGModuleCat.of R M.carrier
  have hFM : Stacks.SheafOfModules.IsCoherent
      (AlgebraicGeometry.tilde (ModuleCat.of (CommRingCat.of R) M.carrier)) :=
    (tilde_isCoherent_iff R (ModuleCat.of (CommRingCat.of R) M.carrier)).mpr M.finite
  let qF : AffineQuasicoherentModules R :=
    ⟨F.obj, by
      have : _root_.SheafOfModules.IsCoherent F.obj :=
        (isCoherent_iff_isCoherent' F.obj).mp F.property
      exact isQuasicoherent_of_isCoherent F.obj⟩
  let qM : AffineQuasicoherentModules R :=
    ⟨AlgebraicGeometry.tilde (ModuleCat.of (CommRingCat.of R) M.carrier), inferInstance⟩
  let cF : AffineCoherentQuasicoherentModules R := ⟨qF, F.property⟩
  let cM : AffineCoherentQuasicoherentModules R := ⟨qM, hFM⟩
  obtain ⟨hFiso⟩ := hF
  have hD : E₂.functor.obj F ≅ E₃.functor.obj N := by
    show cF ≅ cM
    exact ObjectProperty.isoMk _ (ObjectProperty.isoMk _ hFiso)
  have hP : (coherentModulesEquivFGModuleCat R).functor.obj F ≅ N := by
    show E₃.inverse.obj (E₂.functor.obj F) ≅ N
    exact E₃.inverse.mapIso hD ≪≫ (E₃.unitIso.app N).symm
  rw [affineCoherentKZeroEquiv, AddEquiv.trans_apply, kZeroEquivOfEquivalence_mk,
    kZeroEquivKPrime0_mk]
  exact FinModule.cls_eq_of_linearEquiv
    (finModuleOfFG ((coherentModulesEquivFGModuleCat R).functor.obj F)) M
    (FGModuleCat.isoToLinearEquiv hP)

end Stacks.AlgebraicGeometry.GrothendieckGroupAffine

end
