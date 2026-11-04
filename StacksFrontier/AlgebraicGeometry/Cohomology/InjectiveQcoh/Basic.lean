module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ProductIdealSheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Topology.Sheaves.Flasque
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerComplement.Basic
public import StacksFrontier.AlgebraicGeometry.IdealPowerHomColimit.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjects

/-!
# Extending sections of an injective quasi-coherent module

Let `X` be a scheme and `𝒥` an injective object of the category of quasi-coherent
`𝒪_X`-modules. This file reduces the flasqueness of `𝒥` to a single statement about ideal
sheaves: if every section of `𝒥` over an open `U` is the image, under some morphism from a
quasi-coherent sheaf of ideals `𝒦 ⊆ 𝒪_X`, of a section of `𝒦` over `U` whose image in
`𝒪_X` is `1`, then `𝒥` is flasque.

The reduction is the use made of injectivity: such a `𝒦` comes with the monomorphism
`𝒦 ⟶ 𝒪_X`, injectivity extends the morphism `𝒦 ⟶ 𝒥` along it to `𝒪_X ⟶ 𝒥`, and the image
of the global unit section is a global section of `𝒥` restricting to the given one. Flasqueness
follows because a presheaf on a space whose restriction maps out of the whole space are
surjective has all its restriction maps surjective.

Also collected here is the vocabulary of the complement of the closed subscheme attached to a
quasi-coherent sheaf of ideals: over an affine open disjoint from the support the ideal is the
unit ideal, and consequently every power `I ^ n • 𝒪_X` has the section `1` over the whole
complement. That section is the `e` of the reduction above.

## Main definitions

* `AlgebraicGeometry.onePowerSection`: the section `1` of `I ^ n • 𝒪_X` over an open disjoint
  from the support of `I`.

The sheaf of ideals of the reduced induced closed subscheme structure on the complement of an
open is `AlgebraicGeometry.Scheme.IdealSheafData.complementIdeal`, which this file consumes
rather than defines.

## Main results

* `AlgebraicGeometry.ideal_eq_top_of_le_compl_support`: an affine open disjoint from the support
  of a sheaf of ideals carries the unit ideal.
* `AlgebraicGeometry.one_mem_idealPowerMultiple_unit_of_subset_compl_support`: `1` is a section
  of `I ^ n • 𝒪_X` over any open disjoint from the support of `I`.
* `AlgebraicGeometry.idealComplement_openComplementIdeal`: the open complement of the closed
  subscheme cut out by `Scheme.IdealSheafData.complementIdeal U` is `U`.
* `AlgebraicGeometry.exists_sectionOverTop_of_quasicoherentIdealHom`: injectivity turns a
  morphism out of a quasi-coherent sheaf of ideals into a global section of `𝒥`.
* `AlgebraicGeometry.isFlasque_of_injective_quasicoherent_of_forall_exists_idealHom`: the
  reduction of flasqueness to the existence of such morphisms.
* `AlgebraicGeometry.isFlasque_of_injective_quasicoherent_of_forall_exists_idealPowerHom`: the
  same reduction with the sheaf of ideals taken to be a power of
  `Scheme.IdealSheafData.complementIdeal U`, which is the shape in which [Stacks, Tag 01YB]
  supplies it.

## Implementation notes

The morphism out of the sheaf of ideals is extended inside the full subcategory of
quasi-coherent modules, where injectivity is a hypothesis; the inclusion of that subcategory is
faithful, so the monomorphism `𝒦 ⟶ 𝒪_X` of sheaves of modules is still a monomorphism there.
This is why the quasi-coherence of `𝒦` appears as an explicit argument rather than as an
instance.

## References

* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA) is the same reduction
  for sheaves of modules on a ringed space, where the extension by zero plays the part the
  sheaf of ideals plays here.
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB) is the statement that
  supplies the hypothesis of the reduction on a Noetherian scheme.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealPowerHomColimit

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The complement of the closed subscheme attached to a sheaf of ideals -/

/-- An affine open disjoint from the support of a quasi-coherent sheaf of ideals carries the
unit ideal: the zero locus of its ideal of sections there is empty. -/
public lemma ideal_eq_top_of_le_compl_support (I : X.IdealSheafData) (V : X.affineOpens)
    (hV : (V : Set X) ⊆ ((I.support : Set X))ᶜ) : I.ideal V = ⊤ := by
  refine PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp (Set.eq_empty_of_forall_notMem fun p hp => ?_)
  have himg : V.2.fromSpec p ∈
      X.zeroLocus ((I.ideal V : Ideal Γ(X, V)) : Set Γ(X, V)) ∩ (V : Set X) :=
    (V.2.fromSpec_image_zeroLocus _) ▸ ⟨p, hp, rfl⟩
  have hsupp : V.2.fromSpec p ∈ (I.support : Set X) ∩ (V : Set X) :=
    (I.coe_support_inter V) ▸ himg
  exact hV hsupp.2 hsupp.1

/-- Restriction in the unit sheaf of modules sends `1` to `1`. -/
private theorem unit_map_one_of_le {U V : X.Opens} (h : V ≤ U) :
    ((SheafOfModules.unit X.ringCatSheaf).val.map (homOfLE h).op).hom (1 : Γ(X, U)) =
      (1 : Γ(X, V)) :=
  PresheafOfModules.unit_map_one X.ringCatSheaf.obj _

/-- The section `1` of `𝒪_X` over an open `U` disjoint from the support of a quasi-coherent
sheaf of ideals `I` lies in the subsheaf `I ^ n • 𝒪_X`: over every affine open contained in `U`
the ideal of sections of `I` is the unit ideal, and `I ^ n • 𝒪_X` is a subsheaf. -/
public lemma one_mem_idealPowerMultiple_unit_of_subset_compl_support (I : X.IdealSheafData)
    (n : ℕ) (U : X.Opens) (hU : (U : Set X) ⊆ ((I.support : Set X))ᶜ) :
    (1 : Γ(X, U)) ∈
      (idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op U) := by
  refine (idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).isSheaf
    (1 : Γ(X, U)) ?_
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨_, ⟨W, hWaff, rfl⟩, hxW, hWU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  let Wa : X.affineOpens := ⟨W, hWaff⟩
  replace hWU : (Wa : X.Opens) ≤ U := hWU
  have hWS : ((Wa : X.Opens) : Set X) ⊆ ((I.support : Set X))ᶜ := fun y hy => hU (hWU hy)
  refine ⟨Wa, homOfLE hWU, ?_, hxW⟩
  have hmemJ : (1 : Γ(X, (Wa : X.Opens))) ∈ I.ideal Wa ^ n :=
    (Ideal.eq_top_iff_one _).mp (by
      rw [ideal_eq_top_of_le_compl_support I Wa hWS, Ideal.top_pow])
  have hle := le_idealPowerMultiple_obj I n (SheafOfModules.unit X.ringCatSheaf) Wa
  rw [ideal_smul_top_unit Wa.1 (I.ideal Wa ^ n)] at hle
  show ((SheafOfModules.unit X.ringCatSheaf).val.map (homOfLE hWU).op).hom
      (1 : Γ(X, U)) ∈
    (idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op Wa.1)
  rw [unit_map_one_of_le hWU]
  exact hle hmemJ

/-- The support of `Scheme.IdealSheafData.complementIdeal U` is the closed complement of `U`. -/
@[simp]
public lemma coe_support_openComplementIdeal (U : X.Opens) :
    (((Scheme.IdealSheafData.complementIdeal U).support : Closeds X) : Set X) = ((U : Set X))ᶜ :=
  Scheme.IdealSheafData.coe_support_vanishingIdeal _

/-- An open is disjoint from the support of the ideal sheaf of the reduced induced structure on
its complement. -/
public lemma subset_compl_support_openComplementIdeal (U : X.Opens) :
    (U : Set X) ⊆ (((Scheme.IdealSheafData.complementIdeal U).support : Set X))ᶜ := by
  rw [coe_support_openComplementIdeal]
  exact (compl_compl (U : Set X)).ge

/-- The open complement of the closed subscheme cut out by
`Scheme.IdealSheafData.complementIdeal U` is `U`. -/
public lemma idealComplement_openComplementIdeal (U : X.Opens) :
    Stacks.LocalCohomology.idealComplement (Scheme.IdealSheafData.complementIdeal U) = U := by
  refine TopologicalSpace.Opens.ext ?_
  show (((Scheme.IdealSheafData.complementIdeal U).support : Set X))ᶜ = (U : Set X)
  rw [coe_support_openComplementIdeal, compl_compl]

/-- The section `1` of the subsheaf `I ^ n • 𝒪_X` over an open `U` disjoint from the support of
`I`. This is the section a morphism out of `I ^ n • 𝒪_X` has to send to a prescribed section of
the target, in order for the global section produced by injectivity to restrict to it. -/
public def onePowerSection (I : X.IdealSheafData) (n : ℕ) (U : X.Opens)
    (hU : (U : Set X) ⊆ ((I.support : Set X))ᶜ) :
    Γ((idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules, U) :=
  ⟨(1 : Γ(X, U)), one_mem_idealPowerMultiple_unit_of_subset_compl_support I n U hU⟩

/-- The image of `onePowerSection` in `𝒪_X` is `1`. -/
@[simp]
public lemma ι_onePowerSection (I : X.IdealSheafData) (n : ℕ) (U : X.Opens)
    (hU : (U : Set X) ⊆ ((I.support : Set X))ᶜ) :
    (((idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).ι).val.app (op U)).hom
      (onePowerSection I n U hU) = (1 : Γ(X, U)) :=
  rfl

/-! ### Injectivity turns a morphism out of a sheaf of ideals into a global section -/

/-- Let `𝒥` be an injective quasi-coherent module, `𝒦 ⊆ 𝒪_X` a quasi-coherent sheaf of ideals
and `φ : 𝒦 ⟶ 𝒥` a morphism. A section of `𝒦` over `U` whose image in `𝒪_X` is `1` has
`φ`-image a section of `𝒥` over `U` which extends to the whole scheme.

Injectivity is applied to the monomorphism `𝒦 ⟶ 𝒪_X` inside the category of quasi-coherent
modules; the extension sends the global unit section to the required global section of `𝒥`. -/
public theorem exists_sectionOverTop_of_quasicoherentIdealHom
    (J : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) [Injective J]
    (K : (SheafOfModules.unit X.ringCatSheaf).Submodule)
    (hK : K.toSheafOfModules.IsQuasicoherent)
    (φ : K.toSheafOfModules ⟶ J.obj) (U : X.Opens) (e : Γ(K.toSheafOfModules, U))
    (he : (K.ι.val.app (op U)).hom e = (1 : Γ(X, U))) :
    ∃ t : Γ(J.obj, ⊤), (J.obj.val.map (homOfLE (le_top : U ≤ ⊤)).op).hom t
      = (φ.val.app (op U)).hom e := by
  let A : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
    ⟨K.toSheafOfModules, hK⟩
  let O : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
    ⟨SheafOfModules.unit X.ringCatSheaf, unit_isQuasicoherent_and_isFiniteType.1⟩
  let incl : A ⟶ O := ObjectProperty.homMk K.ι
  have hmono : Mono incl := by
    refine (ObjectProperty.ι _).mono_of_mono_map (f := incl) ?_
    show Mono K.ι
    infer_instance
  let φA : A ⟶ J := ObjectProperty.homMk φ
  let ex := Injective.factorThru φA incl
  have hext : K.ι ≫ ex.hom = φ :=
    congrArg InducedCategory.Hom.hom (Injective.comp_factorThru φA incl)
  refine ⟨(ex.hom.val.app (op ⊤)).hom (1 : Γ(X, ⊤)), ?_⟩
  refine (PresheafOfModules.naturality_apply ex.hom.val
    (homOfLE (le_top : U ≤ ⊤)).op (1 : Γ(X, ⊤))).symm.trans ?_
  rw [unit_map_one_of_le le_top, ← he]
  exact congrArg (fun f : K.toSheafOfModules ⟶ J.obj => (f.val.app (op U)).hom e) hext

/-! ### The reduction of flasqueness -/

/-- An injective quasi-coherent `𝒪_X`-module is flasque as soon as every one of its sections
over an open `U` is the `φ`-image of a section of a quasi-coherent sheaf of ideals `𝒦 ⊆ 𝒪_X`
over `U` whose image in `𝒪_X` is `1`, for some morphism `φ : 𝒦 ⟶ 𝒥`.

On a Noetherian scheme the hypothesis holds with `𝒦` a power of the ideal sheaf of the reduced
induced structure on `Uᶜ`, which is the content of [Stacks, Tag 01YB]. -/
public theorem isFlasque_of_injective_quasicoherent_of_forall_exists_idealHom
    (J : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) [Injective J]
    (H : ∀ (U : X.Opens) (s : Γ(J.obj, U)),
      ∃ (K : (SheafOfModules.unit X.ringCatSheaf).Submodule)
        (_ : K.toSheafOfModules.IsQuasicoherent)
        (φ : K.toSheafOfModules ⟶ J.obj) (e : Γ(K.toSheafOfModules, U)),
        (K.ι.val.app (op U)).hom e = (1 : Γ(X, U)) ∧ (φ.val.app (op U)).hom e = s) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj J.obj) where
  epi {V W} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    obtain ⟨K, hK, φ, e, he, hs⟩ := H W.unop s
    obtain ⟨t, ht⟩ := exists_sectionOverTop_of_quasicoherentIdealHom J K hK φ W.unop e he
    refine ⟨(J.obj.val.map (homOfLE (le_top : V.unop ≤ ⊤)).op).hom t, ?_⟩
    have hcomp : (homOfLE (le_top : W.unop ≤ ⊤)).op =
        (homOfLE (le_top : V.unop ≤ ⊤)).op ≫ i.unop.op := Subsingleton.elim _ _
    show (J.obj.val.map i.unop.op).hom
      ((J.obj.val.map (homOfLE (le_top : V.unop ≤ ⊤)).op).hom t) = s
    rw [← PresheafOfModules.map_comp_apply J.obj.val
      (homOfLE (le_top : V.unop ≤ ⊤)).op i.unop.op t, ← hcomp, ht, hs]

/-- **The flasqueness of an injective quasi-coherent module, reduced to Stacks 01YB.** Let `𝒥`
be an injective object of the category of quasi-coherent `𝒪_X`-modules. Suppose that for every
open `U` and every section `s` of `𝒥` over `U` there are an `n` and a morphism
`φ : I ^ n • 𝒪_X ⟶ 𝒥`, where `I` is the sheaf of ideals of the reduced induced structure on
`Uᶜ`, with `φ` sending the section `1` over `U` to `s`. Then `𝒥` is flasque.

The hypothesis is exactly the surjectivity of the canonical map
`colim_n Hom(I ^ n, 𝒥) ⟶ Γ(U, 𝒥)` of [Stacks, Tag 01YB], which holds on a Noetherian scheme. -/
public theorem isFlasque_of_injective_quasicoherent_of_forall_exists_idealPowerHom
    (J : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) [Injective J]
    (H : ∀ (U : X.Opens) (s : Γ(J.obj, U)), ∃ (n : ℕ)
      (φ : (idealPowerMultiple (Scheme.IdealSheafData.complementIdeal U) n
          (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules ⟶ J.obj),
      (φ.val.app (op U)).hom
        (onePowerSection (Scheme.IdealSheafData.complementIdeal U) n U
          (subset_compl_support_openComplementIdeal U)) = s) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj J.obj) := by
  refine isFlasque_of_injective_quasicoherent_of_forall_exists_idealHom J fun U s => ?_
  obtain ⟨n, φ, hφ⟩ := H U s
  exact ⟨idealPowerMultiple (Scheme.IdealSheafData.complementIdeal U) n
      (SheafOfModules.unit X.ringCatSheaf),
    idealPowerMultiple_unit_isQuasicoherent _ n, φ,
    onePowerSection (Scheme.IdealSheafData.complementIdeal U) n U
      (subset_compl_support_openComplementIdeal U),
    ι_onePowerSection _ n U _, hφ⟩

end AlgebraicGeometry

end

end
