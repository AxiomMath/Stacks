module

public import StacksFrontier.AlgebraicGeometry.IntegralReduction.Transport
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.AffineCoverOfOpen
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeGeneration
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectAffine
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.GraphKernelRestriction
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.QuasiCoherentExtension
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SubsheafGlueProperties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending a finite type quasi-coherent submodule from a quasi-compact open

Let `X` be a quasi-compact quasi-separated scheme, `F` a quasi-coherent `𝒪_X`-module, `U` a
quasi-compact open and `G` a quasi-coherent subobject of `F|_U` of finite type. This file produces
a quasi-coherent subobject `G'` of `F` of finite type whose restriction to `U` is `G`, compatibly
with the inclusions into `F`.

## Main definitions

* `AlgebraicGeometry.IsFinitelyGeneratedAt`: a module is finitely generated at a point if some
  neighbourhood of that point carries finitely many generating sections of its restriction.
* `AlgebraicGeometry.generatingSectionsRestrictOfOver` and
  `AlgebraicGeometry.generatingSectionsOfRangeSubset`: generating sections of a restriction, from
  generating sections on the slice site, respectively along a larger open immersion.

## Main results

* `AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_extension`: a quasi-coherent
  subobject of finite type of `F|_U` extends to a quasi-coherent subobject of finite type of `F`.
* `AlgebraicGeometry.exists_finiteTypeSubobject_isIso_app`: a quasi-coherent module whose
  restriction to a quasi-compact open `U` is of finite type has a quasi-coherent submodule of
  finite type which agrees with it on `U`.
* `AlgebraicGeometry.isFiniteType_of_forall_isFinitelyGeneratedAt` and
  `AlgebraicGeometry.isFinitelyGeneratedAt_of_restrict_isFiniteType`: finite type and pointwise
  finite generation determine each other.
* `AlgebraicGeometry.exists_subobject_of_restrict`: the graph kernel of a monomorphism into the
  restriction of a module to an affine open is a submodule which is of finite type there and
  which changes nothing where the monomorphism was already an isomorphism.
* `AlgebraicGeometry.exists_subobject_step`: finite generation near every point of a
  quasi-compact open extends across one more affine open.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.Subsheaf
open Stacks.AlgebraicGeometry.CoherentTFAE

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {M A : X.Modules}

/-! ### Restrictions along open immersions with the same image -/

/-- The restriction of a restriction is the restriction along the composite. -/
private noncomputable def restrictCompIso (M : X.Modules) {Y Z : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (h : Z ⟶ Y) [IsOpenImmersion h] :
    (M.restrict f).restrict h ≅ M.restrict (h ≫ f) :=
  ((Scheme.Modules.restrictFunctorComp h f).app M).symm

/-- Two restrictions along open immersions with the same image differ by the restriction along
the induced isomorphism of the two open subschemes. -/
private noncomputable def restrictRangeEqIso {Y Z : Scheme.{u}} (M : X.Modules)
    (f : Y ⟶ X) (g : Z ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (hr : Set.range f.base = Set.range g.base) :
    M.restrict f ≅ (M.restrict g).restrict (IsOpenImmersion.isoOfRangeEq f g hr).hom :=
  ((Scheme.Modules.restrictFunctorCongr
      (IsOpenImmersion.isoOfRangeEq_hom_fac f g hr)).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp (IsOpenImmersion.isoOfRangeEq f g hr).hom g).app M

/-- Finite type of a restriction depends only on the image of the open immersion. -/
private theorem isFiniteType_restrict_of_range_eq {Y Z : Scheme.{u}} (M : X.Modules)
    (f : Y ⟶ X) (g : Z ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (hr : Set.range f.base = Set.range g.base) (h : (M.restrict g).IsFiniteType) :
    (M.restrict f).IsFiniteType := by
  have hinst := h
  have hκ : IsOpenImmersion (IsOpenImmersion.isoOfRangeEq f g hr).hom :=
    IsOpenImmersion.of_isIso _
  have h1 : ((M.restrict g).restrict (IsOpenImmersion.isoOfRangeEq f g hr).hom).IsFiniteType :=
    isFiniteType_restrict _ _
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u} (restrictRangeEqIso M f g hr).symm

/-- Quasi-coherence of a restriction depends only on the image of the open immersion. -/
private theorem isQuasicoherent_restrict_of_range_eq {Y Z : Scheme.{u}} (M : X.Modules)
    (f : Y ⟶ X) (g : Z ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (hr : Set.range f.base = Set.range g.base) (h : (M.restrict g).IsQuasicoherent) :
    (M.restrict f).IsQuasicoherent := by
  have hinst := h
  have hκ : IsOpenImmersion (IsOpenImmersion.isoOfRangeEq f g hr).hom :=
    IsOpenImmersion.of_isIso _
  have h1 : ((M.restrict g).restrict (IsOpenImmersion.isoOfRangeEq f g hr).hom).IsQuasicoherent :=
    inferInstance
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (restrictRangeEqIso M f g hr).symm h1

/-! ### Opens of an open subscheme -/

/-- The image in `X` of the preimage of `T` in the open subscheme `V` is `T ⊓ V`. -/
private theorem image_pre_eq_inf (V T : X.Opens) : V.ι ''ᵁ pre V T = T ⊓ V := by
  ext x
  exact ⟨by rintro ⟨y, hy, rfl⟩; exact ⟨hy, y.2⟩, fun ⟨hxT, hxV⟩ => ⟨⟨x, hxV⟩, hxT, rfl⟩⟩

/-- The open immersion of the preimage of `T` in the open subscheme `V`, composed with the
inclusion of `V`, has the same image as the inclusion of `T ⊓ V`. -/
private theorem range_pre_ι_comp (V T : X.Opens) :
    Set.range ((pre V T).ι ≫ V.ι).base = Set.range ((T ⊓ V : X.Opens)).ι.base := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Scheme.Opens.range_ι, Set.range_comp,
    ← image_pre_eq_inf V T]
  simp

/-- A module of finite type on `W` restricts, on the open subscheme `V`, to a module of finite type
on the preimage of `W`. -/
private theorem isFiniteType_restrict_pre_of_restrict (N : X.Modules) (V W : X.Opens)
    [(N.restrict W.ι).IsFiniteType] : ((N.restrict V.ι).restrict (pre V W).ι).IsFiniteType := by
  have hft1 : ((N.restrict W.ι).restrict (pre W V).ι).IsFiniteType :=
    isFiniteType_restrict (pre W V).ι (N.restrict W.ι)
  have hft2 : (N.restrict ((pre W V).ι ≫ W.ι)).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} (restrictCompIso N W.ι (pre W V).ι)
  have hft3 : (N.restrict ((pre V W).ι ≫ V.ι)).IsFiniteType :=
    isFiniteType_restrict_of_range_eq N _ _
      (by rw [range_pre_ι_comp, range_pre_ι_comp, inf_comm]) hft2
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u} (restrictCompIso N V.ι (pre V W).ι).symm

/-- A quasi-coherent module on `W` restricts, on the open subscheme `V`, to a quasi-coherent module
on the preimage of `W`. -/
private theorem isQuasicoherent_restrict_pre_of_restrict (N : X.Modules) (V W : X.Opens)
    (h : (N.restrict W.ι).IsQuasicoherent) :
    ((N.restrict V.ι).restrict (pre V W).ι).IsQuasicoherent := by
  have hq1 : ((N.restrict W.ι).restrict (pre W V).ι).IsQuasicoherent := inferInstance
  have hq2 : (N.restrict ((pre W V).ι ≫ W.ι)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (pre W V).toScheme.ringCatSheaf).prop_of_iso
      (restrictCompIso N W.ι (pre W V).ι) hq1
  have hq3 : (N.restrict ((pre V W).ι ≫ V.ι)).IsQuasicoherent :=
    isQuasicoherent_restrict_of_range_eq N _ _
      (by rw [range_pre_ι_comp, range_pre_ι_comp, inf_comm]) hq2
  exact (SheafOfModules.isQuasicoherent (pre V W).toScheme.ringCatSheaf).prop_of_iso
    (restrictCompIso N V.ι (pre V W).ι).symm hq3

/-- Two opens whose supremum is `Y` have preimages in the open subscheme `Y` covering it. -/
private theorem pre_sup_eq_top {W V Y : X.Opens} (hWV : W ⊔ V = Y) : pre Y W ⊔ pre Y V = ⊤ := by
  refine top_le_iff.1 fun y _ => ?_
  have hy : y.1 ∈ W ⊔ V := hWV ▸ y.2
  exact hy

/-! ### Comparing two submodules over an open -/

/-- The range of the inclusion of a submodule is that submodule. -/
private theorem mem_rangeObj_modι (N : SheafOfModules.Submodule M) (T : X.Opens) (s : Γ(M, T)) :
    s ∈ rangeObj (modι N) T ↔ s ∈ N.obj (op T) := by
  refine ⟨fun hs => ?_, fun hs => mem_rangeObj.mpr ⟨mkSection N s hs, rfl⟩⟩
  obtain ⟨w, hw⟩ := mem_rangeObj.mp hs
  rw [← hw]
  exact mem_modι_app N T w

/-- A monomorphism whose restriction to `W` is an isomorphism is surjective on the sections over
every open contained in `W`. -/
private theorem mem_rangeObj_of_isIso_restrict (a : A ⟶ M) (W : X.Opens)
    (h : IsIso ((Scheme.Modules.restrictFunctor W.ι).map a)) {T : X.Opens} (hT : T ≤ W)
    (s : Γ(M, T)) : s ∈ rangeObj a T := by
  have hinst := h
  have hb : ∀ T' : W.toScheme.Opens, Function.Surjective (a.app (W.ι ''ᵁ T')) := by
    intro T'
    have h1 : IsIso (((Scheme.Modules.restrictFunctor W.ι).map a).app T') := inferInstance
    exact ((ConcreteCategory.isIso_iff_bijective _).mp h1).2
  have h3 := hb (pre W T)
  rw [image_pre_eq W hT] at h3
  exact mem_rangeObj.mpr (h3 s)

/-- Two monomorphisms into `M` whose restrictions to `W` differ by an isomorphism have the same
range over every open contained in `W`. -/
private theorem rangeObj_eq_of_restrict_comp {A' : X.Modules} (a : A ⟶ M) (a' : A' ⟶ M)
    (W : X.Opens) (ψ : A'.restrict W.ι ≅ A.restrict W.ι)
    (hψ : ψ.hom ≫ (Scheme.Modules.restrictFunctor W.ι).map a =
      (Scheme.Modules.restrictFunctor W.ι).map a')
    {T : X.Opens} (hT : T ≤ W) : rangeObj a' T = rangeObj a T := by
  have key : ∀ T' : W.toScheme.Opens, rangeObj a' (W.ι ''ᵁ T') = rangeObj a (W.ι ''ᵁ T') := by
    intro T'
    have happ : ∀ x : Γ(A'.restrict W.ι, T'),
        a'.app (W.ι ''ᵁ T') x = a.app (W.ι ''ᵁ T') (ψ.hom.app T' x) := by
      intro x
      have h1 := congrArg (fun f : A'.restrict W.ι ⟶ M.restrict W.ι => f.app T') hψ
      have h2 := congr($h1 x)
      simp only [Scheme.Modules.Hom.comp_app, comp_apply] at h2
      exact h2.symm
    have hinv : ∀ y : Γ(A.restrict W.ι, T'), ψ.hom.app T' (ψ.inv.app T' y) = y := by
      intro y
      have h3 := congrArg (fun f : A.restrict W.ι ⟶ A.restrict W.ι => f.app T') ψ.inv_hom_id
      have h4 := congr($h3 y)
      simpa only [Scheme.Modules.Hom.comp_app, comp_apply, Scheme.Modules.Hom.id_app,
        id_apply] using h4
    refine SetLike.ext fun s => ⟨fun hs => ?_, fun hs => ?_⟩
    · obtain ⟨x, hx⟩ := mem_rangeObj.mp hs
      exact mem_rangeObj.mpr ⟨ψ.hom.app T' x, (happ x).symm.trans hx⟩
    · obtain ⟨y, hy⟩ := mem_rangeObj.mp hs
      refine mem_rangeObj.mpr ⟨ψ.inv.app T' y, (happ (ψ.inv.app T' y)).trans ?_⟩
      exact (congrArg (fun z => a.app (W.ι ''ᵁ T') z) (hinv y)).trans hy
  have h5 := key (pre W T)
  rwa [image_pre_eq W hT] at h5

/-- The inclusion of a submodule which is everything over `U` is an isomorphism over `U`. -/
private theorem isIso_restrict_modι (N : SheafOfModules.Submodule M) (U : X.Opens)
    (h : ∀ T : X.Opens, T ≤ U → ∀ s : Γ(M, T), s ∈ N.obj (op T)) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (modι N)) := by
  refine isIso_of_bijective_app _ fun T => ?_
  rw [app_restrict_map]
  refine ⟨fun x y hxy => injective_app (modι N) _ hxy, fun y => ?_⟩
  exact ⟨mkSection N y (h _ (image_le U T) y), rfl⟩

/-! ### The gluing over an open rather than over the whole scheme -/

/-- If `B` and `C` are submodules of `M` with `B ≤ C` over `W` and `C ≤ B` over `V`, of finite
type over `W` and over `V` respectively, then their intersection is of finite type over
`Y = W ⊔ V`. -/
private theorem isFiniteType_inter_restrict {W V Y : X.Opens} (hWV : W ⊔ V = Y)
    (B C : SheafOfModules.Submodule M)
    (h1 : ∀ T : X.Opens, T ≤ W → B.obj (op T) ≤ C.obj (op T))
    (h2 : ∀ T : X.Opens, T ≤ V → C.obj (op T) ≤ B.obj (op T))
    (hB : ((mod B).restrict W.ι).IsFiniteType)
    (hC : ((mod C).restrict V.ι).IsFiniteType) :
    ((mod (inter B C)).restrict Y.ι).IsFiniteType := by
  have hiW := isIso_restrict_inclusion_inf_left B C h1
  have hiV := isIso_restrict_inclusion_inf_right B C h2
  have hIW : ((mod (inter B C)).restrict W.ι).IsFiniteType := by
    have := hB
    exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      (asIso ((Scheme.Modules.restrictFunctor W.ι).map
        (inclusion (N := inter B C) (N' := B) (fun _ => inf_le_left)))).symm
  have hIV : ((mod (inter B C)).restrict V.ι).IsFiniteType := by
    have := hC
    exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      (asIso ((Scheme.Modules.restrictFunctor V.ι).map
        (inclusion (N := inter B C) (N' := C) (fun _ => inf_le_right)))).symm
  have hW3 := isFiniteType_restrict_pre_of_restrict (mod (inter B C)) Y W
  have hV3 := isFiniteType_restrict_pre_of_restrict (mod (inter B C)) Y V
  refine isFiniteType_of_iSup_eq_top _ (fun bb : Bool => if bb then pre Y W else pre Y V) ?_ ?_
  · rw [iSup_bool_eq]
    simpa using pre_sup_eq_top hWV
  · intro bb
    cases bb
    · simpa using hV3
    · simpa using hW3

/-- If `B` and `C` are submodules of `M` with `B ≤ C` over `W` and `C ≤ B` over `V`,
quasi-coherent over `W` and over `V` respectively, then their intersection is quasi-coherent over
`Y = W ⊔ V`. -/
private theorem isQuasicoherent_inter_restrict {W V Y : X.Opens} (hWV : W ⊔ V = Y)
    (B C : SheafOfModules.Submodule M)
    (h1 : ∀ T : X.Opens, T ≤ W → B.obj (op T) ≤ C.obj (op T))
    (h2 : ∀ T : X.Opens, T ≤ V → C.obj (op T) ≤ B.obj (op T))
    (hB : ((mod B).restrict W.ι).IsQuasicoherent)
    (hC : ((mod C).restrict V.ι).IsQuasicoherent) :
    ((mod (inter B C)).restrict Y.ι).IsQuasicoherent := by
  have hiW := isIso_restrict_inclusion_inf_left B C h1
  have hiV := isIso_restrict_inclusion_inf_right B C h2
  have hIW : ((mod (inter B C)).restrict W.ι).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso
      (asIso ((Scheme.Modules.restrictFunctor W.ι).map
        (inclusion (N := inter B C) (N' := B) (fun _ => inf_le_left)))).symm hB
  have hIV : ((mod (inter B C)).restrict V.ι).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso
      (asIso ((Scheme.Modules.restrictFunctor V.ι).map
        (inclusion (N := inter B C) (N' := C) (fun _ => inf_le_right)))).symm hC
  have hW3 := isQuasicoherent_restrict_pre_of_restrict (mod (inter B C)) Y W hIW
  have hV3 := isQuasicoherent_restrict_pre_of_restrict (mod (inter B C)) Y V hIV
  refine isQuasicoherent_of_iSup_eq_top _
    (fun bb : Bool => if bb then pre Y W else pre Y V) ?_ ?_
  · rw [iSup_bool_eq]
    simpa using pre_sup_eq_top hWV
  · intro bb
    cases bb
    · simpa using hV3
    · simpa using hW3

/-! ### The two steps of the induction -/

/-- A submodule `N` of a quasi-coherent module `M` whose restriction to a quasi-compact open `W`
is quasi-coherent and of finite type agrees over `W` with a quasi-coherent submodule `B` of `M`
which is of finite type over `W`. -/
private theorem exists_quasicoherentSubmodule_eq_of_le [QuasiSeparatedSpace X]
    (M : X.Modules) [M.IsQuasicoherent] (N : SheafOfModules.Submodule M)
    (W : X.Opens) (hW : IsCompact W.1)
    (hNqc : ((mod N).restrict W.ι).IsQuasicoherent)
    (hNft : ((mod N).restrict W.ι).IsFiniteType) :
    ∃ B : SheafOfModules.Submodule M, (mod B).IsQuasicoherent ∧
      ((mod B).restrict W.ι).IsFiniteType ∧
      ∀ T : X.Opens, T ≤ W → B.obj (op T) = N.obj (op T) := by
  have hqcW : QuasiCompact W.ι := quasiCompact_opens_ι hW
  have hmono : Mono ((Scheme.Modules.restrictFunctor W.ι).map (modι N)) :=
    mono_restrictFunctor_map W.ι (modι N)
  have hSqc : ((Subobject.mk ((Scheme.Modules.restrictFunctor W.ι).map (modι N))) :
      W.toScheme.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso ((Scheme.Modules.restrictFunctor W.ι).map (modι N))).symm hNqc
  obtain ⟨B₀, hB₀qc, eB, heB⟩ := exists_quasicoherentSubobject_restrict W.ι M
    (Subobject.mk ((Scheme.Modules.restrictFunctor W.ι).map (modι N))) hSqc
  refine ⟨ofMono B₀.arrow, ?_, ?_, ?_⟩
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (isoOfMono B₀.arrow) hB₀qc
  · have hft := hNft
    exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      ((Subobject.underlyingIso ((Scheme.Modules.restrictFunctor W.ι).map (modι N))).symm ≪≫
        eB.symm ≪≫ (Scheme.Modules.restrictFunctor W.ι).mapIso (isoOfMono B₀.arrow))
  · intro T hT
    obtain ⟨ψ, hψ⟩ : ∃ ψ : (mod (ofMono B₀.arrow)).restrict W.ι ≅ (mod N).restrict W.ι,
        ψ.hom ≫ (Scheme.Modules.restrictFunctor W.ι).map (modι N) =
          (Scheme.Modules.restrictFunctor W.ι).map (modι (ofMono B₀.arrow)) := by
      refine ⟨((Scheme.Modules.restrictFunctor W.ι).mapIso (isoOfMono B₀.arrow)).symm ≪≫ eB ≪≫
        Subobject.underlyingIso ((Scheme.Modules.restrictFunctor W.ι).map (modι N)), ?_⟩
      have harrow := (Subobject.underlyingIso_hom_comp_eq_mk
        ((Scheme.Modules.restrictFunctor W.ι).map (modι N))).symm
      have hmodιB : (isoOfMono B₀.arrow).inv ≫ B₀.arrow = modι (ofMono B₀.arrow) :=
        calc (isoOfMono B₀.arrow).inv ≫ B₀.arrow
            = (isoOfMono B₀.arrow).inv ≫
              (isoOfMono B₀.arrow).hom ≫ modι (ofMono B₀.arrow) := by
              rw [isoOfMono_hom_comp B₀.arrow]
          _ = modι (ofMono B₀.arrow) := Iso.inv_hom_id_assoc _ _
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Category.assoc]
      rw [← harrow, heB, ← Functor.map_comp, hmodιB]
    have h := rangeObj_eq_of_restrict_comp (modι N) (modι (ofMono B₀.arrow)) W ψ hψ hT
    refine SetLike.ext fun x : Γ(M, T) => ?_
    refine Iff.trans (mem_rangeObj_modι (ofMono B₀.arrow) T x).symm ?_
    rw [h]
    exact mem_rangeObj_modι N T x

/-- **One affine extension step.** Given a submodule `B` of `M` which is quasi-coherent and of
finite type over a quasi-compact open `W`, and an affine open `V`, there is a submodule `C` of `M`
which is quasi-coherent and of finite type over `V`, contains `B` over `W` and is contained in `B`
over `V`. -/
@[ega "I 9.4.3" "affine case"]
private theorem exists_finiteTypeSubmodule_of_isAffineOpen [QuasiSeparatedSpace X] (M : X.Modules)
    (B : SheafOfModules.Submodule M) (hBqc : (mod B).IsQuasicoherent)
    (W : X.Opens) (hW : IsCompact W.1) (hBft : ((mod B).restrict W.ι).IsFiniteType)
    (V : X.Opens) (hVa : IsAffineOpen V) :
    ∃ C : SheafOfModules.Submodule M,
      ((mod C).restrict V.ι).IsQuasicoherent ∧
      ((mod C).restrict V.ι).IsFiniteType ∧
      (∀ T : X.Opens, T ≤ W → B.obj (op T) ≤ C.obj (op T)) ∧
      (∀ T : X.Opens, T ≤ V → C.obj (op T) ≤ B.obj (op T)) := by
  have hqcV : QuasiCompact V.ι := quasiCompact_opens_ι hVa.isCompact
  have hPc : IsCompact (pre V W).1 := V.ι.isCompact_preimage hW
  have hVaff : IsAffine V.toScheme := hVa
  have hft4 : (((mod B).restrict V.ι).restrict (pre V W).ι).IsFiniteType :=
    isFiniteType_restrict_pre_of_restrict (mod B) V W
  obtain ⟨C₀, hC₀qc, hC₀ft, hC₀iso⟩ :=
    exists_finiteTypeQuasicoherentSubobject_isIso_restrict_of_isAffine
      ((mod B).restrict V.ι) (pre V W) hPc
  have hmono : Mono (C₀.arrow ≫ (Scheme.Modules.restrictFunctor V.ι).map (modι B)) :=
    mono_comp _ _
  refine ⟨push V (ofMono (C₀.arrow ≫ (Scheme.Modules.restrictFunctor V.ι).map (modι B))),
    ?_, ?_, ?_, ?_⟩
  · exact (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso
      (isoOfMono (C₀.arrow ≫ (Scheme.Modules.restrictFunctor V.ι).map (modι B)) ≪≫
        pushRestrictIso V _) hC₀qc
  · exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      (isoOfMono (C₀.arrow ≫ (Scheme.Modules.restrictFunctor V.ι).map (modι B)) ≪≫
        pushRestrictIso V _)
  · refine le_push_of_le_image B _ ?_
    intro T' hT'W s hs
    have hT'le : T' ≤ pre V W := fun x hx => hT'W ⟨x, hx, rfl⟩
    obtain ⟨x, hx⟩ := mem_rangeObj.mp (mem_rangeObj_of_isIso_restrict C₀.arrow (pre V W)
      hC₀iso hT'le (mkSection B s hs))
    refine mem_rangeObj.mpr ⟨x, ?_⟩
    simp only [Scheme.Modules.Hom.comp_app, comp_apply]
    rw [app_restrict_map, hx]
    exact modι_app_mkSection B s hs
  · refine push_le_of_le_image B _ ?_
    intro T' s hs
    obtain ⟨x, hx⟩ := mem_rangeObj.mp hs
    rw [← hx]
    simp only [Scheme.Modules.Hom.comp_app, comp_apply]
    rw [app_restrict_map]
    exact mem_modι_app B _ _

/-! ### The induction -/

/-- For every `Finset` of affine opens of a quasi-separated scheme there is a submodule of `M`
which is everything over the quasi-compact open `U`, and which is quasi-coherent and of finite
type over `U` together with the members of the `Finset`. -/
private theorem exists_submodule_of_finset_affineOpens [QuasiSeparatedSpace X] (M : X.Modules)
    [M.IsQuasicoherent] (U : X.Opens) (hU : IsCompact U.1)
    [(M.restrict U.ι).IsFiniteType] (s : Finset X.affineOpens) :
    ∃ N : SheafOfModules.Submodule M,
      (∀ T : X.Opens, T ≤ U → ∀ x : Γ(M, T), x ∈ N.obj (op T)) ∧
      ((mod N).restrict (U ⊔ ⨆ V ∈ s, (V : X.Opens)).ι).IsQuasicoherent ∧
      ((mod N).restrict (U ⊔ ⨆ V ∈ s, (V : X.Opens)).ι).IsFiniteType := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hemp : U ⊔ (⨆ V ∈ (∅ : Finset X.affineOpens), (V : X.Opens)) = U := by simp
    refine ⟨push U (ofMono (𝟙 (M.restrict U.ι))), ?_, ?_, ?_⟩
    · intro T hT x
      exact (mem_push_iff U _ x).mpr
        (mem_rangeObj.mpr ⟨res M (image_pre_le U T) x, rfl⟩)
    · rw [hemp]
      exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
        (isoOfMono (𝟙 (M.restrict U.ι)) ≪≫ pushRestrictIso U _) inferInstance
    · rw [hemp]
      exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
        (isoOfMono (𝟙 (M.restrict U.ι)) ≪≫ pushRestrictIso U _)
  | @insert V s hV ih =>
    obtain ⟨N, hNU, hNqc, hNft⟩ := ih
    have hWc : IsCompact (U ⊔ ⨆ V' ∈ s, (V' : X.Opens)).1 :=
      isCompact_sup_biSup_affineOpens hU s
    obtain ⟨B, hBqc, hBft, hBN⟩ :=
      exists_quasicoherentSubmodule_eq_of_le M N _ hWc hNqc hNft
    obtain ⟨C, hCqc, hCft, hBC, hCB⟩ :=
      exists_finiteTypeSubmodule_of_isAffineOpen M B hBqc _ hWc hBft (V : X.Opens) V.2
    have hsup : (U ⊔ ⨆ V' ∈ s, (V' : X.Opens)) ⊔ (V : X.Opens)
        = U ⊔ ⨆ V' ∈ insert V s, (V' : X.Opens) := by
      rw [Finset.iSup_insert, sup_assoc, sup_comm (⨆ V' ∈ s, (V' : X.Opens))]
    have hBqcW : ((mod B).restrict (U ⊔ ⨆ V' ∈ s, (V' : X.Opens)).ι).IsQuasicoherent := by
      have := hBqc
      infer_instance
    refine ⟨inter B C, ?_, ?_, ?_⟩
    · intro T hT x
      have hTW : T ≤ U ⊔ ⨆ V' ∈ s, (V' : X.Opens) := hT.trans le_sup_left
      have hxB : x ∈ B.obj (op T) := by
        rw [hBN T hTW]
        exact hNU T hT x
      exact ⟨hxB, hBC T hTW hxB⟩
    · exact isQuasicoherent_inter_restrict hsup B C hBC hCB hBqcW hCqc
    · exact isFiniteType_inter_restrict hsup B C hBC hCB hBft hCft

/-! ### Extending a finite type quasi-coherent subobject -/

/-- Let `X` be a quasi-compact quasi-separated scheme, `F` a quasi-coherent `𝒪_X`-module, `U` a
quasi-compact open and `G` a quasi-coherent subobject of `F|_U` of finite type. Then `G` extends to
a quasi-coherent subobject of `F` of finite type: there is a quasi-coherent subobject `G'` of `F`
of finite type and an isomorphism of `G'|_U` with `G` compatible with the inclusions into `F|_U`.
-/
@[stacks 01PF, ega "I 9.4.6" "qcqs case", ega "I 9.4.3" "qcqs scheme", ega "I 9.4.7" "(b)"]
theorem exists_finiteTypeQuasicoherentSubobject_extension
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsCompact U.1)
    (G : CategoryTheory.Subobject (F.restrict U.ι))
    [(G : U.toScheme.Modules).IsQuasicoherent]
    [(G : U.toScheme.Modules).IsFiniteType] :
    ∃ (G' : CategoryTheory.Subobject F), (G' : X.Modules).IsQuasicoherent ∧
      (G' : X.Modules).IsFiniteType ∧
      ∃ e : (G' : X.Modules).restrict U.ι ≅ (G : U.toScheme.Modules),
        (Scheme.Modules.restrictFunctor U.ι).map G'.arrow = e.hom ≫ G.arrow := by
  have hqcU : QuasiCompact U.ι := quasiCompact_opens_ι hU
  obtain ⟨H, hHqc, e0, he0⟩ := exists_quasicoherentSubobject_restrict U.ι F G inferInstance
  have hHqc' := hHqc
  have hMUft : ((H : X.Modules).restrict U.ι).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} e0.symm
  obtain ⟨s, hs⟩ := exists_finset_affineOpens_sup_eq_top (X := X) U
  obtain ⟨N, hNU, hNqc, hNft⟩ :=
    exists_submodule_of_finset_affineOpens (H : X.Modules) U hU s
  rw [hs] at hNqc hNft
  have hNqcg : (mod N).IsQuasicoherent :=
    isQuasicoherent_of_iSup_eq_top (mod N) (fun _ : Unit => (⊤ : X.Opens)) (by simp)
      (fun _ => hNqc)
  have hNftg : (mod N).IsFiniteType := (isFiniteType_restrict_top_iff (mod N)).mp hNft
  have hiso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (modι N)) :=
    isIso_restrict_modι N U hNU
  have hmono : Mono (modι N ≫ H.arrow) := mono_comp _ _
  refine ⟨Subobject.mk (modι N ≫ H.arrow), ?_, ?_, ?_⟩
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso (modι N ≫ H.arrow)).symm hNqcg
  · exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      (Subobject.underlyingIso (modι N ≫ H.arrow)).symm
  · refine ⟨(Scheme.Modules.restrictFunctor U.ι).mapIso
      (Subobject.underlyingIso (modι N ≫ H.arrow)) ≪≫
      asIso ((Scheme.Modules.restrictFunctor U.ι).map (modι N)) ≪≫ e0, ?_⟩
    have harrow := (Subobject.underlyingIso_hom_comp_eq_mk (modι N ≫ H.arrow)).symm
    rw [harrow, Functor.map_comp, Functor.map_comp]
    simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Category.assoc]
    rw [he0]

/-! ### Pointwise finite generation and the subobject form of the extension -/

section Pointwise

open CategoryTheory.Limits _root_.SheafOfModules
open Stacks.AlgebraicGeometry.Tag01YEIntegralReduction
  (isIso_restrictFunctor_map_of_forall_app isIso_app_of_isIso_restrictFunctor_map)

/-- Generating sections of a restriction, from generating sections on the slice site. -/
noncomputable def generatingSectionsRestrictOfOver (V : X.Opens) (N : X.Modules)
    (σ : (N.over V).GeneratingSections) : (N.restrict V.ι).GeneratingSections :=
  GeneratingSections.equivOfIso ((Scheme.Modules.overFunctorEquiv V).app N)
    (@GeneratingSections.map _ _ _ _ _ _ _ _ _ _ _ _ _ σ
      (V.sheafOfModulesEquivOver X.ringCatSheaf).functor
      ((V.sheafOfModulesEquivOver X.ringCatSheaf).toAdjunction.leftAdjoint_preservesColimits)
      (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit V X.ringCatSheaf))

/-- The index type of `generatingSectionsRestrictOfOver V N σ` is that of `σ`. -/
@[simp]
theorem generatingSectionsRestrictOfOver_I (V : X.Opens) (N : X.Modules)
    (σ : (N.over V).GeneratingSections) :
    (generatingSectionsRestrictOfOver V N σ).I = σ.I := rfl

/-- Generating sections restrict from a larger open immersion to a smaller one. -/
noncomputable def generatingSectionsOfRangeSubset {Z Z' : Scheme.{u}} (N : X.Modules)
    (f : Z ⟶ X) [IsOpenImmersion f] (f' : Z' ⟶ X) [IsOpenImmersion f']
    (h : Set.range f'.base ⊆ Set.range f.base)
    (σ : (N.restrict f).GeneratingSections) : (N.restrict f').GeneratingSections :=
  GeneratingSections.equivOfIso
    (((Scheme.Modules.restrictFunctorComp (IsOpenImmersion.lift f f' h) f).app N).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (IsOpenImmersion.lift_fac f f' h)).app N)
    (generatingSectionsRestrict (IsOpenImmersion.lift f f' h) σ)

/-- The index type of `generatingSectionsOfRangeSubset N f f' h σ` is that of `σ`. -/
@[simp]
theorem generatingSectionsOfRangeSubset_I {Z Z' : Scheme.{u}} (N : X.Modules)
    (f : Z ⟶ X) [IsOpenImmersion f] (f' : Z' ⟶ X) [IsOpenImmersion f']
    (h : Set.range f'.base ⊆ Set.range f.base)
    (σ : (N.restrict f).GeneratingSections) :
    (generatingSectionsOfRangeSubset N f f' h σ).I = σ.I := rfl

/-- `N` is generated by finitely many sections on some neighbourhood of `x`. -/
def IsFinitelyGeneratedAt (N : X.Modules) (x : X) : Prop :=
  ∃ (V : X.Opens) (_ : x ∈ V) (σ : (N.restrict V.ι).GeneratingSections), Finite σ.I

/-- A module which is generated by finitely many sections near every point is of finite type. -/
theorem isFiniteType_of_forall_isFinitelyGeneratedAt (N : X.Modules)
    (h : ∀ x : X, IsFinitelyGeneratedAt N x) : N.IsFiniteType := by
  choose V hxV σ hσ using h
  exact isFiniteType_of_restrict_generatingSections N V
    (IsOpenCover.mk (top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hxV x⟩)) σ hσ

/-- A module of finite type on an open is generated by finitely many sections near every point
of that open. -/
theorem isFinitelyGeneratedAt_of_restrict_isFiniteType (N : X.Modules) (A : X.Opens)
    (h : ((Scheme.Modules.restrictFunctor A.ι).obj N).IsFiniteType) {x : X} (hx : x ∈ A) :
    IsFinitelyGeneratedAt N x := by
  obtain ⟨V', hyV', σ, hσ⟩ := Stacks.SheafOfModules.isFiniteTypeAt_of_isFiniteType
    ((Scheme.Modules.restrictFunctor A.ι).obj N) h ⟨x, hx⟩
  refine ⟨A.ι ''ᵁ V', ⟨⟨x, hx⟩, hyV', rfl⟩,
    generatingSectionsOfRangeSubset N (Scheme.Opens.ι V' ≫ A.ι) (A.ι ''ᵁ V').ι ?_
      (GeneratingSections.equivOfIso
        ((Scheme.Modules.restrictFunctorComp (Scheme.Opens.ι V') A.ι).app N).symm
        (generatingSectionsRestrictOfOver V' _ σ)), hσ.finite⟩
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨⟨w, hw⟩, rfl⟩

/-- Finite generation near a point transports along an isomorphism. -/
theorem isFinitelyGeneratedAt_of_iso {N P : X.Modules} (e : N ≅ P) {x : X}
    (h : IsFinitelyGeneratedAt N x) : IsFinitelyGeneratedAt P x := by
  obtain ⟨V, hxV, σ, hσ⟩ := h
  exact ⟨V, hxV, GeneratingSections.equivOfIso
    ((Scheme.Modules.restrictFunctor V.ι).mapIso e) σ, hσ⟩

/-- Finite generation near a point transports along a morphism which is bijective on sections
over the opens of a neighbourhood of that point. -/
theorem isFinitelyGeneratedAt_of_isIso_app {N P : X.Modules} (g : N ⟶ P) {V : X.Opens}
    (hg : ∀ W : X.Opens, W ≤ V → IsIso (g.app W)) {x : X} (hx : x ∈ V)
    (h : IsFinitelyGeneratedAt P x) : IsFinitelyGeneratedAt N x := by
  obtain ⟨V₀, hxV₀, σ, hσ⟩ := h
  have hran : Set.range (V₀ ⊓ V).ι.base ⊆ Set.range V₀.ι.base := by
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact fun z hz => hz.1
  have hiso : IsIso ((Scheme.Modules.restrictFunctor (V₀ ⊓ V).ι).map g) :=
    isIso_restrictFunctor_map_of_forall_app g (V₀ ⊓ V)
      (fun W hW => hg W (hW.trans inf_le_right))
  exact ⟨V₀ ⊓ V, ⟨hxV₀, hx⟩,
    GeneratingSections.equivOfIso (@asIso _ _ _ _ _ hiso).symm
      (generatingSectionsOfRangeSubset P V₀.ι (V₀ ⊓ V).ι hran σ), hσ⟩

/-- Finite generation near a point passes to the restriction along an open immersion. -/
theorem isFinitelyGeneratedAt_restrict {Z : Scheme.{u}} (f : Z ⟶ X) [IsOpenImmersion f]
    (N : X.Modules) (z : Z) (h : IsFinitelyGeneratedAt N (f.base z)) :
    IsFinitelyGeneratedAt ((Scheme.Modules.restrictFunctor f).obj N) z := by
  obtain ⟨V₀, hxV₀, σ, hσ⟩ := h
  have hran : Set.range ((f ⁻¹ᵁ V₀).ι ≫ f).base ⊆ Set.range V₀.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨v, rfl⟩
    exact v.2
  refine ⟨f ⁻¹ᵁ V₀, hxV₀, GeneratingSections.equivOfIso
    ((Scheme.Modules.restrictFunctorComp (f ⁻¹ᵁ V₀).ι f).app N)
    (generatingSectionsOfRangeSubset N V₀.ι ((f ⁻¹ᵁ V₀).ι ≫ f) hran σ), hσ⟩

/-- The intersection of two quasi-compact opens of a quasi-separated scheme is quasi-compact,
read as an open of the second one. -/
theorem isCompact_preimage_ι_of_quasiSeparatedSpace {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (V Y : X.Opens)
    (hVc : IsCompact (V : Set X)) (hYc : IsCompact (Y : Set X)) :
    IsCompact ((Y.ι ⁻¹ᵁ V : Y.toScheme.Opens) : Set Y.toScheme) := by
  rw [(Y.ι.isOpenEmbedding.isEmbedding).isCompact_iff]
  have himg : (Y.ι.base '' ((Y.ι ⁻¹ᵁ V : Y.toScheme.Opens) : Set Y.toScheme)) =
      (V : Set X) ∩ (Y : Set X) := by
    change ⇑Y.ι '' (⇑Y.ι ⁻¹' (V : Set X)) = _
    rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
  rw [himg]
  exact QuasiSeparatedSpace.inter_isCompact _ _ V.2 hVc Y.2 hYc

/-- If `φ` is a monomorphism into the restriction of `C` to an affine open `Y` which is already
bijective on sections over the opens lying in `V`, then the graph kernel of `φ` is a quasi-coherent
submodule of `C` which is bijective on sections over the opens lying in `V` and whose restriction
to `Y` is of finite type. -/
theorem exists_subobject_of_restrict {X : Scheme.{u}} (C : X.Modules) [C.IsQuasicoherent]
    (Y : X.Opens) [QuasiCompact Y.ι] (V : X.Opens)
    (B : Y.toScheme.Modules) [B.IsQuasicoherent] [B.IsFiniteType]
    (φ : B ⟶ (Scheme.Modules.pullback Y.ι).obj C) [Mono φ]
    (hφ : ∀ W' : Y.toScheme.Opens, Y.ι ''ᵁ W' ≤ V → IsIso (φ.app W')) :
    ∃ (K : X.Modules) (_ : K.IsQuasicoherent) (p : K ⟶ C) (_ : Mono p),
      (∀ W : X.Opens, W ≤ V → IsIso (p.app W)) ∧
      ((Scheme.Modules.restrictFunctor Y.ι).obj K).IsFiniteType := by
  have hpush : IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      ((Scheme.Modules.pushforward Y.ι).map φ)) :=
    isIso_restrict_pushforward_map Y V φ hφ
  have hpiso : IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      (Scheme.Modules.graphKernelProjection Y.ι C B φ)) :=
    graphKernelProjection_restrict_isIso Y.ι C B φ V
  refine ⟨Scheme.Modules.graphKernel Y.ι C B φ, inferInstance,
    Scheme.Modules.graphKernelProjection Y.ι C B φ,
    Scheme.Modules.graphKernelProjection_mono Y.ι C B φ, ?_, ?_⟩
  · exact fun W hW => isIso_app_of_isIso_restrictFunctor_map _ V hpiso W hW
  · exact isFiniteType_of_iso_modules
      ((Scheme.Modules.restrictFunctorIsoPullback Y.ι).app (Scheme.Modules.graphKernel Y.ι C B φ) ≪≫
        Scheme.Modules.graphKernelPullbackIso Y.ι C B φ) inferInstance

/-- Let `C` be a quasi-coherent submodule of `H` which is generated by finitely many sections near
every point of a quasi-compact open `V`, and which agrees with `H` on an open `U ≤ V`. Then for any
affine open `Y` there is a smaller such submodule which is moreover finitely generated near every
point of `V ⊔ Y`. -/
theorem exists_subobject_step {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (H : X.Modules) [H.IsQuasicoherent]
    (U V : X.Opens) (hUV : U ≤ V) (hVc : IsCompact (V : Set X))
    (Y : X.Opens) (hY : IsAffineOpen Y)
    (C : Subobject H) (hCqc : (C : X.Modules).IsQuasicoherent)
    (hCfg : ∀ x ∈ V, IsFinitelyGeneratedAt (C : X.Modules) x)
    (hCU : ∀ W : X.Opens, W ≤ U → IsIso (C.arrow.app W)) :
    ∃ C' : Subobject H, (C' : X.Modules).IsQuasicoherent ∧
      (∀ x ∈ V ⊔ Y, IsFinitelyGeneratedAt (C' : X.Modules) x) ∧
      (∀ W : X.Opens, W ≤ U → IsIso (C'.arrow.app W)) := by
  have hYaff : IsAffine Y.toScheme := hY
  have hYc : IsCompact (Y : Set X) := hY.isCompact
  have hQC : QuasiCompact Y.ι := quasiCompact_iff_isSpectralMap.mpr
    (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp (hYc.isRetrocompact Y.2))
  have hCqc' : (C : X.Modules).IsQuasicoherent := hCqc
  have hNY : ((Scheme.Modules.restrictFunctor Y.ι).obj (C : X.Modules)).IsQuasicoherent :=
    restrictFunctor_isQuasicoherent Y.ι (C : X.Modules)
  have hWc : IsCompact ((Y.ι ⁻¹ᵁ V : Y.toScheme.Opens) : Set Y.toScheme) :=
    isCompact_preimage_ι_of_quasiSeparatedSpace V Y hVc hYc
  have hft : ((Scheme.Modules.restrictFunctor (Y.ι ⁻¹ᵁ V).ι).obj
      ((Scheme.Modules.restrictFunctor Y.ι).obj (C : X.Modules))).IsFiniteType :=
    isFiniteType_of_forall_isFinitelyGeneratedAt _ fun z => isFinitelyGeneratedAt_of_iso
      ((Scheme.Modules.restrictFunctorComp (Y.ι ⁻¹ᵁ V).ι Y.ι).app (C : X.Modules))
      (isFinitelyGeneratedAt_restrict ((Y.ι ⁻¹ᵁ V).ι ≫ Y.ι) (C : X.Modules) z (hCfg _ z.2))
  obtain ⟨B, hBqc, hBft, hBiso⟩ := exists_finiteTypeSubobject_isIso_app_of_isAffine
    ((Scheme.Modules.restrictFunctor Y.ι).obj (C : X.Modules)) (Y.ι ⁻¹ᵁ V) hWc hft
  have hBqc' : (B : Y.toScheme.Modules).IsQuasicoherent := hBqc
  have hBft' : (B : Y.toScheme.Modules).IsFiniteType := hBft
  have hφapp : ∀ W' : Y.toScheme.Opens, Y.ι ''ᵁ W' ≤ V →
      IsIso ((B.arrow ≫ (Scheme.Modules.restrictFunctorIsoPullback Y.ι).hom.app
        (C : X.Modules)).app W') := by
    intro W' hW'
    have h1 : IsIso (B.arrow.app W') := hBiso W' (fun z hz => hW' ⟨z, hz, rfl⟩)
    have h2 : IsIso (((Scheme.Modules.restrictFunctorIsoPullback Y.ι).hom.app
        (C : X.Modules)).app W') := isIso_app_of_isIso _ W'
    rw [Scheme.Modules.Hom.comp_app]
    infer_instance
  have : Mono (B.arrow ≫ (Scheme.Modules.restrictFunctorIsoPullback Y.ι).hom.app
      (C : X.Modules)) :=
    mono_comp _ ((Scheme.Modules.restrictFunctorIsoPullback Y.ι).app (C : X.Modules)).hom
  obtain ⟨K, hKqc, p, hpmono, hpV, hKY⟩ :=
    exists_subobject_of_restrict (C : X.Modules) Y V (B : Y.toScheme.Modules)
      (B.arrow ≫ (Scheme.Modules.restrictFunctorIsoPullback Y.ι).hom.app (C : X.Modules)) hφapp
  have hcmono : Mono (p ≫ C.arrow) := mono_comp _ _
  have harrow : (Subobject.underlyingIso (p ≫ C.arrow)).hom ≫ (p ≫ C.arrow) =
      (Subobject.mk (p ≫ C.arrow)).arrow := Subobject.underlyingIso_hom_comp_eq_mk _
  refine ⟨Subobject.mk (p ≫ C.arrow), ?_, ?_, ?_⟩
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso (p ≫ C.arrow)).symm hKqc
  · intro x hx
    refine isFinitelyGeneratedAt_of_iso (Subobject.underlyingIso (p ≫ C.arrow)).symm ?_
    rcases (TopologicalSpace.Opens.mem_sup).mp hx with hxV | hxY
    · exact isFinitelyGeneratedAt_of_isIso_app p hpV hxV (hCfg x hxV)
    · exact isFinitelyGeneratedAt_of_restrict_isFiniteType K Y hKY hxY
  · intro W hW
    have h1 : IsIso ((Subobject.underlyingIso (p ≫ C.arrow)).hom.app W) :=
      isIso_app_of_isIso _ W
    have h2 : IsIso (p.app W) := hpV W (hW.trans hUV)
    have h3 : IsIso (C.arrow.app W) := hCU W hW
    rw [← harrow, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
    infer_instance

/-- Inserting an affine open into a `Finset` adds it to the supremum. -/
private theorem sup_insert_affineOpens {X : Scheme.{u}} [DecidableEq X.affineOpens]
    (U : X.Opens) (Y : X.affineOpens) (s : Finset X.affineOpens) :
    (U ⊔ (insert Y s).sup (fun Y => (Y : X.Opens)) : X.Opens) =
      (U ⊔ s.sup (fun Y => (Y : X.Opens))) ⊔ (Y : X.Opens) := by
  rw [Finset.sup_insert]
  ac_rfl

/-- The union of a quasi-compact open with finitely many affine opens is quasi-compact. -/
theorem isCompact_sup_finset_affineOpens {X : Scheme.{u}} (U : X.Opens)
    (hU : IsCompact (U : Set X)) (s : Finset X.affineOpens) :
    IsCompact ((U ⊔ s.sup (fun Y => (Y : X.Opens)) : X.Opens) : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hU
  | @insert Y s hYs ih =>
      rw [sup_insert_affineOpens, TopologicalSpace.Opens.coe_sup]
      exact ih.union (Y : X.affineOpens).2.isCompact

/-- For every `Finset` of affine opens, a quasi-coherent module `H` of finite type over a
quasi-compact open `U` has a quasi-coherent submodule which agrees with it on `U` and is finitely
generated near every point of `U` and of the members of the `Finset`. -/
private theorem exists_subobject_finset {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (H : X.Modules) [H.IsQuasicoherent] (U : X.Opens) (hUc : IsCompact (U : Set X))
    (hHU : ((Scheme.Modules.restrictFunctor U.ι).obj H).IsFiniteType)
    (s : Finset X.affineOpens) :
    ∃ C : Subobject H, (C : X.Modules).IsQuasicoherent ∧
      (∀ x ∈ U ⊔ s.sup (fun Y => (Y : X.Opens)), IsFinitelyGeneratedAt (C : X.Modules) x) ∧
      (∀ W : X.Opens, W ≤ U → IsIso (C.arrow.app W)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have harrow : (Subobject.underlyingIso (𝟙 H)).hom ≫ 𝟙 H =
          (Subobject.mk (𝟙 H)).arrow := Subobject.underlyingIso_hom_comp_eq_mk _
      refine ⟨Subobject.mk (𝟙 H), ?_, ?_, ?_⟩
      · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
          (Subobject.underlyingIso (𝟙 H)).symm inferInstance
      · intro x hx
        refine isFinitelyGeneratedAt_of_iso (Subobject.underlyingIso (𝟙 H)).symm ?_
        exact isFinitelyGeneratedAt_of_restrict_isFiniteType H U hHU (by simpa using hx)
      · intro W hW
        rw [← harrow, Scheme.Modules.Hom.comp_app]
        have h1 : IsIso ((Subobject.underlyingIso (𝟙 H)).hom.app W) := isIso_app_of_isIso _ W
        have h2 : IsIso ((𝟙 H : H ⟶ H).app W) := by
          rw [Scheme.Modules.Hom.id_app]; infer_instance
        infer_instance
  | @insert Y s hYs ih =>
      obtain ⟨C, hCqc, hCfg, hCU⟩ := ih
      obtain ⟨C', hC'qc, hC'fg, hC'U⟩ := exists_subobject_step H U
        (U ⊔ s.sup (fun Y => (Y : X.Opens))) le_sup_left
        (isCompact_sup_finset_affineOpens U hUc s) (Y : X.Opens) (Y : X.affineOpens).2
        C hCqc hCfg hCU
      refine ⟨C', hC'qc, fun x hx => hC'fg x ?_, hC'U⟩
      rwa [← sup_insert_affineOpens]

/-- On a quasi-compact, quasi-separated scheme, a quasi-coherent module whose restriction to a
quasi-compact open `U` is of finite type has a quasi-coherent submodule of finite type which agrees
with it on `U`. -/
@[ega "I 9.4.7" "special case"]
theorem exists_finiteTypeSubobject_isIso_app {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (H : X.Modules) [H.IsQuasicoherent] (U : X.Opens)
    (hUc : IsCompact (U : Set X))
    (hHU : ((Scheme.Modules.restrictFunctor U.ι).obj H).IsFiniteType) :
    ∃ C : Subobject H, (C : X.Modules).IsQuasicoherent ∧ (C : X.Modules).IsFiniteType ∧
      ∀ W : X.Opens, W ≤ U → IsIso (C.arrow.app W) := by
  obtain ⟨s, hs⟩ := exists_finset_affineOpens_sup_eq_top (⊥ : X.Opens)
  obtain ⟨C, hCqc, hCfg, hCU⟩ := exists_subobject_finset H U hUc hHU s
  refine ⟨C, hCqc, isFiniteType_of_forall_isFinitelyGeneratedAt _ fun x => hCfg x ?_, hCU⟩
  have hs' : s.sup (fun Y => (Y : X.Opens)) = ⊤ := by
    rw [Finset.sup_eq_iSup]
    simpa using hs
  rw [hs']
  simp

end Pointwise

end AlgebraicGeometry
