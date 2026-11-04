module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AssociatedPointsMono.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Embedded
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.EmbeddedCharacterization
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.CartierPart
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DivisorCover
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.Topology.Dimension.Codimension
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# Codimension-one closed subschemes without embedded points are effective Cartier divisors

Let `Z ⊆ X` be a closed subscheme of a Noetherian scheme such that `Z` has no embedded points,
every irreducible component of `Z` has codimension one in `X`, and the local rings `𝒪_{X,x}` for
`x ∈ Z` are unique factorization domains — or `X` is regular.  Then `Z` is an effective Cartier
divisor.

## Main results

* `AlgebraicGeometry.isEffectiveCartierDivisor_of_codimension_one`: **Stacks Tag 0BXH.**

## The argument

Codimension one makes the support of `Z` nowhere dense, so Tag 0AGB applies: there is an
effective Cartier divisor `D ⊆ Z` agreeing with `Z` outside a closed set of codimension at least
two.  The inclusion `D ⊆ Z` of closed subschemes is then an isomorphism, because the absence of
embedded points makes the comparison map of ideal sheaves injective on stalks at the associated
points of `Z` (`Stacks.AlgebraicGeometry.AssociatedPointsMono`), all of which are generic points
of components of `Z` and hence lie outside the codimension-two set.

## References

* [Stacks Project, Tag 0BXH](https://stacks.math.columbia.edu/tag/0BXH)
-/

@[expose] public section

open CategoryTheory Stacks.Divisors TopologicalSpace

universe u

namespace AlgebraicGeometry

@[ega "IV 21.10.5" "special case"]
private theorem support_nowhereDense_of_codimension_one
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (hcodim : ∀ Z ∈ irreducibleComponents I.subscheme,
      ∀ x : I.subscheme, IsGenericPoint x Z →
        codimension (IrreducibleCloseds.closureSingleton (I.subschemeι x)) = 1) :
    IsNowhereDense (I.support : Set X) := by
  change interior (closure (I.support : Set X)) = ∅
  rw [I.support.isClosed.closure_eq]
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hgen : Dense (genericPoints X) := dense_iff_closure_eq.mpr genericPoints.closure
  obtain ⟨η, hηV, hηgen⟩ := hgen.inter_open_nonempty _ isOpen_interior ⟨x, hx⟩
  obtain ⟨y, hyη⟩ : η ∈ Set.range I.subschemeι.base := by
    rw [I.range_subschemeι]
    exact interior_subset hηV
  let C : irreducibleComponents I.subscheme :=
    ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
  let ηY := genericPoints.ofComponent C
  have hηYC : IsGenericPoint (ηY : I.subscheme) (C : Set I.subscheme) :=
    genericPoints.isGenericPoint_ofComponent C
  let Cimg : Set X := I.subschemeι.base '' (C : Set I.subscheme)
  have hCimgClosed : IsClosed Cimg := I.subschemeι.isClosedEmbedding.isClosedMap _
    (isClosed_of_mem_irreducibleComponents (C : Set I.subscheme) C.property)
  have hCimgIrr : IsIrreducible Cimg :=
    C.property.1.image I.subschemeι.base I.subschemeι.continuous.continuousOn
  have hyC : y ∈ (C : Set I.subscheme) := mem_irreducibleComponent
  let Cx : irreducibleComponents X := genericPoints.component ⟨η, hηgen⟩
  have hηgenX : IsGenericPoint η (Cx : Set X) := genericPoints.isGenericPoint ⟨η, hηgen⟩
  have hCxsubsetCimg : (Cx : Set X) ⊆ Cimg :=
    hηgenX.mem_closed_set_iff hCimgClosed |>.mp ⟨y, hyC, hyη⟩
  have hCimgEq : Cimg = (Cx : Set X) :=
    Set.Subset.antisymm (Cx.property.2 hCimgIrr hCxsubsetCimg) hCxsubsetCimg
  have hηYimg : IsGenericPoint (I.subschemeι ηY) Cimg := by
    have h : IsGenericPoint (I.subschemeι ηY) (closure Cimg) := by
      simpa only [Cimg] using hηYC.image I.subschemeι.continuous
    rwa [hCimgClosed.closure_eq] at h
  have hηY_eq : I.subschemeι ηY = η := hηYimg.eq (by simpa [hCimgEq] using hηgenX)
  have hcodim0 : codimension (IrreducibleCloseds.closureSingleton η) = 0 := by
    rw [codimension_eq_coheight]
    have hEq : IrreducibleCloseds.closureSingleton η =
        (⟨(Cx : Set X), Cx.property.1, isClosed_of_mem_irreducibleComponents _ Cx.property⟩ :
          IrreducibleCloseds X) :=
      IrreducibleCloseds.ext hηgenX.def
    rw [hEq]
    exact Order.IsMax.coheight_eq_zero fun D hCD => Cx.property.2 D.isIrreducible' hCD
  have hcodim1 := hcodim C C.property ηY hηYC
  rw [hηY_eq, hcodim0] at hcodim1
  norm_num at hcodim1

private theorem associatedPoints_are_generic_of_noEmbeddedPoints
    {X : Scheme.{u}} [IsLocallyNoetherian X] (hno : HasNoEmbeddedPoints X)
    (x : X) (hx : x ∈ Stacks.Divisors.schemeAssociatedPoints X) :
    ∃ Z ∈ irreducibleComponents X, IsGenericPoint x Z := by
  by_contra h
  exact hno x <| (isEmbeddedPoint_iff_not_genericPoint X x).2 ⟨hx, h⟩

private theorem associatedPoints_subset_open_of_codimension_one
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (hno : HasNoEmbeddedPoints I.subscheme)
    (hcodim : ∀ Z ∈ irreducibleComponents I.subscheme,
      ∀ x : I.subscheme, IsGenericPoint x Z →
        codimension (IrreducibleCloseds.closureSingleton (I.subschemeι x)) = 1)
    (U : X.Opens)
    (hbad : ∀ x : X, x ∈ I.support → x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) :
    ∀ x ∈ Stacks.Divisors.schemeAssociatedPoints I.subscheme, I.subschemeι x ∈ U := by
  have : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  intro x hx
  obtain ⟨Z, hZ, hgeneric⟩ :=
    associatedPoints_are_generic_of_noEmbeddedPoints hno x hx
  have hcodimx := hcodim Z hZ x hgeneric
  have hxsupport : I.subschemeι x ∈ I.support := by
    change I.subschemeι.base x ∈ (I.support : Set X)
    rw [← I.range_subschemeι]
    exact Set.mem_range_self x
  by_contra hxU
  have hlarge := hbad (I.subschemeι x) hxsupport hxU
  rw [hcodimx] at hlarge
  norm_num at hlarge

private theorem subschemeMap_isIso_on_agreement_open
    {X : Scheme.{u}} [IsLocallyNoetherian X] (E I : X.IdealSheafData)
    (U : X.Opens) (hEq : E.comap U.ι = I.comap U.ι)
    (f : E.subscheme ⟶ I.subscheme)
    (hcomp : f ≫ I.subschemeι = E.subschemeι) :
    IsIso (f ∣_ (I.subschemeι ⁻¹ᵁ U)) := by
  let V : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ U
  let W : E.subscheme.Opens := E.subschemeι ⁻¹ᵁ U
  have hpre : f ⁻¹ᵁ V = W := by
    ext y
    change I.subschemeι (f y) ∈ U ↔ E.subschemeι y ∈ U
    rw [← Scheme.Hom.comp_apply f I.subschemeι y, hcomp]
  let e : (f ⁻¹ᵁ V).toScheme ≅ W.toScheme :=
    Scheme.isoOfEq E.subscheme hpre
  let iE : W.toScheme ⟶ U.toScheme := E.subschemeι ∣_ U
  let iI : V.toScheme ⟶ U.toScheme := I.subschemeι ∣_ U
  let g : W.toScheme ⟶ V.toScheme := e.inv ≫ (f ∣_ V)
  have he : e.inv ≫ (f ⁻¹ᵁ V).ι = W.ι := by
    simp [e]
  have hgi : g ≫ iI = iE := by
    change (e.inv ≫ (f ∣_ V)) ≫ (I.subschemeι ∣_ U) = E.subschemeι ∣_ U
    apply (cancel_mono U.ι).1
    calc
      ((e.inv ≫ (f ∣_ V)) ≫ (I.subschemeι ∣_ U)) ≫ U.ι =
          (e.inv ≫ (f ∣_ V)) ≫ ((I.subschemeι ∣_ U) ≫ U.ι) := by
            rw [Category.assoc]
      _ = (e.inv ≫ (f ∣_ V)) ≫ (V.ι ≫ I.subschemeι) := by
            rw [morphismRestrict_ι]
      _ = (e.inv ≫ ((f ∣_ V) ≫ V.ι)) ≫ I.subschemeι := by
            simp [Category.assoc]
      _ = (e.inv ≫ ((f ⁻¹ᵁ V).ι ≫ f)) ≫ I.subschemeι := by
            rw [morphismRestrict_ι]
      _ = (e.inv ≫ (f ⁻¹ᵁ V).ι) ≫ (f ≫ I.subschemeι) := by
            simp [Category.assoc]
      _ = W.ι ≫ E.subschemeι := by rw [he, hcomp]
      _ = (E.subschemeι ∣_ U) ≫ U.ι := by rw [morphismRestrict_ι]
  have hker : iE.ker = iI.ker := by
    change (E.subschemeι ∣_ U).ker = (I.subschemeι ∣_ U).ker
    rw [ker_morphismRestrict_eq_comap,
      ker_morphismRestrict_eq_comap,
      E.ker_subschemeι, I.ker_subschemeι, hEq]
  have _ : IsIso g := IsClosedImmersion.isIso_of_ker_eq iE iI g hgi hker
  exact IsIso.of_isIso_comp_left (e.inv) (f ∣_ V)

private theorem stalkFunctor_map_injective_of_app_injective_on_open
    {X : Type u} [TopologicalSpace X]
    {F G : TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of X)} {α : F ⟶ G}
    (U : Opens X) (x : X) (hx : x ∈ U)
    (hα : ∀ W : Opens X, W ≤ U →
      Function.Injective (ConcreteCategory.hom (α.app (Opposite.op W)))) :
    Function.Injective
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α)) := by
  intro s t hst
  obtain ⟨U₁, hxU₁, s₁, rfl⟩ := F.exists_germ_eq s
  obtain ⟨U₂, hxU₂, s₂, rfl⟩ := F.exists_germ_eq t
  change (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α))
      ((ConcreteCategory.hom (F.germ U₁ x hxU₁)) s₁) =
    (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α))
      ((ConcreteCategory.hom (F.germ U₂ x hxU₂)) s₂) at hst
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
  obtain ⟨W, hxW, hWU₁, hWU₂, heq⟩ := G.germ_eq x hxU₁ hxU₂
    ((ConcreteCategory.hom (α.app (Opposite.op U₁))) s₁)
    ((ConcreteCategory.hom (α.app (Opposite.op U₂))) s₂) hst
  let W' : Opens X := W ⊓ U
  have hxW' : x ∈ W' := ⟨hxW, hx⟩
  have hW'U₁ : W' ≤ U₁ := inf_le_left.trans hWU₁.le
  have hW'U₂ : W' ≤ U₂ := inf_le_left.trans hWU₂.le
  have hn (U' : Opens X) (h : W' ≤ U') (s : F.obj (Opposite.op U')) :
      (ConcreteCategory.hom (G.map (homOfLE h).op))
          ((ConcreteCategory.hom (α.app (Opposite.op U'))) s) =
        (ConcreteCategory.hom (α.app (Opposite.op W')))
          ((ConcreteCategory.hom (F.map (homOfLE h).op)) s) := by
    simpa only [ConcreteCategory.comp_apply] using
      (congrArg (fun k => (ConcreteCategory.hom k) s) (α.naturality (homOfLE h).op)).symm
  have heq' : (ConcreteCategory.hom (α.app (Opposite.op W')))
        ((ConcreteCategory.hom (F.map (homOfLE hW'U₁).op)) s₁) =
      (ConcreteCategory.hom (α.app (Opposite.op W')))
        ((ConcreteCategory.hom (F.map (homOfLE hW'U₂).op)) s₂) := by
    rw [← hn _ hW'U₁, ← hn _ hW'U₂]
    have hcomp (U' : Opens X) (h : W' ≤ U') (h' : W ⟶ U') :
        G.map (homOfLE h).op = G.map h'.op ≫ G.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op :=
      G.map_comp h'.op _
    rw [hcomp _ hW'U₁ hWU₁, hcomp _ hW'U₂ hWU₂]
    exact congrArg (ConcreteCategory.hom (G.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op)) heq
  exact (F.germ_res_apply (homOfLE hW'U₁) x hxW' s₁).symm.trans <|
    (congrArg (ConcreteCategory.hom (F.germ W' x hxW')) (hα W' inf_le_right heq')).trans
      (F.germ_res_apply (homOfLE hW'U₂) x hxW' s₂)

/-- If the restriction of `f` to an open `V` is an isomorphism, then `f.app W` is an
isomorphism for every open `W ≤ V`. -/
private theorem isIso_app_of_le_of_isIso_morphismRestrict {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    {V : Z.Opens} [IsIso (f ∣_ V)] {W : Z.Opens} (hWV : W ≤ V) : IsIso (f.app W) := by
  have hImage : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, hWV hy⟩, hy, rfl⟩
  have : IsIso (f.app (V.ι ''ᵁ (V.ι ⁻¹ᵁ W)) ≫
      Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f V (V.ι ⁻¹ᵁ W))).op) := by
    have : IsIso ((f ∣_ V).app (V.ι ⁻¹ᵁ W)) := inferInstance
    rw [← morphismRestrict_app f V (V.ι ⁻¹ᵁ W)]
    exact this
  have hAppImage : IsIso (f.app (V.ι ''ᵁ (V.ι ⁻¹ᵁ W))) :=
    IsIso.of_isIso_comp_right (f.app (V.ι ''ᵁ (V.ι ⁻¹ᵁ W)))
      (Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f V (V.ι ⁻¹ᵁ W))).op)
  exact hImage ▸ hAppImage

private theorem toPresheaf_map_unitToPushforwardObjUnit_app_apply {Y Z : Scheme.{u}}
    (f : Y ⟶ Z) (W : Z.Opens) (r) :
    ConcreteCategory.hom (((PresheafOfModules.toPresheaf Z.ringCatSheaf.obj).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val).app
          (Opposite.op W)) r =
      ConcreteCategory.hom (f.toRingCatSheafHom.hom.app (Opposite.op W)) r :=
  (PresheafOfModules.toPresheaf_map_app_apply _ (Opposite.op W) r).trans
    (SheafOfModules.unitToPushforwardObjUnit_val_app_apply f.toRingCatSheafHom
      (X := Opposite.op W) r)

private theorem mono_unitToPushforwardObjUnit_of_isIso_morphismRestrict
    {Y Z : Scheme.{u}} [IsLocallyNoetherian Z] (f : Y ⟶ Z) [QuasiCompact f] [QuasiSeparated f]
    (V : Z.Opens) [IsIso (f ∣_ V)] (hV : ∀ x ∈ schemeAssociatedPoints Z, x ∈ V) :
    Mono (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :
      SheafOfModules.unit Z.ringCatSheaf ⟶
        (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)) := by
  have _ : ((SheafOfModules.pushforward f.toRingCatSheafHom).obj
      (SheafOfModules.unit Y.ringCatSheaf)).IsQuasicoherent :=
    pushforward_isQuasicoherent f (SheafOfModules.unit Y.ringCatSheaf)
  apply Stacks.AlgebraicGeometry.AssociatedPointsMono.mono_of_stalk_injective_on_associatedPoints
  intro x
  by_cases hx : x ∈ schemeAssociatedPoints Z
  · left
    refine stalkFunctor_map_injective_of_app_injective_on_open (α :=
      (PresheafOfModules.toPresheaf Z.ringCatSheaf.obj).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val)
      V x (hV x hx) fun W hWV r s hrs => ?_
    have := isIso_app_of_le_of_isIso_morphismRestrict f hWV
    rw [toPresheaf_map_unitToPushforwardObjUnit_app_apply,
      toPresheaf_map_unitToPushforwardObjUnit_app_apply] at hrs
    exact ((ConcreteCategory.isIso_iff_bijective (f.app W)).1 this).1 hrs
  · exact Or.inr hx

private theorem eq_of_le_of_comap_eq_of_associatedPoints_mem
    {X : Scheme.{u}} [IsLocallyNoetherian X] {E I : X.IdealSheafData} (hIE : I ≤ E)
    (U : X.Opens) (hEq : E.comap U.ι = I.comap U.ι)
    (hU : ∀ x ∈ schemeAssociatedPoints I.subscheme, I.subschemeι x ∈ U) : E = I := by
  let f : E.subscheme ⟶ I.subscheme := Scheme.IdealSheafData.inclusion hIE
  have hcomp : f ≫ I.subschemeι = E.subschemeι := by
    simp [f]
  have : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  have _ := subschemeMap_isIso_on_agreement_open E I U hEq f hcomp
  let m : SheafOfModules.unit I.subscheme.ringCatSheaf ⟶
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit E.subscheme.ringCatSheaf) :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have hmono : Mono m :=
    mono_unitToPushforwardObjUnit_of_isIso_morphismRestrict f (I.subschemeι ⁻¹ᵁ U) hU
  let α := (PresheafOfModules.toPresheaf I.subscheme.ringCatSheaf.obj).map m.val
  have hmonoα : Mono α := by
    change Mono ((Scheme.Modules.toPresheaf I.subscheme).map m)
    exact @Functor.PreservesMonomorphisms.preserves _ _ _ _
      (Scheme.Modules.toPresheaf I.subscheme) inferInstance _ _ m hmono
  have hfapp (W : I.subscheme.Opens) : Function.Injective (f.app W) := by
    intro r s hrs
    have hmonoApp : Mono (α.app (Opposite.op W)) :=
      (NatTrans.mono_iff_mono_app α).mp hmonoα (Opposite.op W)
    exact (AddCommGrpCat.mono_iff_injective _).1 hmonoApp
      ((toPresheaf_map_unitToPushforwardObjUnit_app_apply f W r).trans
        (hrs.trans (toPresheaf_map_unitToPushforwardObjUnit_app_apply f W s).symm))
  have hker : f.ker = ⊥ := by
    apply Scheme.IdealSheafData.ext_of_iSup_eq_top
      (fun W : I.subscheme.affineOpens => W) (iSup_affineOpens_eq_top I.subscheme)
    intro W
    rw [Scheme.Hom.ker_apply]
    simpa [Scheme.IdealSheafData.ideal_bot] using
      (RingHom.injective_iff_ker_eq_bot (f.app W.1).hom).1 (hfapp W.1)
  have _ : IsIso f := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  have hkerEq : E.subschemeι.ker = I.subschemeι.ker := by
    rw [← hcomp, Scheme.Hom.ker_comp_of_isIso f]
  simpa only [E.ker_subschemeι, I.ker_subschemeι] using hkerEq

/-- A codimension-one closed subscheme with no embedded points is an effective Cartier
divisor when the ambient local rings along it are UFDs, or the ambient scheme is regular. -/
@[stacks 0BXH, ega "IV 21.6.9" "(ii) c) ⇒ b)"]
theorem isEffectiveCartierDivisor_of_codimension_one
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (hno : HasNoEmbeddedPoints I.subscheme)
    (hcodim : ∀ Z ∈ irreducibleComponents I.subscheme,
      ∀ x : I.subscheme, IsGenericPoint x Z →
        codimension (IrreducibleCloseds.closureSingleton (I.subschemeι x)) = 1)
    (hlocal : (∀ x : X, x ∈ I.support →
      UniqueFactorizationMonoid (X.presheaf.stalk x)) ∨ IsRegular X) :
    IsEffectiveCartierDivisor I := by
  classical
  obtain ⟨D, Z', hD, hZ', hcover⟩ := exists_integral_effectiveCartierDivisors_cover
    X I (support_nowhereDense_of_codimension_one I hcodim) hlocal
  let Dfun : {J : X.IdealSheafData // J ∈ D} → X.IdealSheafData := fun j => j.1
  have hDfun (j) : IsIntegral (Dfun j).subscheme ∧ IsEffectiveCartierDivisor (Dfun j) :=
    hD j.1 j.2
  have hcover' : (I.support : Set X) ⊆ (Z' : Set X) ∪ ⋃ j, ((Dfun j).support : Set X) := by
    intro x hx
    rcases hcover hx with hxZ' | hxD
    · exact Or.inl hxZ'
    · obtain ⟨J, hxJ⟩ := Set.mem_iUnion.mp hxD
      obtain ⟨hJD, hxD⟩ := Set.mem_iUnion.mp hxJ
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨J, hJD⟩, hxD⟩)
  obtain ⟨a, hpart⟩ :=
    exists_effectiveCartierDivisor_agree_off_codimension_two X I Dfun Z' hDfun hZ' hcover'
  dsimp at hpart
  rcases hpart with ⟨hE, hIE, U, hEq, hbad⟩
  have hEI := eq_of_le_of_comap_eq_of_associatedPoints_mem hIE U hEq
    (associatedPoints_subset_open_of_codimension_one I hno hcodim U hbad)
  exact hEI ▸ hE

end AlgebraicGeometry

end
