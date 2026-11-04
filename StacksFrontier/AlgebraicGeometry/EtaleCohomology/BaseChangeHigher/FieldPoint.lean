module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.Basic

/-!
# Reducing a property of schemes to a field-valued point

Let `T` be a nonempty quasi-compact quasi-separated scheme and let `P` be a property of
quasi-compact quasi-separated schemes over `T`. If `P` is invariant under thickenings, passes to
inverse limits along affine transition morphisms, and passes from a scheme to either a closed
subscheme or the quasi-compact open complement of that subscheme, then `P` holds at a
field-valued point of `T`.

This is the formal dévissage behind the base-change theorems for higher direct images: it
reduces a statement about an arbitrary such scheme to the case of the spectrum of a field.

## Main results

* `AlgebraicGeometry.exists_field_point` produces the field-valued point at which `P` holds.

## Implementation notes

The property is indexed by both a scheme and its structure morphism to the base, so that the
hypotheses can be applied to subschemes and to limits while keeping track of the map to `T`. In
the inverse-limit hypothesis a chosen limiting cone and a compatible family of structure maps
are supplied, rather than a canonical limit, so the hypothesis can be discharged for whichever
cone the construction produces. A closed subscheme is presented by its ideal sheaf and the open
complement by the complement of that sheaf's support.

The proof takes a maximal element of the family of ideal sheaves whose closed subscheme is
nonempty and satisfies `P` — maximality coming from the inverse-limit hypothesis applied to a
chain — and shows that the corresponding subscheme has a single point with a field as residue
ring, since otherwise the closed/open hypothesis would produce a strictly larger member.

## References

* [Stacks Project, Tag 0F06](https://stacks.math.columbia.edu/tag/0F06)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry

private instance compactSpace_subscheme {X : Scheme.{u}} [CompactSpace X]
    (I : X.IdealSheafData) : CompactSpace I.subscheme :=
  I.subschemeι.isClosedEmbedding.compactSpace

private instance quasiSeparatedSpace_subscheme {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) : QuasiSeparatedSpace I.subscheme :=
  quasiSeparatedSpace_of_quasiSeparated I.subschemeι

/-- A point of the subscheme of `I` maps into the support of `I`. -/
private theorem subschemeι_mem_support {X : Scheme.{u}} (I : X.IdealSheafData)
    (y : I.subscheme) : I.subschemeι y ∈ (I.support : Set X) :=
  I.range_subschemeι ▸ Set.mem_range_self y

/-- The subscheme of `I` is nonempty as soon as the support of `I` is. -/
private theorem nonempty_subscheme_of_support_nonempty {X : Scheme.{u}} (I : X.IdealSheafData)
    (h : (I.support : Set X).Nonempty) : Nonempty I.subscheme := by
  obtain ⟨x, hx⟩ := h
  rw [← I.range_subschemeι] at hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y⟩

private noncomputable def chainSubschemeDiagram {X : Scheme.{u}} (S : Set X.IdealSheafData)
    (_hS : IsChain (· ≤ ·) S) :
    @CategoryTheory.Functor ({I // I ∈ S}ᵒᵖ) (inferInstance) Scheme Scheme.instCategory :=
  { obj i := i.unop.1.subscheme
    map f := Scheme.IdealSheafData.inclusion f.unop.le
    map_id := by intro i; simp
    map_comp := by
      intro i j k f g
      exact (Scheme.IdealSheafData.inclusion_comp g.unop.le f.unop.le).symm }

private noncomputable def chainSupCone {X : Scheme.{u}} (S : Set X.IdealSheafData)
    (hS : IsChain (· ≤ ·) S) :
    @Cone _ _ Scheme Scheme.instCategory (chainSubschemeDiagram S hS) where
  pt := (sSup S).subscheme
  π := {
    app i := Scheme.IdealSheafData.inclusion (le_sSup i.unop.2)
    naturality := by
      intro i j f
      change Scheme.IdealSheafData.inclusion (le_sSup j.unop.2) =
        Scheme.IdealSheafData.inclusion (le_sSup i.unop.2) ≫
          Scheme.IdealSheafData.inclusion f.unop.le
      rw [Scheme.IdealSheafData.inclusion_comp] }

private theorem chainCone_ambient_eq {X : Scheme.{u}} (S : Set X.IdealSheafData)
    (hS : IsChain (· ≤ ·) S)
    (s : @Cone _ _ Scheme Scheme.instCategory (chainSubschemeDiagram S hS))
    (i₀ i : {I // I ∈ S}) :
    s.π.app (Opposite.op i) ≫ i.1.subschemeι =
      s.π.app (Opposite.op i₀) ≫ i₀.1.subschemeι := by
  rcases hS.total i.property i₀.property with h | h
  · let a : Opposite.op i₀ ⟶ Opposite.op i := Quiver.Hom.op (homOfLE h)
    have hw := congrArg (fun f => f ≫ i.1.subschemeι) (s.w a)
    simpa [chainSubschemeDiagram, Scheme.IdealSheafData.inclusion_subschemeι,
      Category.assoc, a] using hw.symm
  · let a : Opposite.op i ⟶ Opposite.op i₀ := Quiver.Hom.op (homOfLE h)
    have hw := congrArg (fun f => f ≫ i₀.1.subschemeι) (s.w a)
    simpa [chainSubschemeDiagram, Scheme.IdealSheafData.inclusion_subschemeι,
      Category.assoc, a] using hw

private noncomputable def chainSupLift {X : Scheme.{u}} (S : Set X.IdealSheafData)
    (hS : IsChain (· ≤ ·) S) (hne : S.Nonempty)
    (s : @Cone _ _ Scheme Scheme.instCategory (chainSubschemeDiagram S hS)) :
    @Quiver.Hom Scheme Scheme.instCategory.toQuiver s.pt (sSup S).subscheme := by
  classical
  let i₀ : {I // I ∈ S} := ⟨hne.choose, hne.choose_spec⟩
  let g : s.pt ⟶ X := s.π.app (Opposite.op i₀) ≫ i₀.1.subschemeι
  have hbound : sSup S ≤ g.ker := by
    apply sSup_le
    intro I hI
    have hIker : I ≤ (s.π.app (Opposite.op ⟨I, hI⟩) ≫ I.subschemeι).ker := by
      have hk := Scheme.Hom.le_ker_comp
        (s.π.app (Opposite.op ⟨I, hI⟩)) I.subschemeι
      calc
        I = I.subschemeι.ker := (Scheme.IdealSheafData.ker_subschemeι I).symm
        _ ≤ (s.π.app (Opposite.op ⟨I, hI⟩) ≫ I.subschemeι).ker := hk
    rw [chainCone_ambient_eq S hS s i₀ ⟨I, hI⟩] at hIker
    exact hIker
  apply IsClosedImmersion.lift (sSup S).subschemeι g
  simpa only [Scheme.IdealSheafData.ker_subschemeι] using hbound

private noncomputable def chainSupCone_isLimit {X : Scheme.{u}} (S : Set X.IdealSheafData)
    (hS : IsChain (· ≤ ·) S) (hne : S.Nonempty) :
    IsLimit (chainSupCone S hS) := by
  classical
  let D := chainSubschemeDiagram S hS
  let c := chainSupCone S hS
  refine {
    lift := fun s => by simpa only [chainSupCone] using chainSupLift S hS hne s
    fac := fun s i => ?_
    uniq := fun s m hm => ?_ }
  · change (chainSupLift S hS hne s ≫
      Scheme.IdealSheafData.inclusion (le_sSup i.unop.2)) = s.π.app i
    apply (cancel_mono i.unop.1.subschemeι).1
    let i₀ : {I // I ∈ S} := ⟨hne.choose, hne.choose_spec⟩
    calc
      (chainSupLift S hS hne s ≫ Scheme.IdealSheafData.inclusion (le_sSup i.unop.2)) ≫
          i.unop.1.subschemeι = chainSupLift S hS hne s ≫ (sSup S).subschemeι := by
            rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
      _ = s.π.app (Opposite.op i₀) ≫ i₀.1.subschemeι :=
            IsClosedImmersion.lift_fac _ _ _
      _ = s.π.app i ≫ i.unop.1.subschemeι := by
            exact (chainCone_ambient_eq S hS s i₀ i.unop).symm
  · dsimp only [chainSupCone] at m hm ⊢
    apply (cancel_mono ((sSup S).subschemeι)).1
    let i₀ : {I // I ∈ S} := ⟨hne.choose, hne.choose_spec⟩
    have hinc : Scheme.IdealSheafData.inclusion (le_sSup i₀.property) ≫
        i₀.1.subschemeι = (sSup S).subschemeι :=
      Scheme.IdealSheafData.inclusion_subschemeι _
    calc
      m ≫ (sSup S).subschemeι =
          m ≫ (Scheme.IdealSheafData.inclusion (le_sSup i₀.property) ≫ i₀.1.subschemeι) := by
            rw [hinc]
      _ = (m ≫ Scheme.IdealSheafData.inclusion (le_sSup i₀.property)) ≫ i₀.1.subschemeι := by
            rw [Category.assoc]
      _ = s.π.app (Opposite.op i₀) ≫ i₀.1.subschemeι := by
            exact congrArg (fun f => f ≫ i₀.1.subschemeι) (hm (Opposite.op i₀))
      _ = chainSupLift S hS hne s ≫ (sSup S).subschemeι :=
            (IsClosedImmersion.lift_fac _ _ _).symm

private theorem chainSup_property {B X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (P : ∀ Y : Scheme.{u}, (Y ⟶ B) → Prop)
    (hLimit : ∀ {I : Type u} [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ Scheme.{u})
      [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)]
      [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
      (c : Cone D) (_ : IsLimit c)
      [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
      (f : c.pt ⟶ B) (fi : ∀ i, D.obj i ⟶ B),
      (∀ {i j : I} (a : i ⟶ j), D.map a ≫ fi j = fi i) →
      (∀ i, c.π.app i ≫ fi i = f) →
      (∀ i, P (D.obj i) (fi i)) → P c.pt f)
    (f : X ⟶ B) (S : Set X.IdealSheafData) (hS : IsChain (· ≤ ·) S)
    (hne : S.Nonempty)
    (hmem : ∀ I ∈ S, P I.subscheme (I.subschemeι ≫ f)) :
    P (sSup S).subscheme ((sSup S).subschemeι ≫ f) := by
  let D := chainSubschemeDiagram S hS
  let c := chainSupCone S hS
  let : IsCofiltered ({I // I ∈ S}ᵒᵖ) := {
    nonempty := ⟨Opposite.op ⟨hne.choose, hne.choose_spec⟩⟩
    cone_objs := fun i j => by
      rcases hS.total i.unop.2 j.unop.2 with h | h
      · exact ⟨Opposite.op j.unop, Quiver.Hom.op (homOfLE h), 𝟙 _, trivial⟩
      · exact ⟨Opposite.op i.unop, 𝟙 _, Quiver.Hom.op (homOfLE h), trivial⟩
    cone_maps := by
      intro i j f g
      exact ⟨_, 𝟙 _, Subsingleton.elim _ _⟩ }
  let : ∀ {i j : ({I // I ∈ S}ᵒᵖ)} (a : i ⟶ j), IsAffineHom (D.map a) := by
    intro i j a
    dsimp [D, chainSubschemeDiagram]
    infer_instance
  let : ∀ i, CompactSpace (D.obj i) := fun i => compactSpace_subscheme i.unop.1
  let : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i => quasiSeparatedSpace_subscheme i.unop.1
  let : CompactSpace c.pt := inferInstanceAs (CompactSpace (sSup S).subscheme)
  let : QuasiSeparatedSpace c.pt := inferInstanceAs (QuasiSeparatedSpace (sSup S).subscheme)
  apply hLimit D c (chainSupCone_isLimit S hS hne)
    ((sSup S).subschemeι ≫ f) (fun i => i.unop.1.subschemeι ≫ f)
  · intro i j a
    dsimp [D, chainSubschemeDiagram]
    simp
  · intro i
    show Scheme.IdealSheafData.inclusion (le_sSup i.unop.2) ≫
      (i.unop.1.subschemeι ≫ f) = (sSup S).subschemeι ≫ f
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  · intro i
    exact hmem i.unop.1 i.unop.2

private theorem mapped_subscheme_iso_fac {T : Scheme.{u}} (I : T.IdealSheafData)
    (J : I.subscheme.IdealSheafData) :
    ∃ e : (J.map I.subschemeι).subscheme ≅ J.subscheme,
      e.hom ≫ J.subschemeι ≫ I.subschemeι = (J.map I.subschemeι).subschemeι := by
  let f : I.subscheme ⟶ T := I.subschemeι
  let g : J.subscheme ⟶ T := J.subschemeι ≫ f
  let K : T.IdealSheafData := J.map f
  have hKdef : K = g.ker := rfl
  have hker : K.subschemeι.ker = g.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι K, hKdef]
  let φ : K.subscheme ⟶ J.subscheme := IsClosedImmersion.lift g K.subschemeι hker.ge
  have hfac : φ ≫ g = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have : IsIso φ := IsClosedImmersion.isIso_of_ker_eq K.subschemeι g φ hfac hker
  refine ⟨asIso φ, ?_⟩
  simpa [f, g] using hfac

private theorem iso_is_thickening {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] [IsIso f] : IsThickening f := by
  refine ⟨inferInstance, ?_⟩
  intro y
  refine ⟨(asIso f).inv y, ?_⟩
  show ((asIso f).inv ≫ (asIso f).hom) y = y
  exact congrArg (fun q : Y ⟶ Y => q y) (Iso.inv_hom_id (asIso f))

private theorem closedSubscheme_not_property_of_maximal
    {T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (P : ∀ Y : Scheme.{u}, (Y ⟶ T) → Prop)
    (hThickening : ∀ {X X' : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace X'] [QuasiSeparatedSpace X'] (i : X ⟶ X') (f : X' ⟶ T),
      IsThickening i → (P X (i ≫ f) ↔ P X' f))
    (S : Set T.IdealSheafData) (I : T.IdealSheafData) (_hI : I ∈ S)
    (hmax : ∀ {J : T.IdealSheafData}, J ∈ S → I ≤ J → J ≤ I)
    (hS : ∀ J : T.IdealSheafData, P J.subscheme (J.subschemeι ≫ 𝟙 T) →
      Nonempty J.subscheme → J ∈ S)
    (J : I.subscheme.IdealSheafData) [CompactSpace J.subscheme]
    [QuasiSeparatedSpace J.subscheme] (η : I.subscheme)
    (hη : η ∉ (J.support : Set I.subscheme))
    (hJne : Nonempty J.subscheme)
    (hJP : P J.subscheme (J.subschemeι ≫ I.subschemeι)) : False := by
  let f : I.subscheme ⟶ T := I.subschemeι
  let K : T.IdealSheafData := J.map f
  obtain ⟨e, hfac⟩ := mapped_subscheme_iso_fac I J
  have hφthick : IsThickening e.hom := iso_is_thickening e.hom
  have hKP : P K.subscheme (K.subschemeι ≫ 𝟙 T) := by
    have h := (hThickening e.hom (J.subschemeι ≫ I.subschemeι) hφthick).mpr hJP
    simpa only [hfac, Category.comp_id] using h
  have hKne : Nonempty K.subscheme := Nonempty.map e.inv hJne
  have hKmem : K ∈ S := hS K hKP hKne
  have hIK : I ≤ K := by
    show I ≤ J.map f
    calc
      I = (⊥ : I.subscheme.IdealSheafData).map f := by
        rw [Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]
      _ ≤ J.map f := Scheme.IdealSheafData.map_mono f bot_le
  have hEq : I = K := le_antisymm hIK (hmax hKmem hIK)
  have hxK : f η ∈ (K.support : Set T) := hEq ▸ subschemeι_mem_support I η
  have hclosed : IsClosed (f '' (J.support : Set I.subscheme)) :=
    f.isClosedEmbedding.isClosed_iff_image_isClosed.mp J.support.isClosed
  have hxclosure : f η ∈ closure (f '' (J.support : Set I.subscheme)) := by
    rwa [Scheme.IdealSheafData.support_map] at hxK
  have hximage : f η ∈ f '' (J.support : Set I.subscheme) :=
    (closure_minimal subset_rfl hclosed) hxclosure
  obtain ⟨z, hzJ, hzf⟩ := hximage
  have hzeq : z = η := f.isClosedEmbedding.injective hzf
  exact hη (hzeq ▸ hzJ)

private theorem compactOpen_neighborhood_has_property
    {T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (P : ∀ Y : Scheme.{u}, (Y ⟶ T) → Prop)
    (hThickening : ∀ {X X' : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace X'] [QuasiSeparatedSpace X'] (i : X ⟶ X') (f : X' ⟶ T),
      IsThickening i → (P X (i ≫ f) ↔ P X' f))
    (hClosedOrOpen : ∀ {X : Scheme.{u}} [CompactSpace X]
      [QuasiSeparatedSpace X] (f : X ⟶ T) (J : X.IdealSheafData)
      [CompactSpace J.subscheme] [QuasiSeparatedSpace J.subscheme]
      (V : X.Opens) (_hV : (V : Set X) = (J.support : Set X)ᶜ)
      [CompactSpace V.toScheme] [QuasiSeparatedSpace V.toScheme],
      P X f → (P V.toScheme (V.ι ≫ f) ∨
        P J.subscheme (J.subschemeι ≫ f)))
    (S : Set T.IdealSheafData) (I : T.IdealSheafData) (hI : I ∈ S)
    (hmax : ∀ {J : T.IdealSheafData}, J ∈ S → I ≤ J → J ≤ I)
    (hS : ∀ J : T.IdealSheafData, P J.subscheme (J.subschemeι ≫ 𝟙 T) →
      Nonempty J.subscheme → J ∈ S)
    (η : I.subscheme) (hP : P I.subscheme (I.subschemeι ≫ 𝟙 T))
    {U : I.subscheme.Opens} (hUcompact : IsCompact (U : Set I.subscheme))
    (hUη : η ∈ U) : P U.toScheme (U.ι ≫ I.subschemeι) := by
  classical
  let X := I.subscheme
  let f : X ⟶ T := I.subschemeι
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hUcompact
  let : QuasiSeparatedSpace U.toScheme := quasiSeparatedSpace_of_quasiSeparated U.ι
  by_cases hUtop : U = ⊤
  · subst U
    have htop : Scheme.Opens.ι (⊤ : X.Opens) = (Scheme.topIso X).hom := rfl
    let : IsIso (Scheme.Opens.ι (⊤ : X.Opens)) := htop ▸ (Scheme.topIso X).isIso_hom
    exact (hThickening (Scheme.Opens.ι (⊤ : X.Opens)) f (iso_is_thickening _)).mpr hP
  · let J : X.IdealSheafData :=
      Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
    let V : X.Opens := U
    have hV : (V : Set X) = (J.support : Set X)ᶜ := by
      simp [V, J]
    rcases hClosedOrOpen f J V hV hP with hU | hJ
    · exact hU
    · have hηJ : η ∉ (J.support : Set X) := by
        intro h
        have hnot : η ∉ V := by
          have : η ∈ (V : Set X)ᶜ := by simpa [hV] using h
          simpa using this
        exact hnot (by simpa [V] using hUη)
      have hJne : Nonempty J.subscheme := by
        refine nonempty_subscheme_of_support_nonempty J ?_
        have hcompne : ((U : Set X)ᶜ).Nonempty :=
          Set.nonempty_compl.mpr fun h => hUtop (SetLike.coe_injective h)
        rwa [hV, compl_compl] at hcompne
      exact False.elim (closedSubscheme_not_property_of_maximal P hThickening
        S I hI hmax hS J η hηJ hJne hJ)

private abbrev affinePointNhdsProp {X : Scheme.{u}} (x : X) :
    ObjectProperty (OpenNhds x) := fun U => IsAffineOpen U.1

private abbrev affinePointNhds {X : Scheme.{u}} (x : X) :=
  (affinePointNhdsProp x).FullSubcategory

private noncomputable def affinePointNhdsInclusion {X : Scheme.{u}} (x : X) :
    (affinePointNhds x)ᵒᵖ ⥤ (OpenNhds x)ᵒᵖ where
  obj i := Opposite.op i.unop.obj
  map f := Quiver.Hom.op f.unop.hom
  map_id := by intro i; apply Subsingleton.elim
  map_comp := by intro i j k f g; apply Subsingleton.elim

private theorem affinePointNhds_isCofiltered {X : Scheme.{u}} (x : X) :
    IsCofiltered (affinePointNhds x) := by
  classical
  refine {
    cone_objs := ?_
    cone_maps := ?_
    nonempty := ?_ }
  · intro i j
    obtain ⟨W, hW, hxW, hWsub⟩ := exists_isAffineOpen_mem_and_subset
      (X := X)
      (U := (i.obj.1 : X.Opens) ⊓ (j.obj.1 : X.Opens))
      ⟨i.obj.2, j.obj.2⟩
    let k : affinePointNhds x := ⟨⟨W, hxW⟩, hW⟩
    have hki : k.obj.1 ≤ i.obj.1 := SetLike.coe_subset_coe.mp (hWsub.trans inf_le_left)
    have hkj : k.obj.1 ≤ j.obj.1 := SetLike.coe_subset_coe.mp (hWsub.trans inf_le_right)
    exact ⟨k, ObjectProperty.homMk (homOfLE hki),
      ObjectProperty.homMk (homOfLE hkj), trivial⟩
  · intro i j f g
    exact ⟨i, 𝟙 _, rfl⟩
  · obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := X) (U := ⊤) (by simp)
    exact ⟨⟨⟨U, hxU⟩, hU⟩⟩

private theorem affinePointNhdsInclusion_final {X : Scheme.{u}} (x : X) :
    Functor.Final (affinePointNhdsInclusion x) := by
  classical
  let : IsCofiltered (affinePointNhds x) := affinePointNhds_isCofiltered x
  refine ⟨?_⟩
  intro V
  have : Nonempty (StructuredArrow V (affinePointNhdsInclusion x)) := by
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset
      (X := X)
      (U := V.unop.1) V.unop.2
    let i : affinePointNhds x := ⟨⟨W, hxW⟩, hW⟩
    have hle : i.obj ≤ V.unop := by
      show (W : X.Opens) ≤ V.unop.1
      exact SetLike.coe_subset_coe.mp hWV
    let a : V ⟶ (affinePointNhdsInclusion x).obj (Opposite.op i) :=
      Quiver.Hom.op (homOfLE hle)
    exact ⟨StructuredArrow.mk a⟩
  apply zigzag_isConnected
  intro A B
  obtain ⟨k, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs A.right.unop B.right.unop
  let a' : A.right ⟶ Opposite.op k := Quiver.Hom.op a
  let b' : B.right ⟶ Opposite.op k := Quiver.Hom.op b
  let C : StructuredArrow V (affinePointNhdsInclusion x) :=
    StructuredArrow.mk (A.hom ≫ (affinePointNhdsInclusion x).map a')
  let f : A ⟶ C := StructuredArrow.homMk a'
  let g : B ⟶ C := StructuredArrow.homMk b' (Subsingleton.elim _ _)
  exact Zigzag.of_zag_trans (Zag.of_hom f) (Zag.of_inv g)

private noncomputable def affinePointNhdsRingDiagram {X : Scheme.{u}} (x : X) :
    (affinePointNhds x)ᵒᵖ ⥤ CommRingCat :=
  affinePointNhdsInclusion x ⋙ (OpenNhds.inclusion x).op ⋙ X.presheaf

private noncomputable def stalkCocone {X : Scheme.{u}} (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf) where
  pt := X.presheaf.stalk x
  ι := {
    app := fun i => X.presheaf.germ i.unop.1 x i.unop.2
    naturality := by
      intro i j f
      exact X.presheaf.germ_res' f x j.unop.2 }

private noncomputable def stalkCocone_isColimit {X : Scheme.{u}} (x : X) :
    IsColimit (stalkCocone x) := by
  apply IsColimit.ofIsoColimit (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ X.presheaf))
  refine Cocone.ext (Iso.refl _) ?_
  intro i
  rfl

private noncomputable def affinePointNhdsStalkCocone_isColimit {X : Scheme.{u}} (x : X) :
    IsColimit ((stalkCocone x).whisker (affinePointNhdsInclusion x) :
      Cocone (affinePointNhdsRingDiagram x)) :=
  haveI : Functor.Final (affinePointNhdsInclusion x) := affinePointNhdsInclusion_final x
  (Functor.Final.isColimitWhiskerEquiv (affinePointNhdsInclusion x) (stalkCocone x)).symm
    (stalkCocone_isColimit x)

private theorem specMap_comp_isoSpec_inv {X : Scheme.{u}} {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ≤ V) :
    Spec.map (X.presheaf.map (homOfLE h).op) ≫ hV.isoSpec.inv =
      hU.isoSpec.inv ≫ X.homOfLE h := by
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  exact Scheme.Opens.toSpecΓ_SpecMap_presheaf_map U V h

private theorem specMap_comp_isoSpec_inv_ι {X T : Scheme.{u}} {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ≤ V) (g : X ⟶ T) :
    Spec.map (X.presheaf.map (homOfLE h).op) ≫ (hV.isoSpec.inv ≫ (V.ι ≫ g)) =
      hU.isoSpec.inv ≫ (U.ι ≫ g) := by
  rw [reassoc_of% specMap_comp_isoSpec_inv hU hV h, Scheme.homOfLE_ι_assoc]

private theorem property_specStalk {T : Scheme.{u}} (P : ∀ X : Scheme.{u}, (X ⟶ T) → Prop)
    (hThickening : ∀ {X X' : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace X'] [QuasiSeparatedSpace X'] (i : X ⟶ X') (f : X' ⟶ T),
      IsThickening i → (P X (i ≫ f) ↔ P X' f))
    (hLimit : ∀ {I : Type u} [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ Scheme.{u})
      [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)]
      [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
      (c : Cone D) (_ : IsLimit c)
      [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
      (f : c.pt ⟶ T) (fi : ∀ i, D.obj i ⟶ T),
      (∀ {i j : I} (a : i ⟶ j), D.map a ≫ fi j = fi i) →
      (∀ i, c.π.app i ≫ fi i = f) →
      (∀ i, P (D.obj i) (fi i)) → P c.pt f)
    {X : Scheme.{u}} (g : X ⟶ T) (x : X)
    (hU : ∀ U : X.Opens, IsAffineOpen U → x ∈ U → P U.toScheme (U.ι ≫ g)) :
    P (Spec (X.presheaf.stalk x)) (X.fromSpecStalk x ≫ g) := by
  let cR : Cocone (affinePointNhdsRingDiagram x) :=
    (stalkCocone x).whisker (affinePointNhdsInclusion x)
  let D : (affinePointNhds x)ᵒᵖᵒᵖ ⥤ Scheme :=
    (affinePointNhdsRingDiagram x).op ⋙ Scheme.Spec
  let c : Cone D := Scheme.Spec.mapCone cR.op
  have hc : IsLimit c :=
    isLimitOfPreserves Scheme.Spec (affinePointNhdsStalkCocone_isColimit x).op
  let : IsAffine c.pt := by
    dsimp [c, D]
    infer_instance
  let : CompactSpace c.pt := (compactSpace_iff_quasiCompact c.pt).mpr (by infer_instance)
  let : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_of_isAffine c.pt
  let fi : ∀ i : (affinePointNhds x)ᵒᵖᵒᵖ, D.obj i ⟶ T := fun i =>
    let j : affinePointNhds x := i.unop.unop
    let U : X.Opens := j.obj.1
    j.property.isoSpec.inv ≫ U.ι ≫ g
  let : ∀ {i j : (affinePointNhds x)ᵒᵖᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a) := by
    intro i j a
    dsimp [D, affinePointNhdsRingDiagram]
    infer_instance
  let : ∀ i, IsAffine (D.obj i) := by
    intro i
    dsimp [D, affinePointNhdsRingDiagram]
    infer_instance
  let : ∀ i, CompactSpace (D.obj i) := fun i =>
    (compactSpace_iff_quasiCompact (D.obj i)).mpr (by infer_instance)
  let : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i => quasiSeparatedSpace_of_isAffine _
  let : IsCofiltered (affinePointNhds x) := affinePointNhds_isCofiltered x
  let : IsCofiltered ((affinePointNhds x)ᵒᵖᵒᵖ) :=
    IsCofiltered.of_equivalence (opOpEquivalence (affinePointNhds x)).symm
  refine hLimit D c hc (X.fromSpecStalk x ≫ g) fi ?_ ?_ fun i => ?_
  · intro i j a
    exact specMap_comp_isoSpec_inv_ι i.unop.unop.property j.unop.unop.property
      a.unop.unop.hom.le g
  · intro i
    let i₀ : affinePointNhds x := i.unop.unop
    dsimp [c, cR, stalkCocone, D, fi, affinePointNhdsRingDiagram, affinePointNhdsInclusion]
    show i₀.property.fromSpecStalk i₀.obj.2 ≫ g = X.fromSpecStalk x ≫ g
    exact congrArg (fun q => q ≫ g) (i₀.property.fromSpecStalk_eq_fromSpecStalk i₀.obj.2)
  · let j : affinePointNhds x := i.unop.unop
    let U : X.Opens := j.obj.1
    let : IsAffine U.toScheme := j.property
    let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp j.property.isCompact
    let : QuasiSeparatedSpace U.toScheme := quasiSeparatedSpace_of_isAffine U.toScheme
    exact (hThickening j.property.isoSpec.inv (U.ι ≫ g) (iso_is_thickening _)).mpr
      (hU U j.property j.obj.2)

private theorem isThickening_inclusion_radical {X : Scheme.{u}} (I : X.IdealSheafData) :
    IsThickening (Scheme.IdealSheafData.inclusion (Scheme.IdealSheafData.le_radical I)) := by
  let k : I.radical.subscheme ⟶ I.subscheme :=
    Scheme.IdealSheafData.inclusion (Scheme.IdealSheafData.le_radical I)
  show IsThickening k
  refine ⟨inferInstance, fun y => ?_⟩
  have hy' : I.subschemeι y ∈ (I.radical.support : Set X) :=
    (Scheme.IdealSheafData.support_radical I).symm ▸ subschemeι_mem_support I y
  have hy'' : I.subschemeι y ∈ Set.range I.radical.subschemeι :=
    I.radical.range_subschemeι.symm ▸ hy'
  obtain ⟨z, hz⟩ := hy''
  refine ⟨z, I.subschemeι.isClosedEmbedding.injective ?_⟩
  calc
    I.subschemeι (k z) = (k ≫ I.subschemeι) z := by simp
    _ = I.radical.subschemeι z := by rw [Scheme.IdealSheafData.inclusion_subschemeι]
    _ = I.subschemeι y := hz

private theorem nonempty_subscheme_sSup {X : Scheme.{u}} [CompactSpace X]
    (c : Set X.IdealSheafData) (hcc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (h : ∀ I ∈ c, Nonempty I.subscheme) : Nonempty (sSup c).subscheme := by
  obtain ⟨y, hy⟩ := hne
  let supportFamily : {I // I ∈ c} → Set X := fun I => I.1.support
  let : Nonempty {I // I ∈ c} := ⟨⟨y, hy⟩⟩
  have hdirected : Directed (· ⊇ ·) supportFamily := by
    intro a b
    rcases hcc.total a.2 b.2 with hab | hba
    · exact ⟨b, Scheme.IdealSheafData.support_antitone hab, le_rfl⟩
    · exact ⟨a, le_rfl, Scheme.IdealSheafData.support_antitone hba⟩
  have hInter : (⋂ i, supportFamily i).Nonempty :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed supportFamily
      hdirected
      (fun i => by
        obtain ⟨x⟩ := h i.1 i.2
        exact ⟨_, subschemeι_mem_support i.1 x⟩)
      (fun i => i.1.support.isClosed.isCompact)
      (fun i => i.1.support.isClosed)
  have hsupport : ((sSup c).support : Set X).Nonempty := by
    simpa [supportFamily, Scheme.IdealSheafData.support_sSup] using hInter
  exact nonempty_subscheme_of_support_nonempty _ hsupport

/-- **Stacks Project, Tag 0F06.** A property of quasi-compact, quasi-separated schemes
over a nonempty base, invariant under thickenings and stable under affine-transition
inverse limits and passage to a closed subscheme or its quasi-compact open complement,
holds at some field-valued point.

The `[Nonempty T]` hypothesis is deliberate and necessary rather than a weakening. Without it the
statement is false: `T = Spec PUnit` is empty and affine, hence quasi-compact and quasi-separated,
and for `P = fun _ _ ↦ True` all four remaining hypotheses hold, while the conclusion would supply
a morphism into `T` from the nonempty scheme `Spec K`. The Stacks statement leaves the condition
implicit; the proof below needs it to put `⊥` into the family of closed subschemes that are
nonempty and carry `P`, which is where Zorn's lemma is applied. -/
@[stacks 0F06]
public theorem exists_field_point {T : Scheme.{u}} [Nonempty T] [CompactSpace T]
    [QuasiSeparatedSpace T] (P : ∀ X : Scheme.{u}, (X ⟶ T) → Prop)
    (hThickening : ∀ {X X' : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace X'] [QuasiSeparatedSpace X'] (i : X ⟶ X') (f : X' ⟶ T),
      IsThickening i → (P X (i ≫ f) ↔ P X' f))
    (hLimit : ∀ {I : Type u} [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ Scheme.{u})
      [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)]
      [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
      (c : Cone D) (_ : IsLimit c)
      [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
      (f : c.pt ⟶ T) (fi : ∀ i, D.obj i ⟶ T),
      (∀ {i j : I} (a : i ⟶ j), D.map a ≫ fi j = fi i) →
      (∀ i, c.π.app i ≫ fi i = f) →
      (∀ i, P (D.obj i) (fi i)) → P c.pt f)
    (hClosedOrOpen : ∀ {X : Scheme.{u}} [CompactSpace X]
      [QuasiSeparatedSpace X] (f : X ⟶ T) (J : X.IdealSheafData)
      [CompactSpace J.subscheme] [QuasiSeparatedSpace J.subscheme]
      (V : X.Opens) (_hV : (V : Set X) = (J.support : Set X)ᶜ)
      [CompactSpace V.toScheme] [QuasiSeparatedSpace V.toScheme],
      P X f → (P V.toScheme (V.ι ≫ f) ∨
        P J.subscheme (J.subschemeι ≫ f)))
    (hP : P T (𝟙 T)) :
    ∃ (K : Type u) (_ : Field K) (g : Spec (.of K) ⟶ T),
      P (Spec (.of K)) g := by
  classical
  let S : Set T.IdealSheafData :=
    { I | P I.subscheme (I.subschemeι ≫ 𝟙 T) ∧ Nonempty I.subscheme }
  have hbot : ⊥ ∈ S := by
    exact ⟨(hThickening (Scheme.IdealSheafData.subschemeι (⊥ : T.IdealSheafData))
        (𝟙 T) (iso_is_thickening _)).mpr hP,
      Nonempty.map (asIso (Scheme.IdealSheafData.subschemeι (⊥ : T.IdealSheafData))).inv
        ‹Nonempty T›⟩
  have hchain : ∀ c : Set (T.IdealSheafData), c ⊆ S → IsChain (· ≤ ·) c →
      ∀ y ∈ c, ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := fun c hc hcc y hy =>
    ⟨sSup c, ⟨chainSup_property P hLimit (𝟙 T) c hcc ⟨y, hy⟩ fun I hI => (hc hI).1,
      nonempty_subscheme_sSup c hcc ⟨y, hy⟩ fun I hI => (hc hI).2⟩, fun _ hz => le_sSup hz⟩
  obtain ⟨I, -, hI, hmax⟩ := zorn_le_nonempty₀ S hchain ⊥ hbot
  let k : I.radical.subscheme ⟶ I.subscheme :=
    Scheme.IdealSheafData.inclusion (Scheme.IdealSheafData.le_radical I)
  have hk : IsThickening k := isThickening_inclusion_radical I
  have hradproperty : P I.radical.subscheme (I.radical.subschemeι ≫ 𝟙 T) := by
    simpa only [k, Scheme.IdealSheafData.inclusion_subschemeι, Category.assoc,
      Category.comp_id] using (hThickening k (I.subschemeι ≫ 𝟙 T) hk).mpr hI.1
  have hIradical : I.radical = I := le_antisymm
    (hmax ⟨hradproperty, ⟨(hk.2 (Classical.choice hI.2)).choose⟩⟩
      (Scheme.IdealSheafData.le_radical I))
    (Scheme.IdealSheafData.le_radical I)
  have : IsReduced I.subscheme := by
    rw [hIradical.symm.trans (Scheme.IdealSheafData.vanishingIdeal_support (I := I)).symm]
    exact Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal I.support
  let x : I.subscheme := Classical.choice hI.2
  let component : irreducibleComponents I.subscheme :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let η : I.subscheme := component.2.1.genericPoint
  have hηcomponent : closure {η} ∈ irreducibleComponents I.subscheme :=
    (component.2.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ component.2)).symm ▸ component.2
  have hηfield : IsField (I.subscheme.presheaf.stalk η) :=
    isField_stalk_of_closure_mem_irreducibleComponents I.subscheme η hηcomponent
  refine ⟨I.subscheme.presheaf.stalk η, hηfield.toField,
    I.subscheme.fromSpecStalk η ≫ I.subschemeι, ?_⟩
  show P (Spec (I.subscheme.presheaf.stalk η)) (I.subscheme.fromSpecStalk η ≫ I.subschemeι)
  exact property_specStalk P hThickening hLimit I.subschemeι η fun U hU hηU =>
    compactOpen_neighborhood_has_property P hThickening hClosedOrOpen S I hI
      (fun {J} hJ hIJ => hmax hJ hIJ) (fun J hJP hJne => ⟨hJP, hJne⟩) η hI.1 hU.isCompact hηU

end AlgebraicGeometry
