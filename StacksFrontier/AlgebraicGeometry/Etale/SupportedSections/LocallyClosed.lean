module

public import StacksFrontier.AlgebraicGeometry.Etale.SupportedSections.ClosedSupportEquiv
import all StacksFrontier.AlgebraicGeometry.Etale.SupportedSections.ClosedSupportEquiv
import all StacksFrontier.AlgebraicGeometry.Etale.SupportedSections.PullbackBranch

/-!
# Sections supported on a locally closed subset

The canonical bijection `AlgebraicGeometry.SmallEtale.supportedSectionsEquiv` is restriction
on every étale test object on which the two inverse images agree
(`AlgebraicGeometry.SmallEtale.supportedSectionsEquiv_restrict`, Stacks 0F6F). Running it
between two Zariski opens in which a locally closed `Z` is relatively closed gives the
restriction isomorphisms of Stacks 0F6F and 0F6G, and with them the group `H_Z(F)` of sections
supported on `Z`, realized on the canonical open `supportOpen`. The file ends with the
injective transition maps of Stacks 0F6H, their functoriality, and their naturality in the
sheaf.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

private theorem supportedSectionsEquiv_selectedBranch_restrict
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U U' : SmallEtale B S hS) (φ : U' ⟶ U) (Z' : Scheme.{u})
    (i : Z' ⟶ (SmallEtale.toScheme B S hS).obj U')
    [IsClosedImmersion i]
    [IsClosedImmersion (i ≫ (SmallEtale.toScheme B S hS).map φ)]
    (s : {s : F.obj.obj (op U) //
      supportSection B S hS F U s ⊆
        Set.range (i ≫ (SmallEtale.toScheme B S hS).map φ).base}) :
    F.obj.map (openObjectι B S hS U'
      (selectedBranchOpen ((SmallEtale.toScheme B S hS).map φ)
        (etale_toScheme_map B S hS φ)
        (i ≫ (SmallEtale.toScheme B S hS).map φ) i rfl)).op
        (supportedSectionsEquiv B S hS F U U' φ Z' i s).val =
      F.obj.map (openObjectι B S hS U'
        (selectedBranchOpen ((SmallEtale.toScheme B S hS).map φ)
          (etale_toScheme_map B S hS φ)
          (i ≫ (SmallEtale.toScheme B S hS).map φ) i rfl) ≫ φ).op s.val := by
  classical
  let φs := (SmallEtale.toScheme B S hS).map φ
  have hφ : Etale φs := etale_toScheme_map B S hS φ
  let Src := {s : F.obj.obj (op U) //
    supportSection B S hS F U s ⊆
      Set.range (i ≫ φs).base}
  let Tgt := {s' : F.obj.obj (op U') //
    supportSection B S hS F U' s' ⊆ Set.range i.base}
  let fwData (s : Src) :=
    cut_supportedSection_exists B S hS F U U' φ Z' i hφ s.val s.property
  let fw : Src → Tgt := fun s => ⟨(Classical.choose (fwData s)),
    (Classical.choose_spec (fwData s)).1⟩
  show F.obj.map
      (openObjectι B S hS U'
        (selectedBranchOpen φs hφ (i ≫ φs) i rfl)).op (fw s).val =
    F.obj.map
      (openObjectι B S hS U'
        (selectedBranchOpen φs hφ (i ≫ φs) i rfl) ≫ φ).op s.val
  exact (Classical.choose_spec (fwData s)).2

/-- The canonical bijection is restriction on any étale test object on which
the inverse images of the two closed subsets coincide. -/
@[stacks 0F6F "restriction characterization"]
public theorem supportedSectionsEquiv_restrict
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U U' : SmallEtale B S hS) (φ : U' ⟶ U)
    (Z' : Scheme.{u})
    (i : Z' ⟶ (SmallEtale.toScheme B S hS).obj U')
    [IsClosedImmersion i]
    [IsClosedImmersion (i ≫ (SmallEtale.toScheme B S hS).map φ)]
    (V : SmallEtale B S hS) (f : V ⟶ U')
    (h : Set.preimage ((SmallEtale.toScheme B S hS).map (f ≫ φ)).base
        (Set.range (i ≫ (SmallEtale.toScheme B S hS).map φ).base) =
      Set.preimage ((SmallEtale.toScheme B S hS).map f).base
        (Set.range i.base))
    (s : {s : F.obj.obj (op U) //
      supportSection B S hS F U s ⊆
        Set.range (i ≫ (SmallEtale.toScheme B S hS).map φ).base}) :
    F.obj.map f.op (supportedSectionsEquiv B S hS F U U' φ Z' i s).val =
      F.obj.map (f ≫ φ).op s.val := by
  classical
  let T := SmallEtale.toScheme B S hS
  let φs := T.map φ
  have hφ : Etale φs := etale_toScheme_map B S hS φ
  let g := i ≫ φs
  let O := selectedBranchOpen φs hφ g i rfl
  let jO := openObjectι B S hS U' O
  let K : Set (T.obj V) := Set.preimage (T.map f).base (Set.range i.base)
  let C : (T.obj V).Opens := ⟨Kᶜ,
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range.preimage
      (T.map f).continuous |>.isOpen_compl⟩
  let VC := openObject B S hS V C
  let jC := openObjectι B S hS V C
  let : HasPullbacks (SmallEtale B S hS) :=
    hasPullbacks_smallEtale B S hS
  let : PreservesLimitsOfShape WalkingCospan T :=
    preservesPullbacks_smallEtaleToScheme B S hS
  let P := Limits.pullback f jO
  let pV := Limits.pullback.fst f jO
  let pO := Limits.pullback.snd f jO
  let ts := supportedSectionsEquiv B S hS F U U' φ Z' i s
  let t := ts.val
  let a := F.obj.map f.op t
  let b := F.obj.map (f ≫ φ).op s.val
  have hbranch : (O : Set (T.obj U')) ∩ φs.base ⁻¹' Set.range g.base =
      Set.range i.base :=
    selectedBranchOpen_inter_preimage φs hφ g i rfl
  have htbound : supportSection B S hS F V a ⊆ K := by
    have hh := supportSection_restrict_subset_preimage B S hS F U' V f t
    exact hh.trans (Set.preimage_mono ts.property)
  have hbpre : supportSection B S hS F V b ⊆
      Set.preimage (T.map (f ≫ φ)).base (Set.range g.base) := by
    have hh := supportSection_restrict_subset_preimage B S hS F U V (f ≫ φ) s.val
    exact hh.trans (Set.preimage_mono s.property)
  have hbbound : supportSection B S hS F V b ⊆ K := by
    have hbpre' : supportSection B S hS F V b ⊆
        Set.preimage ((SmallEtale.toScheme B S hS).map (f ≫ φ)).base
          (Set.range (i ≫ (SmallEtale.toScheme B S hS).map φ).base) :=
      hbpre
    intro x hx
    have hx' := hbpre' hx
    rw [h] at hx'
    exact hx'
  let hc0 := Limits.isLimitOfPreserves T (Limits.pullback.isLimit f jO)
  let c1 := T.mapCone (Limits.pullback.cone f jO)
  let α := Limits.cospanCompIso T f jO
  let cP := (Limits.Cone.postcompose α.hom).obj c1
  have hc : IsLimit cP :=
    (Limits.IsLimit.equivOfNatIsoOfIso α c1 cP (Iso.refl cP)).1 hc0
  let hscheme : IsLimit (Limits.pullback.cone (T.map f) (T.map jO)) :=
    Limits.pullback.isLimit (T.map f) (T.map jO)
  let e := hc.conePointUniqueUpToIso hscheme
  have hefst : e.hom ≫ Limits.pullback.fst (T.map f) (T.map jO) = T.map pV := by
    simpa [e, cP, c1, α, pV, T, Limits.cospanCompIso] using
      hc.conePointUniqueUpToIso_hom_comp hscheme WalkingCospan.left
  have hinvfst : e.inv ≫ T.map pV = Limits.pullback.fst (T.map f) (T.map jO) := by
    calc
      e.inv ≫ T.map pV = e.inv ≫
          (e.hom ≫ Limits.pullback.fst (T.map f) (T.map jO)) := by rw [hefst]
      _ = Limits.pullback.fst (T.map f) (T.map jO) := by simp
  let I := ULift.{u + 1} Bool
  let W : I → SmallEtale B S hS := fun c =>
    match c with | ULift.up false => P | ULift.up true => VC
  let q : ∀ c, W c ⟶ V := fun c =>
    match c with | ULift.up false => pV | ULift.up true => jC
  have hcover' : ∀ x : T.obj V,
      ∃ c y, (T.map (q c)).base y = x := by
    intro x
    by_cases hx : x ∈ K
    · have hO : (T.map f).base x ∈ (O : Set (T.obj U')) := by
        have hh : (T.map f).base x ∈
            (O : Set (T.obj U')) ∩ φs.base ⁻¹' Set.range g.base := by
          rw [hbranch]
          exact hx
        exact hh.1
      have hrange : (T.map f).base x ∈ Set.range (T.map jO).base := by
        rw [openObjectι_range]
        exact hO
      have hpull : x ∈ Set.range (Limits.pullback.fst (T.map f) (T.map jO)).base := by
        rw [Scheme.Pullback.range_fst]
        exact hrange
      obtain ⟨y, hy⟩ := hpull
      refine ⟨ULift.up false, e.inv.base y, ?_⟩
      have heval := congrArg (fun m => m.base y) hinvfst
      have heval' : (T.map pV).base (e.inv.base y) =
          (Limits.pullback.fst (T.map f) (T.map jO)).base y := by
        simpa only [← Scheme.Hom.comp_apply] using heval
      simpa [q, W] using heval'.trans hy
    · have hxC : x ∈ (C : Set (T.obj V)) := hx
      have hrange : x ∈ Set.range (T.map jC).base := by
        rw [openObjectι_range]
        exact hxC
      obtain ⟨y, hy⟩ := hrange
      exact ⟨ULift.up true, y, by simpa [q, W] using hy⟩
  have hetale' : ∀ c, Etale (T.map (q c)) := fun c => etale_toScheme_map B S hS (q c)
  have hcut := supportedSectionsEquiv_selectedBranch_restrict
    B S hS F U U' φ Z' i s
  have hcond : pV ≫ f = pO ≫ jO := Limits.pullback.condition
  have hcomp : pO ≫ jO ≫ φ = (pV ≫ f) ≫ φ := by
    calc
      pO ≫ jO ≫ φ = (pO ≫ jO) ≫ φ := rfl
      _ = (pV ≫ f) ≫ φ := congrArg (fun k => k ≫ φ) hcond.symm
  have hpullEq : F.obj.map pV.op a = F.obj.map pV.op b := by
    calc
      F.obj.map pV.op a = F.obj.map (pV ≫ f).op t := by simp [a, Functor.map_comp]
      _ = F.obj.map (pO ≫ jO).op t := by rw [Limits.pullback.condition]
      _ = F.obj.map pO.op (F.obj.map jO.op t) := by simp [Functor.map_comp]
      _ = F.obj.map pO.op (F.obj.map (jO ≫ φ).op s.val) := by rw [hcut]
      _ = F.obj.map (pO ≫ (jO ≫ φ)).op s.val := by simp [Functor.map_comp]
      _ = F.obj.map ((pV ≫ f) ≫ φ).op s.val :=
            congrArg (fun k => F.obj.map k.op s.val) hcomp
      _ = F.obj.map (pV ≫ (f ≫ φ)).op s.val := by rw [Category.assoc]
      _ = F.obj.map pV.op b := by simp [b, Functor.map_comp]
  have hzero : ∀ c, supportSection B S hS F V c ⊆ K → F.obj.map jC.op c = 0 := by
    intro c hc
    apply section_restrict_zero_of_disjoint_support B S hS F V VC jC c
    apply Set.disjoint_left.mpr
    intro x hx hsx
    have hxC : x ∈ (C : Set (T.obj V)) := by
      rw [← openObjectι_range]
      exact hx
    exact hxC (hc hsx)
  apply section_eq_of_restrict_eq_on_cover B S hS F W q hcover' hetale' a b
  intro c
  rcases c with ⟨c⟩
  cases c
  · simpa [q, W] using hpullEq
  · simpa [q, W] using (hzero a htbound).trans (hzero b hbbound).symm
section LocallyClosedSupport

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})

/-- The subgroup of sections with support in a prescribed subset. -/
@[expose] public def sectionsSupportedOn (W : SmallEtale B S hS)
    (Z : Set ((SmallEtale.toScheme B S hS).obj W)) :
    AddSubgroup (F.obj.obj (op W)) where
  carrier := {s | supportSection B S hS F W s ⊆ Z}
  zero_mem' := by
    have hz : zeroOpen B S hS F W 0 = ⊤ := by
      apply top_unique
      apply le_sSup
      refine ⟨W, 𝟙 W, ?_, ?_, ?_⟩
      · change IsOpenImmersion (𝟙 _)
        infer_instance
      · ext x
        simp
      · simp
    simp [supportSection, hz]
  add_mem' := by
    intro s t hs ht
    exact (supportSection_add_subset B S hS F W s t).trans
      (Set.union_subset hs ht)
  neg_mem' := by
    intro s hs
    have hz : zeroOpen B S hS F W s ≤
        zeroOpen B S hS F W (-s) := by
      apply sSup_le
      rintro U ⟨V, f, hf, hU, he⟩
      apply le_sSup
      exact ⟨V, f, hf, hU, by simp only [map_neg, he, neg_zero]⟩
    exact (Set.compl_subset_compl.mpr hz).trans hs

/-- Sections over an open of `W` supported in `Z`. Only the underlying subset
of the locally closed subscheme matters for this construction. -/
public abbrev supportedSectionsOnOpen (W : SmallEtale B S hS)
    (Z : Set ((SmallEtale.toScheme B S hS).obj W))
    (U : ((SmallEtale.toScheme B S hS).obj W).Opens) :=
  ↥(sectionsSupportedOn B S hS F (openObject B S hS W U)
    (U.ι.base ⁻¹' Z))

/-- Restriction to a smaller open containing a closed support is an equivalence. -/
private noncomputable def closedSupportRestrictionData
    (W : SmallEtale B S hS) (Z : Set ((SmallEtale.toScheme B S hS).obj W))
    (U V : ((SmallEtale.toScheme B S hS).obj W).Opens)
    (h : V ≤ U) (hZV : Z ⊆ V) (hZU : IsClosed (U.ι.base ⁻¹' Z)) :
    {e : supportedSectionsOnOpen B S hS F W Z U ≃
        supportedSectionsOnOpen B S hS F W Z V //
      ∀ s, (e s).val = F.obj.map (openObjectHomOfLE B S hS W h).op s.val} := by
  let φ := openObjectHomOfLE B S hS W h
  let f := (SmallEtale.toScheme B S hS).map φ
  have hf : f = Scheme.homOfLE _ h := openObjectHomOfLE_map B S hS W h
  have hpre : f.base ⁻¹' (U.ι.base ⁻¹' Z) = V.ι.base ⁻¹' Z := by
    rw [hf, ← Set.preimage_comp]
    congr 1
    exact congrArg (fun g : (↑V : Scheme) ⟶ _ => (g.base : _ → _))
      (Scheme.homOfLE_ι _ h)
  let C : TopologicalSpace.Closeds (↑V : Scheme) :=
    ⟨V.ι.base ⁻¹' Z, hpre ▸ hZU.preimage f.continuous⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  let i := I.subschemeι
  have hi : Set.range i.base = V.ι.base ⁻¹' Z := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hcomp : Set.range (i ≫ f).base = U.ι.base ⁻¹' Z := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hi, ← hpre]
    apply Set.image_preimage_eq_of_subset
    intro x hx
    rw [hf]
    refine ⟨⟨x.val, hZV hx⟩, ?_⟩
    apply Subtype.ext
    exact Scheme.homOfLE_apply h ⟨x.val, hZV hx⟩
  have : IsOpenImmersion f := hf ▸ inferInstance
  have : IsClosedImmersion (i ≫ f) :=
    IsClosedImmersion.of_isPreimmersion _ (hcomp ▸ hZU)
  let e := supportedSectionsEquiv B S hS F _ _ φ I.subscheme i
  let a : supportedSectionsOnOpen B S hS F W Z U ≃
      {s : F.obj.obj (op (openObject B S hS W U)) //
        supportSection B S hS F _ s ⊆
          Set.range (i ≫ f).base} :=
    { toFun := fun s => ⟨s.val, by rw [hcomp]; exact s.property⟩
      invFun := fun s => ⟨s.val, by
        change supportSection B S hS F _ s.val ⊆ _
        rw [← hcomp]
        exact s.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let b : {s : F.obj.obj (op (openObject B S hS W V)) //
        supportSection B S hS F _ s ⊆ Set.range i.base} ≃
      supportedSectionsOnOpen B S hS F W Z V :=
    { toFun := fun s => ⟨s.val, by
        change supportSection B S hS F _ s.val ⊆ _
        rw [← hi]
        exact s.property⟩
      invFun := fun s => ⟨s.val, by rw [hi]; exact s.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨a.trans (e.trans b), ?_⟩
  intro s
  have he := supportedSectionsEquiv_restrict B S hS F _ _ φ I.subscheme i
    _ (𝟙 _) (by simpa only [Category.id_comp, CategoryTheory.Functor.map_id] using
      (hcomp ▸ hi ▸ hpre)) (a s)
  change (e (a s)).val = _
  dsimp only [e, a, φ] at he ⊢
  simpa only [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply,
    Category.id_comp, Equiv.coe_fn_mk] using he

/-- The additive restriction equivalence for nested admissible opens. -/
public noncomputable def closedSupportRestrictionEquiv
    (W : SmallEtale B S hS) (Z : Set ((SmallEtale.toScheme B S hS).obj W))
    (U V : ((SmallEtale.toScheme B S hS).obj W).Opens)
    (h : V ≤ U) (hZV : Z ⊆ V) (hZU : IsClosed (U.ι.base ⁻¹' Z)) :
    supportedSectionsOnOpen B S hS F W Z U ≃+
      supportedSectionsOnOpen B S hS F W Z V where
  toEquiv := (closedSupportRestrictionData B S hS F W Z U V h hZV hZU).val
  map_add' s t := by
    apply Subtype.ext
    let d := closedSupportRestrictionData B S hS F W Z U V h hZV hZU
    change (d.val (s + t)).val = (d.val s).val + (d.val t).val
    rw [d.property, d.property, d.property]
    exact map_add _ _ _

/-- The restriction equivalence for nested admissible opens is given by restriction. -/
@[simp] public theorem closedSupportRestrictionEquiv_apply
    (W : SmallEtale B S hS) (Z : Set ((SmallEtale.toScheme B S hS).obj W))
    (U V : ((SmallEtale.toScheme B S hS).obj W).Opens)
    (h : V ≤ U) (hZV : Z ⊆ V) (hZU : IsClosed (U.ι.base ⁻¹' Z))
    (s : supportedSectionsOnOpen B S hS F W Z U) :
    (closedSupportRestrictionEquiv B S hS F W Z U V h hZV hZU s).val =
      F.obj.map (openObjectHomOfLE B S hS W h).op s.val :=
  (closedSupportRestrictionData B S hS F W Z U V h hZV hZU).property s

/-- The canonical bijection of Tag 0F6G (merged into 0F6F), including its
abelian-group structure. Both opens contain the given support as a closed subset. -/
@[stacks 0F6F "locally closed support", stacks 0F6G "the canonical bijection"]
public noncomputable def locallyClosedSupportEquiv
    (W : SmallEtale B S hS) (Z : Set ((SmallEtale.toScheme B S hS).obj W))
    (U V : ((SmallEtale.toScheme B S hS).obj W).Opens)
    (hZU : Z ⊆ U) (hZV : Z ⊆ V)
    (hUc : IsClosed (U.ι.base ⁻¹' Z)) (hVc : IsClosed (V.ι.base ⁻¹' Z)) :
    supportedSectionsOnOpen B S hS F W Z U ≃+
      supportedSectionsOnOpen B S hS F W Z V :=
  (closedSupportRestrictionEquiv B S hS F W Z U (U ⊓ V) inf_le_left
    (Set.subset_inter hZU hZV) hUc).trans
  (closedSupportRestrictionEquiv B S hS F W Z V (U ⊓ V) inf_le_right
    (Set.subset_inter hZU hZV) hVc).symm

/-- Restricting along two nested inclusions of Zariski opens is restricting along the composite. -/
private theorem map_openObjectHomOfLE_map_openObjectHomOfLE (W : SmallEtale B S hS)
    {U V V' : ((SmallEtale.toScheme B S hS).obj W).Opens} (h : V ≤ U) (k : V' ≤ V)
    (s : F.obj.obj (op (openObject B S hS W U))) :
    F.obj.map (openObjectHomOfLE B S hS W k).op (F.obj.map (openObjectHomOfLE B S hS W h).op s) =
      F.obj.map (openObjectHomOfLE B S hS W (k.trans h)).op s := by
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
  simp only [← op_comp, openObjectHomOfLE_comp]

/-- For nested opens the canonical identification is restriction. -/
@[stacks 0F6F "locally closed support, restriction", stacks 0F6G "the canonical bijection"]
public theorem locallyClosedSupportEquiv_restrict
    (W : SmallEtale B S hS) (Z : Set ((SmallEtale.toScheme B S hS).obj W))
    (U V : ((SmallEtale.toScheme B S hS).obj W).Opens)
    (hZU : Z ⊆ U) (hZV : Z ⊆ V)
    (hUc : IsClosed (U.ι.base ⁻¹' Z)) (hVc : IsClosed (V.ι.base ⁻¹' Z))
    (h : V ≤ U) (s : supportedSectionsOnOpen B S hS F W Z U) :
    (locallyClosedSupportEquiv B S hS F W Z U V hZU hZV hUc hVc s).val =
      F.obj.map (openObjectHomOfLE B S hS W h).op s.val := by
  let r := closedSupportRestrictionEquiv B S hS F W Z U V h hZV hUc
  have he : locallyClosedSupportEquiv B S hS F W Z U V hZU hZV hUc hVc s = r s := by
    apply (closedSupportRestrictionEquiv B S hS F W Z V (U ⊓ V) inf_le_right
      (Set.subset_inter hZU hZV) hVc).injective
    dsimp only [locallyClosedSupportEquiv, AddEquiv.trans_apply]
    rw [AddEquiv.apply_symm_apply]
    apply Subtype.ext
    simp only [closedSupportRestrictionEquiv_apply, r]
    exact (map_openObjectHomOfLE_map_openObjectHomOfLE B S hS F W _ _ _).symm
  rw [he]
  exact closedSupportRestrictionEquiv_apply B S hS F W Z U V h hZV hUc s

/-- The canonical open `W \ (closure Z \ Z)` used to define `H_Z`. -/
@[expose] public def supportOpen (W : SmallEtale B S hS)
    (Z : Set ((SmallEtale.toScheme B S hS).obj W)) (hZ : IsLocallyClosed Z) :
    ((SmallEtale.toScheme B S hS).obj W).Opens :=
  ⟨coborder Z, hZ.isOpen_coborder⟩

/-- A locally closed subset is contained in its canonical open. -/
public theorem subset_supportOpen (W : SmallEtale B S hS)
    (Z : Set ((SmallEtale.toScheme B S hS).obj W)) (hZ : IsLocallyClosed Z) :
    Z ⊆ supportOpen B S hS W Z hZ := subset_coborder

/-- A locally closed subset is closed in its canonical open. -/
public theorem isClosed_supportOpen_preimage (W : SmallEtale B S hS)
    (Z : Set ((SmallEtale.toScheme B S hS).obj W)) (hZ : IsLocallyClosed Z) :
    IsClosed ((supportOpen B S hS W Z hZ).ι.base ⁻¹' Z) :=
  isClosed_preimage_val_coborder

/-- `H_Z(F)`, defined on the canonical open. This also covers a locally closed
subscheme of any object `W` of the small étale site, as in the text after 0F6I. -/
public abbrev supportedSections (W : SmallEtale B S hS)
    (Z : Set ((SmallEtale.toScheme B S hS).obj W)) (hZ : IsLocallyClosed Z) :=
  supportedSectionsOnOpen B S hS F W Z (supportOpen B S hS W Z hZ)

/-- Identification of `H_Z(F)` with sections on any admissible open. -/
@[expose] public noncomputable def supportedSectionsOpenEquiv (W : SmallEtale B S hS)
    (Z : Set ((SmallEtale.toScheme B S hS).obj W)) (hZ : IsLocallyClosed Z)
    (U : ((SmallEtale.toScheme B S hS).obj W).Opens)
    (hZU : Z ⊆ U) (hUc : IsClosed (U.ι.base ⁻¹' Z)) :
    supportedSections B S hS F W Z hZ ≃+ supportedSectionsOnOpen B S hS F W Z U :=
  locallyClosedSupportEquiv B S hS F W Z _ U
    (subset_supportOpen B S hS W Z hZ) hZU
    (isClosed_supportOpen_preimage B S hS W Z hZ) hUc

/-- A relatively closed inclusion reverses inclusion of the canonical opens. -/
public theorem supportOpen_antitone (W : SmallEtale B S hS)
    (Z Z' : Set ((SmallEtale.toScheme B S hS).obj W))
    (hZ : IsLocallyClosed Z) (hZ' : IsLocallyClosed Z') (h : Z ⊆ Z')
    (hc : IsClosed ((Subtype.val : Z' → _) ⁻¹' Z)) :
    supportOpen B S hS W Z' hZ' ≤ supportOpen B S hS W Z hZ := by
  have he : closure Z ∩ Z' = Z := by
    rw [isClosed_induced_iff] at hc
    obtain ⟨C, hC, he⟩ := hc
    have hZC : Z ⊆ C := by
      intro x hx
      have : (⟨x, h hx⟩ : Z') ∈ (Subtype.val : Z' → _) ⁻¹' Z := hx
      rw [← he] at this
      exact this
    apply Set.Subset.antisymm
    · rintro x ⟨hx, hx'⟩
      have hxC : x ∈ C := (closure_minimal hZC hC) hx
      have : (⟨x, hx'⟩ : Z') ∈ (Subtype.val : Z' → _) ⁻¹' C := hxC
      rw [he] at this
      exact this
    · exact Set.subset_inter subset_closure h
  intro x hx
  change x ∈ coborder Z' at hx
  show x ∈ coborder Z
  rw [mem_coborder_iff_imp] at hx ⊢
  intro hxZ
  have hxZ' := hx (closure_mono h hxZ)
  exact he ▸ (show x ∈ closure Z ∩ Z' from ⟨hxZ, hxZ'⟩)

/-- The natural injective map of 0F6H, implemented by restriction to the
canonical open of the larger support and inclusion of supported subgroups. -/
@[expose] public noncomputable def supportedSectionsMap (W : SmallEtale B S hS)
    (Z Z' : Set ((SmallEtale.toScheme B S hS).obj W))
    (hZ : IsLocallyClosed Z) (hZ' : IsLocallyClosed Z') (h : Z ⊆ Z')
    (hc : IsClosed ((Subtype.val : Z' → _) ⁻¹' Z)) :
    supportedSections B S hS F W Z hZ →+ supportedSections B S hS F W Z' hZ' :=
  let e := closedSupportRestrictionEquiv B S hS F W Z _ _
    (supportOpen_antitone B S hS W Z Z' hZ hZ' h hc)
    (h.trans (subset_supportOpen B S hS W Z' hZ'))
    (isClosed_supportOpen_preimage B S hS W Z hZ)
  { toFun := fun s => ⟨(e s).val, (e s).property.trans (Set.preimage_mono h)⟩
    map_zero' := by
      have he := congrArg Subtype.val e.map_zero
      exact Subtype.ext he
    map_add' := by
      intro s t
      have he := congrArg Subtype.val (e.map_add s t)
      exact Subtype.ext he }

/-- The transition map of supported sections is injective. -/
public theorem supportedSectionsMap_injective (W : SmallEtale B S hS)
    (Z Z' : Set ((SmallEtale.toScheme B S hS).obj W))
    (hZ : IsLocallyClosed Z) (hZ' : IsLocallyClosed Z') (h : Z ⊆ Z')
    (hc : IsClosed ((Subtype.val : Z' → _) ⁻¹' Z)) :
    Function.Injective (supportedSectionsMap B S hS F W Z Z' hZ hZ' h hc) := by
  intro s t he
  apply (closedSupportRestrictionEquiv B S hS F W Z _ _
    (supportOpen_antitone B S hS W Z Z' hZ hZ' h hc)
    (h.trans (subset_supportOpen B S hS W Z' hZ'))
    (isClosed_supportOpen_preimage B S hS W Z hZ)).injective
  have hh := congrArg Subtype.val he
  exact Subtype.ext hh

/-- The transition map of supported sections is given by restriction to the canonical open of
the larger support. -/
@[simp] public theorem supportedSectionsMap_apply (W : SmallEtale B S hS)
    (Z Z' : Set ((SmallEtale.toScheme B S hS).obj W))
    (hZ : IsLocallyClosed Z) (hZ' : IsLocallyClosed Z') (h : Z ⊆ Z')
    (hc : IsClosed ((Subtype.val : Z' → _) ⁻¹' Z))
    (s : supportedSections B S hS F W Z hZ) :
    (supportedSectionsMap B S hS F W Z Z' hZ hZ' h hc s).val =
      F.obj.map (openObjectHomOfLE B S hS W
        (supportOpen_antitone B S hS W Z Z' hZ hZ' h hc)).op s.val :=
  closedSupportRestrictionEquiv_apply B S hS F W Z _ _
    (supportOpen_antitone B S hS W Z Z' hZ hZ' h hc)
    (h.trans (subset_supportOpen B S hS W Z' hZ'))
    (isClosed_supportOpen_preimage B S hS W Z hZ) s


/-- The supported-section transition for an identity inclusion is the identity. -/
@[simp] public theorem supportedSectionsMap_refl (W : SmallEtale B S hS)
    (Z : Set ((SmallEtale.toScheme B S hS).obj W)) (hZ : IsLocallyClosed Z)
    (hc : IsClosed ((Subtype.val : Z → _) ⁻¹' Z)) :
    supportedSectionsMap B S hS F W Z Z hZ hZ Set.Subset.rfl hc = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro s
  apply Subtype.ext
  rw [supportedSectionsMap_apply]
  simp

/-- Supported-section transitions compose as the inclusions of supports do. -/
public theorem supportedSectionsMap_comp (W : SmallEtale B S hS)
    (Z₁ Z₂ Z₃ : Set ((SmallEtale.toScheme B S hS).obj W))
    (h₁ : IsLocallyClosed Z₁) (h₂ : IsLocallyClosed Z₂) (h₃ : IsLocallyClosed Z₃)
    (h₁₂ : Z₁ ⊆ Z₂) (h₂₃ : Z₂ ⊆ Z₃)
    (hc₁₂ : IsClosed ((Subtype.val : Z₂ → _) ⁻¹' Z₁))
    (hc₂₃ : IsClosed ((Subtype.val : Z₃ → _) ⁻¹' Z₂))
    (hc₁₃ : IsClosed ((Subtype.val : Z₃ → _) ⁻¹' Z₁)) :
    (supportedSectionsMap B S hS F W Z₂ Z₃ h₂ h₃ h₂₃ hc₂₃).comp
        (supportedSectionsMap B S hS F W Z₁ Z₂ h₁ h₂ h₁₂ hc₁₂) =
      supportedSectionsMap B S hS F W Z₁ Z₃ h₁ h₃ (h₁₂.trans h₂₃) hc₁₃ := by
  apply AddMonoidHom.ext
  intro s
  apply Subtype.ext
  show (supportedSectionsMap B S hS F W Z₂ Z₃ h₂ h₃ h₂₃ hc₂₃
    (supportedSectionsMap B S hS F W Z₁ Z₂ h₁ h₂ h₁₂ hc₁₂ s)).val = _
  simp only [supportedSectionsMap_apply]
  exact map_openObjectHomOfLE_map_openObjectHomOfLE B S hS F W _ _ _

variable {F} {G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v}}

/-- A sheaf morphism acts on supported sections by its component on the
canonical open. -/
@[expose] public noncomputable def supportedSectionsSheafMap (φ : F ⟶ G)
    (W : SmallEtale B S hS) (Z : Set ((SmallEtale.toScheme B S hS).obj W))
    (hZ : IsLocallyClosed Z) :
    supportedSections B S hS F W Z hZ →+ supportedSections B S hS G W Z hZ where
  toFun s := ⟨φ.hom.app _ s.val,
    (supportSection_map_subset B S hS F G φ _ s.val).trans
      s.property⟩
  map_zero' := Subtype.ext ((φ.hom.app (op (openObject B S hS W
    (supportOpen B S hS W Z hZ)))).hom.map_zero)
  map_add' s t := Subtype.ext ((φ.hom.app (op (openObject B S hS W
    (supportOpen B S hS W Z hZ)))).hom.map_add s.val t.val)

/-- Naturality in the abelian sheaf of the transition of 0F6H. -/
public theorem supportedSectionsMap_naturality (φ : F ⟶ G)
    (W : SmallEtale B S hS) (Z Z' : Set ((SmallEtale.toScheme B S hS).obj W))
    (hZ : IsLocallyClosed Z) (hZ' : IsLocallyClosed Z') (h : Z ⊆ Z')
    (hc : IsClosed ((Subtype.val : Z' → _) ⁻¹' Z)) :
    (supportedSectionsSheafMap B S hS φ W Z' hZ').comp
        (supportedSectionsMap B S hS F W Z Z' hZ hZ' h hc) =
      (supportedSectionsMap B S hS G W Z Z' hZ hZ' h hc).comp
        (supportedSectionsSheafMap B S hS φ W Z hZ) := by
  apply AddMonoidHom.ext
  intro s
  apply Subtype.ext
  show φ.hom.app _ (supportedSectionsMap B S hS F W Z Z' hZ hZ' h hc s).val = _
  rw [supportedSectionsMap_apply]
  show φ.hom.app _ (F.obj.map _ s.val) =
    (supportedSectionsMap B S hS G W Z Z' hZ hZ' h hc
      (supportedSectionsSheafMap B S hS φ W Z hZ s)).val
  rw [supportedSectionsMap_apply]
  exact ConcreteCategory.congr_hom (φ.hom.naturality _) s.val

end LocallyClosedSupport

end AlgebraicGeometry.SmallEtale

end
