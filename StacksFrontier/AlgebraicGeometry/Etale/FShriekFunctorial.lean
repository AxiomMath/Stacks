module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenInclusion

/-!
# Functoriality of the proper-support direct image in the sheaf

Let `f : X ⟶ Y` be a morphism of a big étale site which is locally of finite type as a
morphism of schemes. A morphism `φ : F ⟶ H` of abelian sheaves on the small étale site of `X`
carries sections with proper support to sections with proper support, because the support of
`φ(s)` is contained in the support of `s`. Hence `φ` induces a morphism `f_! F ⟶ f_! H`,
uniquely determined by its composite with the monomorphisms into the ordinary direct images,
and this assignment is compatible with identities and composition.

For an open immersion `j : X' ⟶ X` the extension-by-zero monomorphism
`AlgebraicGeometry.SmallEtale.openInclusionShriekMap` is natural in the sheaf: extending a
section and then pushing it along `φ` agrees with pushing it along the restriction of `φ` and
then extending.

## Main definitions

* `AlgebraicGeometry.SmallEtale.fShriekMap`: the morphism of proper-support direct images
  induced by a morphism of abelian sheaves, bundled with its characterising equation.

## Main results

* `AlgebraicGeometry.SmallEtale.fShriekMap_id` and
  `AlgebraicGeometry.SmallEtale.fShriekMap_comp`: the induced morphisms respect identities and
  composition, so `f_!` is a functor on abelian sheaves.
* `AlgebraicGeometry.SmallEtale.openInclusionShriekMap_naturality`: extension by zero from an
  open subscheme is natural in the abelian sheaf.

## Implementation notes

The induced morphism is built sectionwise: on a test object the monomorphism into the ordinary
direct image is injective, so a section of `f_! F` has at most one image in `f_! H`, and it has
one because the support of its image under `φ` is a closed subset of the original support,
hence proper over the test object. Bundling the morphism with the equation characterising it
makes the functor laws immediate from monicity.

Naturality of extension by zero is checked after composing with the monomorphism into the
ordinary direct image, where the two sides are compared through the unit of the adjunction
between post-composition with `j` and base change along `j`: the unit is injective on sections
over a test object whose support is contained in the open piece, and both sides have that
property.

## References

* [Stacks Project, Tag 0F53](https://stacks.math.columbia.edu/tag/0F53)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.SmallEtale

/-- The induced map on proper-support direct images, characterized by its
inclusion into ordinary direct image. -/
@[stacks 0F53 "open_inclusion_compatibility: induced maps"]
public noncomputable def fShriekMap
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)]
    (F H : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (φ : F ⟶ H) :
    let G := (SmallEtale.fShriekSubsheaf B f F).val
    let K := (SmallEtale.fShriekSubsheaf B f H).val
    let push := (smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{v}
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)
    {m : G.obj.left ⟶ K.obj.left // m ≫ K.arrow = G.arrow ≫ push.map φ} := by
  classical
  dsimp only
  let G := (SmallEtale.fShriekSubsheaf B f F).val
  let K := (SmallEtale.fShriekSubsheaf B f H).val
  let push := (smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
  change {m : G.obj.left ⟶ K.obj.left // m ≫ K.arrow = G.arrow ≫ push.map φ}
  let α : G.obj.left ⟶ push.obj H := G.arrow ≫ push.map φ
  have hrange (V : (SmallEtale B Y.obj Y.property)ᵒᵖ)
      (x : G.obj.left.obj.obj V) : ∃ y : K.obj.left.obj.obj V,
      K.arrow.hom.app V y = α.hom.app V x := by
      let s := G.arrow.hom.app V x
      let U := (smallEtaleBaseChange B f).obj V.unop
      change F.obj.obj (op U) at s
      have hmap : (push.map φ).hom.app V = φ.hom.app (op U) := by
        exact Functor.sheafPushforwardContinuous_map_hom_app
            (smallEtaleBaseChange B f) AddCommGrpCat.{v}
            (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B X.obj X.property) φ V
      have hsupport : SmallEtale.supportSection B X.obj X.property H U
          (φ.hom.app (op U) s) ⊆
        SmallEtale.supportSection B X.obj X.property F U s := by
        have hzero : SmallEtale.zeroOpen B X.obj X.property F U s ≤
            SmallEtale.zeroOpen B X.obj X.property H U (φ.hom.app (op U) s) := by
          unfold SmallEtale.zeroOpen
          apply sSup_le
          rintro W ⟨T, g, hgOpen, hW, hzero⟩
          change (W : Set ((SmallEtale.toScheme B X.obj X.property).obj U)) ⊆
            (SmallEtale.zeroOpen B X.obj X.property H U
              (φ.hom.app (op U) s) : Set _)
          rw [hW]
          let : IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map g) := hgOpen
          exact (SmallEtale.map_eq_zero_iff_le_zeroOpen
            B X.obj X.property H U (φ.hom.app (op U) s) T g).mp (by
              calc
                H.obj.map g.op (φ.hom.app (op U) s) =
                    φ.hom.app (op T) (F.obj.map g.op s) := by
                      simpa only [ConcreteCategory.comp_apply] using
                        (ConcreteCategory.congr_hom (φ.hom.naturality g.op) s).symm
                _ = 0 := by rw [hzero, map_zero])
        intro z hz
        change z ∉ (SmallEtale.zeroOpen B X.obj X.property H U
          (φ.hom.app (op U) s) : Set _ ) at hz
        change z ∉ (SmallEtale.zeroOpen B X.obj X.property F U s : Set _)
        intro hf
        exact hz (hzero hf)
      have hs : SmallEtale.properSupportSections B f H V.unop
          (φ.hom.app (op U) s) := by
        change SmallEtale.properSupportSections B f H V.unop
          ((push.map φ).hom.app V ((G.arrow.hom.app V) x))
        -- The support of an image section is contained in the original support.
        have hproper : SmallEtale.properSupportSections B f F V.unop s :=
          ((SmallEtale.fShriekSubsheaf B f F).property V.unop s).mp ⟨x, rfl⟩
        -- Properness descends to a closed subset of the support.
        let Z := (SmallEtale.zeroOpen B X.obj X.property F
          ((smallEtaleBaseChange B f).obj V.unop) s).compl
        let Z' := (SmallEtale.zeroOpen B X.obj X.property H U
          (φ.hom.app (op U) s)).compl
        have hle : Z' ≤ Z := by
          change SmallEtale.supportSection B X.obj X.property H
              U (φ.hom.app (op U) s) ⊆
            SmallEtale.supportSection B X.obj X.property F
              U s
          exact hsupport
        change IsProper ((Scheme.IdealSheafData.vanishingIdeal Z').subschemeι ≫
          B.inclusion.map (pullback.fst V.unop.obj.hom f))
        rw [← Scheme.IdealSheafData.inclusion_subschemeι
          (Scheme.IdealSheafData.vanishingIdeal_antimono hle), Category.assoc]
        let : IsProper ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫
            B.inclusion.map (pullback.fst V.unop.obj.hom f)) := hproper
        infer_instance
      have hrange := (SmallEtale.fShriekSubsheaf B f H).property V.unop
        (φ.hom.app (op U) s)
      exact (hrange.mpr hs).elim fun y hy => ⟨y, by
        change K.arrow.hom.app V y =
          (push.map φ).hom.app V ((G.arrow.hom.app V) x)
        rw [hmap]
        change K.arrow.hom.app V y =
          φ.hom.app (op ((smallEtaleBaseChange B f).obj V.unop))
            ((G.arrow.hom.app V) x)
        change K.arrow.hom.app V y =
          φ.hom.app (op ((smallEtaleBaseChange B f).obj V.unop))
            ((G.arrow.hom.app V) x) at hy
        exact hy⟩
  haveI : Mono K.arrow.hom := by
    have : Mono K.arrow := inferInstance
    exact (sheafToPresheaf _ _).map_mono K.arrow
  let mp : G.obj.left.obj ⟶ K.obj.left.obj := by
    have hi (U : (SmallEtale B Y.obj Y.property)ᵒᵖ) :
        Function.Injective (K.arrow.hom.app U) :=
      (AddCommGrpCat.mono_iff_injective (K.arrow.hom.app U)).mp inferInstance
    let b (U : (SmallEtale B Y.obj Y.property)ᵒᵖ) :
        G.obj.left.obj.obj U →+ K.obj.left.obj.obj U := {
      toFun := fun x => Classical.choose (hrange U x)
      map_zero' := by
        apply hi
        simpa using (Classical.choose_spec (hrange U (0 : G.obj.left.obj.obj U))).trans
          ((α.hom.app U).hom.map_zero)
      map_add' := by
        intro x y
        apply hi
        calc
          (K.arrow.hom.app U).hom (Classical.choose (hrange U (x + y))) =
              (α.hom.app U).hom (x + y) := Classical.choose_spec (hrange U (x + y))
          _ = (α.hom.app U).hom x + (α.hom.app U).hom y :=
            (α.hom.app U).hom.map_add _ _
          _ = (K.arrow.hom.app U).hom (Classical.choose (hrange U x)) +
              (K.arrow.hom.app U).hom (Classical.choose (hrange U y)) := by
            rw [Classical.choose_spec (hrange U x), Classical.choose_spec (hrange U y)]
          _ = (K.arrow.hom.app U).hom
              (Classical.choose (hrange U x) + Classical.choose (hrange U y)) :=
            ((K.arrow.hom.app U).hom.map_add _ _).symm
    }
    exact NatTrans.mk (fun U => AddCommGrpCat.ofHom (b U)) (by
      intro U V g
      ext x
      apply hi V
      calc
        (K.arrow.hom.app V).hom (Classical.choose (hrange V (G.obj.left.obj.map g x))) =
            (α.hom.app V).hom (G.obj.left.obj.map g x) :=
          Classical.choose_spec (hrange V (G.obj.left.obj.map g x))
        _ = (push.obj H).obj.map g ((α.hom.app U).hom x) := by
          simpa only [ConcreteCategory.comp_apply] using
            ConcreteCategory.congr_hom (α.hom.naturality g) x
        _ = (push.obj H).obj.map g
            ((K.arrow.hom.app U).hom (Classical.choose (hrange U x))) := by
          rw [Classical.choose_spec (hrange U x)]
        _ = (K.arrow.hom.app V).hom
            (K.obj.left.obj.map g (Classical.choose (hrange U x))) := by
          simpa only [ConcreteCategory.comp_apply] using
            (ConcreteCategory.congr_hom (K.arrow.hom.naturality g)
              (Classical.choose (hrange U x))).symm)
  let m : G.obj.left ⟶ K.obj.left := Sheaf.homEquiv.symm mp
  refine ⟨m, ?_⟩
  apply Sheaf.hom_ext
  change mp ≫ K.arrow.hom = G.arrow.hom ≫ (push.map φ).hom
  ext V x
  change K.arrow.hom.app V (Classical.choose (hrange V x)) =
    (push.map φ).hom.app V ((G.arrow.hom.app V) x)
  exact Classical.choose_spec (hrange V x)

/-- The proper-support direct image takes identity morphisms to identities. -/
@[stacks 0F53 "open_inclusion_compatibility: identity"]
public theorem fShriekMap_id
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}) :
    (fShriekMap B f F F (𝟙 F)).val = 𝟙 _ := by
  classical
  let G := (SmallEtale.fShriekSubsheaf B f F).val
  let push := (smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
  apply (cancel_mono G.arrow).1
  calc
    (fShriekMap B f F F (𝟙 F)).val ≫ G.arrow = G.arrow ≫ push.map (𝟙 F) :=
      (fShriekMap B f F F (𝟙 F)).property
    _ = 𝟙 _ ≫ G.arrow := by simp [push]

/-- The proper-support direct image respects composition of sheaf morphisms. -/
@[stacks 0F53 "open_inclusion_compatibility: composition"]
public theorem fShriekMap_comp
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)]
    (F H K : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (φ : F ⟶ H) (ψ : H ⟶ K) :
    (fShriekMap B f F K (φ ≫ ψ)).val =
      (fShriekMap B f F H φ).val ≫ (fShriekMap B f H K ψ).val := by
  classical
  let G := (SmallEtale.fShriekSubsheaf B f F).val
  let M := (SmallEtale.fShriekSubsheaf B f H).val
  let N := (SmallEtale.fShriekSubsheaf B f K).val
  let push := (smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
  let mφ := fShriekMap B f F H φ
  let mψ := fShriekMap B f H K ψ
  let mcomp := fShriekMap B f F K (φ ≫ ψ)
  have hφ : mφ.val ≫ M.arrow = G.arrow ≫ push.map φ := mφ.property
  have hψ : mψ.val ≫ N.arrow = M.arrow ≫ push.map ψ := mψ.property
  apply (cancel_mono N.arrow).1
  calc
    mcomp.val ≫ N.arrow = G.arrow ≫ push.map (φ ≫ ψ) := mcomp.property
    _ = G.arrow ≫ push.map φ ≫ push.map ψ := by
      rw [Functor.map_comp]
    _ = (mφ.val ≫ M.arrow) ≫ push.map ψ :=
      (congrArg (fun t => t ≫ push.map ψ) hφ).symm
    _ = mφ.val ≫ (mψ.val ≫ N.arrow) := by rw [Category.assoc, hψ]
    _ = (mφ.val ≫ mψ.val) ≫ N.arrow := (Category.assoc _ _ _).symm

private lemma supportSection_map_mono
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (φ : F ⟶ G) (U : SmallEtale B S hS) (s : F.obj.obj (op U)) :
    SmallEtale.supportSection B S hS G U (φ.hom.app (op U) s) ⊆
      SmallEtale.supportSection B S hS F U s := by
  have hzero : SmallEtale.zeroOpen B S hS F U s ≤
      SmallEtale.zeroOpen B S hS G U (φ.hom.app (op U) s) := by
    unfold SmallEtale.zeroOpen
    apply sSup_le
    rintro W ⟨T, g, hgOpen, hW, hzero⟩
    show (W : Set ((SmallEtale.toScheme B S hS).obj U)) ⊆
      (SmallEtale.zeroOpen B S hS G U (φ.hom.app (op U) s) : Set _)
    rw [hW]
    let : IsOpenImmersion ((SmallEtale.toScheme B S hS).map g) := hgOpen
    exact (SmallEtale.map_eq_zero_iff_le_zeroOpen
      B S hS G U (φ.hom.app (op U) s) T g).mp (by
        calc
          G.obj.map g.op (φ.hom.app (op U) s) =
              φ.hom.app (op T) (F.obj.map g.op s) := by
                simpa only [ConcreteCategory.comp_apply] using
                  (ConcreteCategory.congr_hom (φ.hom.naturality g.op) s).symm
          _ = 0 := by rw [hzero, map_zero])
  intro z hz
  change z ∉ (SmallEtale.zeroOpen B S hS G U
    (φ.hom.app (op U) s) : Set _ ) at hz
  show z ∉ (SmallEtale.zeroOpen B S hS F U s : Set _)
  intro hf
  exact hz (hzero hf)

private lemma zeroOpen_neg_eq
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U : SmallEtale B S hS) (s : F.obj.obj (op U)) :
    SmallEtale.zeroOpen B S hS F U (-s) =
      SmallEtale.zeroOpen B S hS F U s := by
  have key (t : F.obj.obj (op U)) :
      SmallEtale.zeroOpen B S hS F U (-t) ≤ SmallEtale.zeroOpen B S hS F U t := by
    unfold SmallEtale.zeroOpen
    apply sSup_le
    intro W hW
    apply le_sSup
    rcases hW with ⟨V, f, hf, hW, hzero⟩
    exact ⟨V, f, hf, hW, by simpa using congrArg Neg.neg hzero⟩
  exact le_antisymm (key s) (by simpa using key (-s))

private lemma section_eq_of_support_subset_open
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U U' : SmallEtale B S hS) (φ : U' ⟶ U)
    [IsOpenImmersion ((SmallEtale.toScheme B S hS).map φ)]
    (a b : F.obj.obj (op U))
    (ha : SmallEtale.supportSection B S hS F U a ⊆
      Set.range ((SmallEtale.toScheme B S hS).map φ).base)
    (hb : SmallEtale.supportSection B S hS F U b ⊆
      Set.range ((SmallEtale.toScheme B S hS).map φ).base)
    (hres : F.obj.map φ.op a = F.obj.map φ.op b) : a = b := by
  let d := a - b
  have hds : SmallEtale.supportSection B S hS F U d ⊆
      SmallEtale.supportSection B S hS F U a ∪
        SmallEtale.supportSection B S hS F U b := by
    simpa [d, sub_eq_add_neg, supportSection_neg_eq] using
      SmallEtale.supportSection_add_subset B S hS F U a (-b)
  have hzero : F.obj.map φ.op d = 0 := by
    dsimp [d]
    rw [map_sub, hres, sub_self]
  have hopen :
      ((SmallEtale.toScheme B S hS).map φ).opensRange ≤
        SmallEtale.zeroOpen B S hS F U d :=
    (SmallEtale.map_eq_zero_iff_le_zeroOpen
      B S hS F U d U' φ).mp hzero
  have hall : (Set.univ : Set ((SmallEtale.toScheme B S hS).obj U)) ⊆
      SmallEtale.zeroOpen B S hS F U d := by
    intro x _
    by_cases hx : x ∈ Set.range ((SmallEtale.toScheme B S hS).map φ).base
    · have hx' : x ∈ ((SmallEtale.toScheme B S hS).map φ).opensRange := by
        simpa [Scheme.Hom.opensRange] using hx
      exact hopen hx'
    · have hxnot : x ∉ SmallEtale.supportSection B S hS F U d :=
        fun hs => hx (hds.trans (Set.union_subset ha hb) hs)
      simpa [SmallEtale.supportSection] using hxnot
  have hzero' : F.obj.map (𝟙 U).op d = 0 :=
    (SmallEtale.map_eq_zero_iff_le_zeroOpen B S hS F U d U (𝟙 U)).2
      fun x _ => hall (Set.mem_univ x)
  exact sub_eq_zero.mp (by simpa using hzero')

private lemma sections_eq_of_support_eq_under_closed_restriction
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U U' : SmallEtale B S hS) (φ : U' ⟶ U)
    (Z' : Scheme.{u}) (i : Z' ⟶ (SmallEtale.toScheme B S hS).obj U')
    [IsClosedImmersion i]
    [IsClosedImmersion (i ≫ (SmallEtale.toScheme B S hS).map φ)]
    (hpre : Set.preimage ((SmallEtale.toScheme B S hS).map φ).base
        (Set.range (i ≫ (SmallEtale.toScheme B S hS).map φ).base) =
      Set.preimage ((SmallEtale.toScheme B S hS).map (𝟙 U')).base
        (Set.range i.base))
    (a b : F.obj.obj (op U))
    (ha : SmallEtale.supportSection B S hS F U a ⊆
      Set.range (i ≫ (SmallEtale.toScheme B S hS).map φ).base)
    (hb : SmallEtale.supportSection B S hS F U b ⊆
      Set.range (i ≫ (SmallEtale.toScheme B S hS).map φ).base)
    (hab : F.obj.map φ.op a = F.obj.map φ.op b) : a = b := by
  let e := SmallEtale.supportedSectionsEquiv B S hS F U U' φ Z' i
  have hpre' : Set.preimage
      ((SmallEtale.toScheme B S hS).map (𝟙 U' ≫ φ)).base
        (Set.range (i ≫ (SmallEtale.toScheme B S hS).map φ).base) =
      Set.preimage ((SmallEtale.toScheme B S hS).map (𝟙 U')).base
        (Set.range i.base) := by
    simpa using hpre
  have hrefl (c : F.obj.obj (op U)) (hc : SmallEtale.supportSection B S hS F U c ⊆
      Set.range (i ≫ (SmallEtale.toScheme B S hS).map φ).base) :
      F.obj.map (𝟙 U').op (e ⟨c, hc⟩).val = F.obj.map (𝟙 U' ≫ φ).op c :=
    SmallEtale.supportedSectionsEquiv_restrict B S hS F U U' φ Z' i U'
      (𝟙 U') hpre' ⟨c, hc⟩
  have heq : e ⟨a, ha⟩ = e ⟨b, hb⟩ := by
    apply Subtype.ext
    simpa [ConcreteCategory.comp_apply] using (hrefl a ha).trans (hab.trans (hrefl b hb).symm)
  exact congrArg Subtype.val ((Equiv.injective e) heq)

/-- The sectionwise form of the characterising equation of `fShriekMap`. -/
public theorem fShriekMap_val_app
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)]
    (F H : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (φ : F ⟶ H) (V : (SmallEtale B Y.obj Y.property)ᵒᵖ)
    (x : (SmallEtale.fShriekSubsheaf B f F).val.obj.left.obj.obj V) :
    (SmallEtale.fShriekSubsheaf B f H).val.arrow.hom.app V
        ((fShriekMap B f F H φ).val.hom.app V x) =
      φ.hom.app (op ((smallEtaleBaseChange B f).obj V.unop))
        ((SmallEtale.fShriekSubsheaf B f F).val.arrow.hom.app V x) := by
  let G := (SmallEtale.fShriekSubsheaf B f F).val
  let K := (SmallEtale.fShriekSubsheaf B f H).val
  let m := fShriekMap B f F H φ
  let push := (smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
  have hpV : m.val.hom.app V ≫ K.arrow.hom.app V =
      G.arrow.hom.app V ≫ (push.map φ).hom.app V := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using
      NatTrans.congr_app (congrArg (fun k => k.hom) m.property) V
  have hpVal : K.arrow.hom.app V (m.val.hom.app V x) =
      ((push.map φ).hom.app V) (G.arrow.hom.app V x) :=
    ConcreteCategory.congr_hom hpV x
  exact hpVal.trans (congrArg (fun g => g (G.arrow.hom.app V x))
    (Functor.sheafPushforwardContinuous_map_hom_app (smallEtaleBaseChange B f) AddCommGrpCat.{v}
      (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property) φ V))

/-- The counit of post-composition with an open immersion factors as an isomorphism followed by
the projection of the fibre product. -/
private theorem postcomposeCounit_eq_iso_comp_fst
    (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)] (W : SmallEtale B X.obj X.property) :
    ∃ e : (SmallEtale.toScheme B X.obj X.property).obj
        ((smallEtalePostcompose B X.obj X.property (openSiteObject B j)).obj
          ((smallEtaleBaseChange B j).obj W)) ≅ _,
      (SmallEtale.toScheme B X.obj X.property).map
        ((smallEtalePostcomposeAdjunction B j).counit.app W) =
        e.hom ≫ B.inclusion.map (pullback.fst W.obj.hom j) := by
  have hpost : SmallEtale.inclusion B X'.obj X'.property ⋙ Over.map j =
      smallEtalePostcompose B X.obj X.property (openSiteObject B j) ⋙
        SmallEtale.inclusion B X.obj X.property := rfl
  have hbase : SmallEtale.inclusion B X.obj X.property ⋙ Over.pullback j =
      smallEtaleBaseChange B j ⋙
        SmallEtale.inclusion B X'.obj X'.property := rfl
  let W' := (smallEtaleBaseChange B j).obj W
  let a := B.inclusion.map ((Over.forget (B.obj X.obj X.property)).map
    ((eqToIso hpost).inv.app W'))
  let b := B.inclusion.map ((Over.forget (B.obj X.obj X.property)).map
    ((Over.map j).map ((eqToIso hbase).inv.app W)))
  let c := B.inclusion.map ((Over.forget (B.obj X.obj X.property)).map
    (Over.homMk
      (U := (Over.map j).obj ((Over.pullback j).obj W.obj))
      (V := W.obj) (pullback.fst W.obj.hom j)
      (by exact pullback.condition)))
  have : IsIso a := inferInstanceAs (IsIso (B.inclusion.map _))
  have : IsIso b := inferInstanceAs (IsIso (B.inclusion.map _))
  have hqcomp : (SmallEtale.toScheme B X.obj X.property).map
      ((smallEtalePostcomposeAdjunction B j).counit.app W) = a ≫ b ≫ c := by
    cases hpost
    cases hbase
    let iX := SmallEtale.inclusion B X.obj X.property
    change B.inclusion.map ((Over.forget (B.obj X.obj X.property)).map
      (iX.map (((Over.mapPullbackAdj j).restrictFullyFaithful
        (ObjectProperty.fullyFaithfulι _)
        (ObjectProperty.fullyFaithfulι _)
        (eqToIso rfl) (eqToIso rfl)).counit.app W))) = _
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    simp [a, b, c, eqToIso, eqToHom, Over.mapPullbackAdj_counit_app]
    rfl
  exact ⟨asIso (a ≫ b), by rw [asIso_hom, hqcomp, Category.assoc]; rfl⟩

/-- The counit of post-composition with an open immersion is an open immersion of schemes. -/
public theorem isOpenImmersion_toScheme_map_postcomposeCounit
    (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)] (W : SmallEtale B X.obj X.property) :
    IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtalePostcomposeAdjunction B j).counit.app W)) := by
  obtain ⟨e, he⟩ := postcomposeCounit_eq_iso_comp_fst B j W
  rw [he]
  have : IsOpenImmersion (B.inclusion.map (pullback.fst W.obj.hom j)) := by
    let := hasPullbacks_bigEtaleSite B
    let := preservesPullbacks_bigEtaleSiteInclusion B
    exact MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback W.obj.hom j).flip.map B.inclusion)
      (inferInstance : IsOpenImmersion (B.inclusion.map j))
  infer_instance

/-- The image of the projection of the fibre product with an open subscheme lies in the image
of the counit of post-composition. -/
public theorem range_pullback_fst_subset_range_postcomposeCounit
    (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)] (W : SmallEtale B X.obj X.property) :
    Set.range (B.inclusion.map (pullback.fst W.obj.hom j)).base ⊆
      Set.range ((SmallEtale.toScheme B X.obj X.property).map
        ((smallEtalePostcomposeAdjunction B j).counit.app W)).base := by
  obtain ⟨e, he⟩ := postcomposeCounit_eq_iso_comp_fst B j W
  have hsurj : Function.Surjective e.hom.base :=
    (TopCat.homeoOfIso (asIso e.hom.base)).surjective
  rw [he]
  rintro z ⟨z', rfl⟩
  obtain ⟨z'', rfl⟩ := hsurj z'
  exact ⟨z'', rfl⟩

/-- Sections with the same image under the unit of restriction along an open immersion have the
same restriction along the counit of post-composition. -/
public theorem map_postcomposeCounit_eq_of_unit_eq
    (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)]
    (H : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (W : SmallEtale B X.obj X.property) (t t' : H.obj.obj (op W))
    (h : (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).unit.app H).hom.app (op W) t =
        (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).unit.app H).hom.app (op W) t') :
    H.obj.map ((smallEtalePostcomposeAdjunction B j).counit.app W).op t =
      H.obj.map ((smallEtalePostcomposeAdjunction B j).counit.app W).op t' := by
  let jObj : SmallEtale B X.obj X.property := openSiteObject B j
  let post := smallEtalePostcompose B X.obj X.property jObj
  let adjSite := smallEtalePostcomposeAdjunction B j
  have : post.IsContinuous
      (SmallEtale.topology B X'.obj X'.property)
      (SmallEtale.topology B X.obj X.property) :=
    smallEtalePostcompose_isContinuous
      B X.obj X.property jObj
  have : (smallEtaleBaseChange B j).IsContinuous
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property) :=
    smallEtaleBaseChange_isContinuous B j
  let pushJ := (smallEtaleBaseChange B j).sheafPushforwardContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X'.obj X'.property)
  let adjRestrict : post.sheafPushforwardContinuous AddCommGrpCat.{v}
      (SmallEtale.topology B X'.obj X'.property)
      (SmallEtale.topology B X.obj X.property) ⊣ pushJ :=
    adjSite.sheafPushforwardContinuous
      (SmallEtale.topology B X'.obj X'.property)
      (SmallEtale.topology B X.obj X.property)
  have : ((smallEtaleBaseChange B j).sheafPushforwardContinuous
      AddCommGrpCat.{v} (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).IsRightAdjoint :=
    openInclusionSheafPushforward_isRightAdjoint B j
  let adjJ := (smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X'.obj X'.property)
  let κ := Adjunction.leftAdjointUniq adjRestrict adjJ
  have hunitComp := Adjunction.unit_leftAdjointUniq_hom_app adjRestrict adjJ H
  have hηordinary (s : H.obj.obj (op W)) :
      (adjRestrict.unit.app H).hom.app (op W) s = H.obj.map (adjSite.counit.app W).op s := by
    show ((Adjunction.whiskerLeft AddCommGrpCat adjSite.op).unit.app H.obj).app
        (op W) s = H.obj.map (adjSite.counit.app W).op s
    rfl
  refine (hηordinary t).symm.trans (Eq.trans ?_ (hηordinary t'))
  have hcomp : (adjRestrict.unit.app H).hom.app (op W) ≫
        (pushJ.map (κ.hom.app H)).hom.app (op W) =
      (adjJ.unit.app H).hom.app (op W) := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using
      NatTrans.congr_app (congrArg (fun k => k.hom) hunitComp) (op W)
  have hcomp₁' : ((pushJ.map (κ.hom.app H)).hom.app (op W))
        ((adjRestrict.unit.app H).hom.app (op W) t) =
      (adjJ.unit.app H).hom.app (op W) t :=
    ConcreteCategory.congr_hom hcomp t
  have hcomp₂' : ((pushJ.map (κ.hom.app H)).hom.app (op W))
        ((adjRestrict.unit.app H).hom.app (op W) t') =
      (adjJ.unit.app H).hom.app (op W) t' :=
    ConcreteCategory.congr_hom hcomp t'
  have : IsIso ((pushJ.map (κ.hom.app H)).hom.app (op W)) := by infer_instance
  have hinj : Function.Injective ((pushJ.map (κ.hom.app H)).hom.app (op W)) :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  exact hinj (hcomp₁'.trans (h.trans hcomp₂'.symm))

/-- Pushing a section along `φ` commutes with extension by zero from an open subscheme after
applying the unit of restriction along the open immersion. -/
public theorem openInclusionShriekMap_unit_naturality
    (B : BigEtaleSite.{u}) {X' X Y : B.Scheme}
    (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion (B.inclusion.map j)]
    [IsSeparated (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)]
    (F H : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (φ : F ⟶ H) (V : (SmallEtale B Y.obj Y.property)ᵒᵖ) :
    letI : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
      infer_instance
    let pull := (smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)
    let η := ((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).unit.app H
    let W := (smallEtaleBaseChange B f).obj V.unop
    let QH := (SmallEtale.fShriekSubsheaf B f H).val
    ∀ x : (SmallEtale.fShriekSubsheaf B (j ≫ f) (pull.obj F)).val.obj.left.obj.obj V,
      η.hom.app (op W) (QH.arrow.hom.app V ((openInclusionShriekMap B j f H).val.hom.app V
          ((fShriekMap B (j ≫ f) (pull.obj F) (pull.obj H) (pull.map φ)).val.hom.app V x))) =
        η.hom.app (op W) (QH.arrow.hom.app V ((fShriekMap B f F H φ).val.hom.app V
          ((openInclusionShriekMap B j f F).val.hom.app V x))) := by
  classical
  let : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
    show LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
    infer_instance
  intro pull η W QH x
  let PF := (SmallEtale.fShriekSubsheaf B (j ≫ f) (pull.obj F)).val
  let PH := (SmallEtale.fShriekSubsheaf B (j ≫ f) (pull.obj H)).val
  let QF := (SmallEtale.fShriekSubsheaf B f F).val
  let m' := fShriekMap B (j ≫ f) (pull.obj F) (pull.obj H) (pull.map φ)
  let aF := openInclusionShriekMap B j f F
  let aH := openInclusionShriekMap B j f H
  let xH := m'.val.hom.app V x
  let tF := QF.arrow.hom.app V (aF.val.hom.app V x)
  let e := (smallEtaleBaseChange_compIso B X' X Y j f).val
  have hαF := (aF.property.2 V.unop x).1
  have hαH := (aH.property.2 V.unop xH).1
  let tL := QH.arrow.hom.app V (aH.val.hom.app V xH)
  let tR := QH.arrow.hom.app V ((fShriekMap B f F H φ).val.hom.app V (aF.val.hom.app V x))
  have hR : tR = φ.hom.app (op W) tF := fShriekMap_val_app B f F H φ V (aF.val.hom.app V x)
  show (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).unit.app H).hom.app (op W) tL =
      (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).unit.app H).hom.app (op W) tR
  let U := (smallEtaleBaseChange B j).obj W
  let adj := (smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X'.obj X'.property)
  have hm' : PH.arrow.hom.app V (m'.val.hom.app V x) =
      (pull.map φ).hom.app (op ((smallEtaleBaseChange B (j ≫ f)).obj V.unop))
        (PF.arrow.hom.app V x) :=
    fShriekMap_val_app B (j ≫ f) (pull.obj F) (pull.obj H) (pull.map φ) V x
  have hnat := (pull.map φ).hom.naturality (e.hom.app V.unop).op
  have hnatVal := ConcreteCategory.congr_hom hnat (PF.arrow.hom.app V x)
  have hnatVal' :
      (pull.obj H).obj.map (e.hom.app V.unop).op
          ((pull.map φ).hom.app
            (op ((smallEtaleBaseChange B (j ≫ f)).obj V.unop))
            (PF.arrow.hom.app V x)) =
        (pull.map φ).hom.app
          (op ((smallEtaleBaseChange B j).obj ((smallEtaleBaseChange B f).obj V.unop)))
          ((pull.obj F).obj.map (e.hom.app V.unop).op (PF.arrow.hom.app V x)) := by
    convert hnatVal.symm using 1 <;> rfl
  have hηhom := congrArg (fun k => k.hom) (adj.unit.naturality φ)
  have hηapp := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using
      NatTrans.congr_app hηhom (op W)
  have hη := ConcreteCategory.congr_hom hηapp tF
  have hη'' :
      (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).unit.app H).hom.app (op W)
          (φ.hom.app (op W) tF) =
        (pull.map φ).hom.app (op U)
          ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
              (op W) tF) := by
    convert hη using 1
    rfl
  rw [← hαH, hm', hnatVal', hαF, ← hη'', ← hR]

/-- Extension by zero from an open subscheme is natural in the abelian sheaf. -/
@[stacks 0F53 "open_inclusion_compatibility"]
public theorem openInclusionShriekMap_naturality
    (B : BigEtaleSite.{u}) {X' X Y : B.Scheme}
    (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion (B.inclusion.map j)]
    [IsSeparated (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)]
    (F H : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (φ : F ⟶ H) :
    letI : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
      infer_instance
    let pull := (smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)
    (fShriekMap B (j ≫ f) (pull.obj F) (pull.obj H) (pull.map φ)).val ≫
      (openInclusionShriekMap B j f H).val =
        (openInclusionShriekMap B j f F).val ≫
        (fShriekMap B f F H φ).val := by
  classical
  let : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
    show LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
    infer_instance
  dsimp only
  let pull := (smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X'.obj X'.property)
  let QF := (SmallEtale.fShriekSubsheaf B f F).val
  let QH := (SmallEtale.fShriekSubsheaf B f H).val
  apply (cancel_mono QH.arrow).1
  apply Sheaf.hom_ext
  ext V x
  let m' := fShriekMap B (j ≫ f) (pull.obj F) (pull.obj H) (pull.map φ)
  let aF := openInclusionShriekMap B j f F
  let aH := openInclusionShriekMap B j f H
  let m := fShriekMap B f F H φ
  let xH := m'.val.hom.app V x
  let tL := QH.arrow.hom.app V (aH.val.hom.app V xH)
  let tF := QF.arrow.hom.app V (aF.val.hom.app V x)
  let tR := QH.arrow.hom.app V
    (m.val.hom.app V (aF.val.hom.app V x))
  let W := (smallEtaleBaseChange B f).obj V.unop
  have hR : tR = φ.hom.app (op W) tF := fShriekMap_val_app B f F H φ V (aF.val.hom.app V x)
  have hunit :
      (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).unit.app H).hom.app (op W) tL =
        (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).unit.app H).hom.app (op W) tR :=
    openInclusionShriekMap_unit_naturality B j f F H φ V x
  let q := (smallEtalePostcomposeAdjunction B j).counit.app W
  have : IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map q) :=
    isOpenImmersion_toScheme_map_postcomposeCounit B j W
  have hcRange := range_pullback_fst_subset_range_postcomposeCounit B j W
  have htF : SmallEtale.supportSection B X.obj X.property F W tF ⊆
      Set.range ((SmallEtale.toScheme B X.obj X.property).map q).base :=
    (aF.property.2 V.unop x).2.subset.trans ((Set.image_subset_range _ _).trans hcRange)
  have htL : SmallEtale.supportSection B X.obj X.property H W tL ⊆
      Set.range ((SmallEtale.toScheme B X.obj X.property).map q).base :=
    (aH.property.2 V.unop xH).2.subset.trans ((Set.image_subset_range _ _).trans hcRange)
  have htR : SmallEtale.supportSection B X.obj X.property H W tR ⊆
      Set.range ((SmallEtale.toScheme B X.obj X.property).map q).base := by
    rw [hR]
    exact (supportSection_map_mono B X.obj X.property F H φ W tF).trans htF
  exact section_eq_of_support_subset_open B X.obj X.property H W _ q tL tR
    htL htR (map_postcomposeCounit_eq_of_unit_eq B j H W tL tR hunit)

end AlgebraicGeometry.SmallEtale

end
