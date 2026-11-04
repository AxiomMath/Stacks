module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

/-!
# Faithfulness of the small étale ringed topos of a scheme

Let `X` and `Y` be schemes of a big étale site `B`. A morphism `a : X ⟶ Y` induces a morphism
of small étale ringed topoi `(a_small, a_small^♯)`: the direct image is base change of étale
`Y`-schemes along `a`, read on sheaves, and the structure map pulls a global function on an
étale `V / Y` back along the projection `X ×_Y V ⟶ V`.

Stacks 04LW says that this construction is *faithful*: two morphisms `a, b : X ⟶ Y` whose
induced morphisms of ringed topoi are 2-isomorphic are equal.

The argument is the one of the source. A 2-isomorphism is in particular an isomorphism
`t : a_* ≅ b_*` of the direct-image functors. The small étale topology is subcanonical, so a
sheaf of the form `h_V` corepresents the sections of the direct image over `V`; an isomorphism
of direct images therefore comes from an isomorphism `X ×_Y V ≅ X ×_Y V` of étale `X`-schemes,
for every étale `V / Y`. Taking for `V` an open subscheme `U ⊆ Y`, both fibre products are
open subschemes of `X`, with images `a⁻¹(U)` and `b⁻¹(U)`; an isomorphism over `X` between
them forces `a⁻¹(U) = b⁻¹(U)`. Hence `a` and `b` agree on underlying topological spaces.
The compatibility of `t` with the two structure maps, read at such a `U` on a section
`s ∈ 𝒪_Y(U)`, then says that `a^♯(s)` and `b^♯(s)` agree in `𝒪_X(a⁻¹(U)) = 𝒪_X(b⁻¹(U))`,
which is the remaining half of `a = b`.

## Main definitions

* `AlgebraicGeometry.baseChangeProjection` and `AlgebraicGeometry.smallEtaleProjection` are the
  projection `X ×_Y V ⟶ V` of a base change, as a transformation of functors on the slice
  category and on the small étale site.
* `AlgebraicGeometry.structureSharp` is the structure map `a_small^♯ : 𝒪_Y ⟶ a_{small,*} 𝒪_X`
  of the small étale sites of a morphism of schemes.
* `AlgebraicGeometry.setStructureSheaf` is the structure sheaf of the small étale site as a
  sheaf of sets, the sheaf at which a 2-morphism of the ringed topoi is evaluated.

## Main results

* `AlgebraicGeometry.eq_of_smallEtale_twoIso` is Stacks 04LW, with the compatibility with the
  structure maps read on sections, and
  `AlgebraicGeometry.eq_of_smallEtale_twoIso_comm` is the same statement with that
  compatibility written as an equation between morphisms of sheaves.

## Implementation notes

The hypotheses are the *data* of a 2-isomorphism of ringed topoi, spelled out: an isomorphism
of the direct-image functors together with the commutation with the two structure maps. Nothing
is assumed about the inverse images — a morphism of ringed topoi carries an exact inverse image,
but a 2-morphism between two of them is a transformation of the direct images and an equation,
and those are what is assumed here. So a 2-isomorphism in the 2-category of ringed topoi gives
these hypotheses by taking its underlying transformation and its compatibility square, and the
conclusion `a = b` is an equality of morphisms of schemes.

Sheaves are taken with values in `Type u`, the universe of the morphisms of the small étale
site and of the sections of its structure sheaf; this is the universe in which the structure
map lives, so it is the one in which the compatibility square can be read.

The schemes are objects of a big étale site `B`, as everywhere in this chapter: the small étale
site of a scheme is only defined relative to such a choice.

## References

* [Stacks Project, Tag 04LW](https://stacks.math.columbia.edu/tag/04LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

section Corepresentability

universe vC uC vD uD

variable {C : Type uC} [Category.{vC, uC} C] {D : Type uD} [Category.{vD, uD} D]

private theorem exists_coyoneda_iso_of_sheafPushforwardContinuous_iso
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [K.Subcanonical]
    (F G : C ⥤ D) [F.IsContinuous J K] [G.IsContinuous J K]
    (t : F.sheafPushforwardContinuous (Type vD) J K ≅
      G.sheafPushforwardContinuous (Type vD) J K) (V : C) :
    ∃ ε : coyoneda.obj (op (K.yoneda.obj (F.obj V))) ≅ coyoneda.obj (op (K.yoneda.obj (G.obj V))),
      ∀ (H : Sheaf K (Type vD)) (g : K.yoneda.obj (F.obj V) ⟶ H),
        K.yonedaEquiv (ε.hom.app H g) = (t.hom.app H).hom.app (op V) (K.yonedaEquiv g) := by
  let P := F.sheafPushforwardContinuous (Type vD) J K
  let Q := G.sheafPushforwardContinuous (Type vD) J K
  let A := K.yoneda.obj (F.obj V)
  let B := K.yoneda.obj (G.obj V)
  let lhs (H : Sheaf K (Type vD)) :
      (A ⟶ H) ≃ (P.obj H).obj.obj (op V) :=
    K.yonedaEquiv (X := F.obj V) (F := H)
  let rhs (H : Sheaf K (Type vD)) :
      (B ⟶ H) ≃ (Q.obj H).obj.obj (op V) :=
    K.yonedaEquiv (X := G.obj V) (F := H)
  have yonedaEquiv_natural (F' : C ⥤ D) [F'.IsContinuous J K] (H H' : Sheaf K (Type vD))
      (α : H ⟶ H') (g : K.yoneda.obj (F'.obj V) ⟶ H) :
      K.yonedaEquiv (g ≫ α) =
        ((F'.sheafPushforwardContinuous (Type vD) J K).map α).hom.app (op V) (K.yonedaEquiv g) := by
    rw [K.yonedaEquiv_comp]
    rfl
  let sectionMap (H : Sheaf K (Type vD)) :
      (P.obj H).obj.obj (op V) ≃ (Q.obj H).obj.obj (op V) :=
    (asIso ((t.app H).hom.hom.app (op V))).toEquiv
  have sectionMap_natural (H H' : Sheaf K (Type vD)) (α : H ⟶ H')
      (x : (P.obj H).obj.obj (op V)) :
      sectionMap H' (((P.map α).hom.app (op V)) x) =
        ((Q.map α).hom.app (op V)) (sectionMap H x) := by
    have htV := congrArg (fun q => q.hom.app (op V)) (t.hom.naturality α)
    have htV' := congrArg (fun q => q x) htV
    change ((t.hom.app H').hom.app (op V))
        (((P.map α).hom.app (op V)) x) =
      ((Q.map α).hom.app (op V))
        (((t.hom.app H).hom.app (op V)) x) at htV'
    simpa only [sectionMap, CategoryTheory.Iso.toEquiv_apply, CategoryTheory.Iso.app_hom,
      asIso_hom] using htV'
  let ecorep : coyoneda.obj (op A) ≅ coyoneda.obj (op B) := by
    refine NatIso.ofComponents (fun H => Equiv.toIso
      ((lhs H).trans ((sectionMap H).trans (rhs H).symm))) ?_
    intro H H' α
    ext g
    show (rhs H').symm (sectionMap H' (lhs H' (g ≫ α))) =
      (rhs H).symm (sectionMap H (lhs H g)) ≫ α
    apply (rhs H').injective
    refine (Equiv.apply_symm_apply _ _).trans ?_
    refine ((congrArg _ (yonedaEquiv_natural F H H' α g)).trans
      (sectionMap_natural H H' α _)).trans ?_
    exact (congrArg _ ((rhs H).apply_symm_apply _).symm).trans (yonedaEquiv_natural G H H' α _).symm
  exact ⟨ecorep, fun H g => (rhs H).apply_symm_apply (sectionMap H (lhs H g))⟩

/-- On a subcanonical site, an isomorphism of the direct images of two continuous functors is,
over each object `V`, the restriction along an isomorphism `F V ≅ G V`.

The sections over `V` of the direct image of a sheaf `H` along `F` are the maps `h_{F V} ⟶ H`,
so an isomorphism of direct images is an isomorphism of the functors corepresented by `h_{F V}`
and `h_{G V}`; Yoneda turns it back into an isomorphism of objects. -/
private theorem exists_iso_of_sheafPushforwardContinuous_iso
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [K.Subcanonical]
    (F G : C ⥤ D) [F.IsContinuous J K] [G.IsContinuous J K]
    (t : F.sheafPushforwardContinuous (Type vD) J K ≅
      G.sheafPushforwardContinuous (Type vD) J K) (V : C) :
    ∃ e : F.obj V ≅ G.obj V,
      ∀ (H : Sheaf K (Type vD))
        (x : (F.sheafPushforwardContinuous (Type vD) J K).obj H |>.obj.obj (op V)),
        ((t.hom.app H).hom.app (op V)) x = H.obj.map (op e.inv) x := by
  obtain ⟨ε, hε⟩ := exists_coyoneda_iso_of_sheafPushforwardContinuous_iso J K F G t V
  let sheafIso := (Coyoneda.fullyFaithful (C := Sheaf K (Type vD))).preimageIso ε
  let e := K.yonedaFullyFaithful.preimageIso (sheafIso.unop.symm)
  refine ⟨e, fun H x => ?_⟩
  let g : K.yoneda.obj (F.obj V) ⟶ H := (K.yonedaEquiv (X := F.obj V) (F := H)).symm x
  have hmap : coyoneda.map sheafIso.hom = ε.hom := by
    dsimp [sheafIso]
    exact Coyoneda.fullyFaithful.map_preimage ε.hom
  have he : K.yoneda.map e.inv = sheafIso.unop.hom := by
    dsimp [e]
    simp
  have hc := congrFun (congrArg (fun n => n.app H) hmap) g
  change (sheafIso.hom).unop ≫ g = ε.hom.app H g at hc
  have hcorep : ε.hom.app H g = K.yoneda.map e.inv ≫ g := by
    rw [he]
    exact (by simpa using hc : sheafIso.unop.hom ≫ g = ε.hom.app H g).symm
  have hx : K.yonedaEquiv g = x := Equiv.apply_symm_apply _ x
  have hn := K.yonedaEquiv_naturality' g (op e.inv)
  rw [hx] at hn
  have h₁ : (t.hom.app H).hom.app (op V) x = K.yonedaEquiv (K.yoneda.map e.inv ≫ g) := by
    rw [← hcorep, hε, hx]
  exact h₁.trans hn.symm

end Corepresentability

variable (B : BigEtaleSite.{u})

/-- The projection `X ×_Y V ⟶ V` of a base change along `a : X ⟶ Y`, as a transformation of
the two forgetful functors of slice categories. -/
public def baseChangeProjection {X Y : B.Scheme} (a : X ⟶ Y) :
    Over.pullback a ⋙ Over.forget X ⟶ Over.forget Y :=
  Functor.whiskerRight (Over.mapPullbackAdj a).counit (Over.forget Y)

/-- At `V / Y`, the base-change projection is the first projection of the fibre product. -/
public theorem baseChangeProjection_app {X Y : B.Scheme} (a : X ⟶ Y) (V : Over Y) :
    (baseChangeProjection B a).app V = pullback.fst V.hom a := rfl

/-- The projection `X ×_Y V ⟶ V` from the base change of an étale `Y`-scheme along
`a : X ⟶ Y`, as a transformation of functors on the small étale site of `Y`. -/
public def smallEtaleProjection {X Y : B.Scheme} (a : X ⟶ Y) :
    smallEtaleBaseChange B a ⋙ SmallEtale.toScheme B X.obj X.property ⟶
      SmallEtale.toScheme B Y.obj Y.property :=
  Functor.whiskerLeft (SmallEtale.inclusion B Y.obj Y.property)
    (Functor.whiskerRight (baseChangeProjection B a) B.inclusion)

/-- At an étale `V / Y`, the projection is the first projection of `X ×_Y V`. -/
public theorem smallEtaleProjection_app {X Y : B.Scheme} (a : X ⟶ Y)
    (V : SmallEtale B Y.obj Y.property) :
    (smallEtaleProjection B a).app V = B.inclusion.map (pullback.fst V.obj.hom a) := rfl

/-- The structure map `a_small^♯ : 𝒪_Y ⟶ a_{small,*} 𝒪_X` of a morphism of schemes, on the
small étale sites: at an étale `V / Y` it pulls a global function on `V` back along the
projection `X ×_Y V ⟶ V`. -/
public def structureSharp {X Y : B.Scheme} (a : X ⟶ Y) :
    SmallEtale.commRingStructureSheaf B Y.obj Y.property ⟶
      ((smallEtaleBaseChange B a).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B X.obj X.property)).obj
        (SmallEtale.commRingStructureSheaf B X.obj X.property) :=
  ⟨Functor.whiskerRight (NatTrans.op (smallEtaleProjection B a)) Scheme.Γ⟩

/-- The structure map is pullback of global functions along the base-change projection. -/
public theorem structureSharp_hom_app {X Y : B.Scheme} (a : X ⟶ Y)
    (V : SmallEtale B Y.obj Y.property) :
    (structureSharp B a).hom.app (op V) =
      Scheme.Γ.map (op (B.inclusion.map (pullback.fst V.obj.hom a))) := rfl

/-- The structure sheaf of the small étale site of `S`, as a sheaf of sets. This is the sheaf
on which a 2-morphism of the ringed topoi is evaluated. -/
public def setStructureSheaf (S : Scheme.{u}) (hS : B.Contains S) :
    Sheaf (SmallEtale.topology B S hS) (Type u) :=
  ⟨(SmallEtale.toScheme B S hS).op ⋙ Scheme.Γ ⋙ forget CommRingCat.{u},
    (isSheaf_iff_isSheaf_of_type _ _).2 (SmallEtale.isSheaf_globalSections B S hS)⟩

/-- An open subscheme of `Y`, regarded as an object of the small étale site of `Y`. -/
private def smallEtaleOpenObject (Y : B.Scheme) (U : (B.inclusion.obj Y).Opens) :
    SmallEtale B Y.obj Y.property :=
  ⟨Over.mk (B.inclusion.preimage
      (show B.inclusion.obj ⟨(↑U : Scheme.{u}),
            lt_of_le_of_lt (Scheme.size_coe_opens_le _ U) Y.property⟩ ⟶ B.inclusion.obj Y
        from U.ι)),
    by
      change Etale (B.inclusion.map (B.inclusion.preimage _))
      rw [B.inclusion.map_preimage]
      infer_instance⟩

/-- The structure morphism of the étale object attached to an open is its open immersion. -/
private theorem smallEtaleOpenObject_hom (Y : B.Scheme) (U : (B.inclusion.obj Y).Opens) :
    B.inclusion.map (smallEtaleOpenObject B Y U).obj.hom = U.ι :=
  B.inclusion.map_preimage _

/-- Equal open immersions have the same image. -/
private theorem opensRange_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} [IsOpenImmersion f]
    [IsOpenImmersion g] (h : f = g) : f.opensRange = g.opensRange := by
  subst h
  rfl

/-- The structure morphism of the étale object attached to an open is an open immersion. -/
private theorem isOpenImmersion_map_openObject_hom (Y : B.Scheme) (U : (B.inclusion.obj Y).Opens) :
    IsOpenImmersion (B.inclusion.map (smallEtaleOpenObject B Y U).obj.hom) := by
  rw [smallEtaleOpenObject_hom]
  exact U.instIsOpenImmersionι

private theorem isOpenImmersion_map_pullbackSnd {X Y : B.Scheme} (c : X ⟶ Y)
    (U : (B.inclusion.obj Y).Opens) :
    IsOpenImmersion (B.inclusion.map (pullback.snd (smallEtaleOpenObject B Y U).obj.hom c)) := by
  have := isOpenImmersion_map_openObject_hom B Y U
  rw [← PreservesPullback.iso_hom_snd B.inclusion (smallEtaleOpenObject B Y U).obj.hom c]
  infer_instance

private theorem opensRange_map_pullbackSnd {X Y : B.Scheme} (c : X ⟶ Y)
    (U : (B.inclusion.obj Y).Opens) :
    haveI := isOpenImmersion_map_pullbackSnd B c U
    (B.inclusion.map (pullback.snd (smallEtaleOpenObject B Y U).obj.hom c)).opensRange =
      (B.inclusion.map c) ⁻¹ᵁ U := by
  let i := (smallEtaleOpenObject B Y U).obj.hom
  have := isOpenImmersion_map_pullbackSnd B c U
  have := isOpenImmersion_map_openObject_hom B Y U
  have hiRange : (B.inclusion.map i).opensRange = U :=
    (@opensRange_eq_of_eq _ _ _ _ ‹_› U.instIsOpenImmersionι
      (smallEtaleOpenObject_hom B Y U)).trans U.opensRange_ι
  calc
    _ = ((PreservesPullback.iso B.inclusion i c).hom ≫
        pullback.snd (B.inclusion.map i) (B.inclusion.map c)).opensRange :=
      opensRange_eq_of_eq (PreservesPullback.iso_hom_snd B.inclusion i c).symm
    _ = (pullback.snd (B.inclusion.map i) (B.inclusion.map c)).opensRange :=
      Scheme.Hom.opensRange_comp_of_isIso _ _
    _ = (B.inclusion.map c) ⁻¹ᵁ U := by
      rw [Scheme.Hom.opensRange_pullbackSnd, hiRange]

private theorem top_le_preimage_map_pullbackSnd {X Y : B.Scheme} (c : X ⟶ Y)
    (U : (B.inclusion.obj Y).Opens) :
    ⊤ ≤ B.inclusion.map (pullback.snd (smallEtaleOpenObject B Y U).obj.hom c) ⁻¹ᵁ
      ((B.inclusion.map c) ⁻¹ᵁ U) := by
  rw [← opensRange_map_pullbackSnd B c U]
  exact fun z _ => ⟨z, rfl⟩

/-- An isomorphism, over `X`, between the base changes along `a` and along `b` of an open
`U ⊆ Y` identifies the two preimages of `U`: both base changes are open subschemes of `X`,
with images `a⁻¹(U)` and `b⁻¹(U)`. -/
private theorem preimage_eq_of_iso {X Y : B.Scheme} (a b : X ⟶ Y)
    (U : (B.inclusion.obj Y).Opens)
    (e : (smallEtaleBaseChange B a).obj (smallEtaleOpenObject B Y U) ≅
      (smallEtaleBaseChange B b).obj (smallEtaleOpenObject B Y U)) :
    (B.inclusion.map a) ⁻¹ᵁ U = (B.inclusion.map b) ⁻¹ᵁ U := by
  have := isOpenImmersion_map_pullbackSnd B a U
  have := isOpenImmersion_map_pullbackSnd B b U
  let eOver := (SmallEtale.inclusion B X.obj X.property).map e.hom
  have hOver : B.inclusion.map eOver.left ≫
      B.inclusion.map (pullback.snd (smallEtaleOpenObject B Y U).obj.hom b) =
        B.inclusion.map (pullback.snd (smallEtaleOpenObject B Y U).obj.hom a) :=
    congrArg B.inclusion.map eOver.w
  have : IsIso eOver := Functor.map_isIso _ e.hom
  have : IsIso eOver.left :=
    ((Over.forget (B.obj X.obj X.property)).mapIso (asIso eOver)).isIso_hom
  have hiso : IsIso (B.inclusion.map eOver.left) := Functor.map_isIso _ eOver.left
  have : IsOpenImmersion (B.inclusion.map eOver.left ≫
      B.inclusion.map (pullback.snd (smallEtaleOpenObject B Y U).obj.hom b)) :=
    @IsOpenImmersion.comp _ _ _ _ _ (IsOpenImmersion.of_isIso _)
      (isOpenImmersion_map_pullbackSnd B b U)
  have hRange : (B.inclusion.map eOver.left ≫
      B.inclusion.map (pullback.snd (smallEtaleOpenObject B Y U).obj.hom b)).opensRange =
        (B.inclusion.map (pullback.snd (smallEtaleOpenObject B Y U).obj.hom a)).opensRange :=
    @opensRange_eq_of_eq _ _ _ _ ‹_› (isOpenImmersion_map_pullbackSnd B a U) hOver
  rw [← opensRange_map_pullbackSnd B a U, ← opensRange_map_pullbackSnd B b U, ← hRange]
  exact @Scheme.Hom.opensRange_comp_of_isIso _ _ _ _ _ hiso (isOpenImmersion_map_pullbackSnd B b U)

/-- Restriction of a section along a commutative square whose left edge is the projection from
a fibre product: pulling `s` back to the fibre product along `p` agrees with pulling it back
along `f` first and then along `q`. -/
private theorem pullback_appLE_section {A Z W : Scheme.{u}}
    (V : W.Opens) (p : A ⟶ V.toScheme) (q : A ⟶ Z) (f : Z ⟶ W)
    (h : p ≫ V.ι = q ≫ f) (s : Γ(W, V)) :
    (p.appLE ⊤ ⊤ (by simp)) ((V.ι.appLE V ⊤ (by simp)) s) =
      (q.appLE (f ⁻¹ᵁ V) ⊤ (by
        rw [← Scheme.Hom.comp_preimage, ← h]
        simp)) (f.app V s) := by
  have eA : (⊤ : A.Opens) ≤ p ⁻¹ᵁ (⊤ : V.toScheme.Opens) := by simp
  have eV : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by simp
  have ePV : (⊤ : A.Opens) ≤ (p ≫ V.ι) ⁻¹ᵁ V := fun x _ => (p.base x).property
  have eQF : (⊤ : A.Opens) ≤ (q ≫ f) ⁻¹ᵁ V := h ▸ ePV
  have eQ : (⊤ : A.Opens) ≤ q ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    simpa only [Scheme.Hom.comp_preimage] using eQF
  have hp := Scheme.Hom.appLE_comp_appLE p V.ι V ⊤ ⊤ eV eA
  have hq := Scheme.Hom.appLE_comp_appLE q f V (f ⁻¹ᵁ V) ⊤ le_rfl eQ
  calc
    (p.appLE ⊤ ⊤ eA) ((V.ι.appLE V ⊤ eV) s) = ((p ≫ V.ι).appLE V ⊤ ePV) s := by
      simpa [Scheme.Hom.appLE, Scheme.Opens.ι_preimage_self] using congrArg (fun φ => φ s) hp
    _ = ((q ≫ f).appLE V ⊤ eQF) s := by simp only [h]
    _ = (q.appLE (f ⁻¹ᵁ V) ⊤ eQ) ((f.appLE V (f ⁻¹ᵁ V) le_rfl) s) :=
      (congrArg (fun φ => φ s) hq).symm
    _ = (q.appLE (f ⁻¹ᵁ V) ⊤ eQ) (f.app V s) := by rw [Scheme.Hom.appLE_eq_app]

/-- An open immersion with image `U` restricts to an isomorphism on the sections over `U`. -/
private theorem openImmersion_appLE_isIso {A Z : Scheme.{u}} (f : A ⟶ Z) [IsOpenImmersion f]
    (U : Z.Opens) (hU : f.opensRange = U) (hpre : ⊤ ≤ f ⁻¹ᵁ U) :
    IsIso (f.appLE U ⊤ hpre) := by
  have hpreEq : f ⁻¹ᵁ U = ⊤ := by
    rw [← hU]
    simp
  have : IsIso (f.app U) := f.isIso_app U (by rw [hU])
  show IsIso (f.app U ≫ A.presheaf.map (homOfLE hpre).op)
  have hmaps : homOfLE hpre = eqToHom hpreEq.symm := Subsingleton.elim _ _
  rw [hmaps]
  infer_instance

private theorem app_top_map_pullbackFst {X Y : B.Scheme} (c : X ⟶ Y)
    (U : (B.inclusion.obj Y).Opens) (s : Γ(B.inclusion.obj Y, U)) :
    (B.inclusion.map (pullback.fst (smallEtaleOpenObject B Y U).obj.hom c)).app ⊤
        ((U.ι.appLE U ⊤ (by simp)) s) =
      (B.inclusion.map (pullback.snd (smallEtaleOpenObject B Y U).obj.hom c)).appLE
        ((B.inclusion.map c) ⁻¹ᵁ U) ⊤ (top_le_preimage_map_pullbackSnd B c U)
        ((B.inclusion.map c).app U s) := by
  have hsq : B.inclusion.map (pullback.fst (smallEtaleOpenObject B Y U).obj.hom c) ≫ U.ι =
      B.inclusion.map (pullback.snd (smallEtaleOpenObject B Y U).obj.hom c) ≫
        B.inclusion.map c := by
    rw [← smallEtaleOpenObject_hom B Y U]
    show B.inclusion.map (pullback.fst (smallEtaleOpenObject B Y U).obj.hom c) ≫
        B.inclusion.map (smallEtaleOpenObject B Y U).obj.hom =
      B.inclusion.map (pullback.snd (smallEtaleOpenObject B Y U).obj.hom c) ≫ B.inclusion.map c
    rw [← Functor.map_comp]
    exact congrArg B.inclusion.map pullback.condition
  rw [Scheme.Hom.app_eq_appLE
    (f := B.inclusion.map (pullback.fst (smallEtaleOpenObject B Y U).obj.hom c))]
  exact pullback_appLE_section U _ _ _ hsq s

private theorem base_eq_of_preimage_eq {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : ∀ U : Y.Opens, f ⁻¹ᵁ U = g ⁻¹ᵁ U) : f.toLRSHom.base = g.toLRSHom.base := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Inseparable.eq
  rw [inseparable_iff_forall_isOpen]
  intro s hs
  have hh := congrArg (fun V : X.Opens => x ∈ (V : Set _)) (h ⟨s, hs⟩)
  change (x ∈ f.toLRSHom.base ⁻¹' s) = (x ∈ g.toLRSHom.base ⁻¹' s) at hh
  exact Iff.of_eq (by simpa only [Set.mem_preimage] using hh)

private theorem app_eq_of_baseChange_iso {X Y : B.Scheme} (a b : X ⟶ Y)
    (U : (B.inclusion.obj Y).Opens)
    (hpre : (B.inclusion.map a) ⁻¹ᵁ U = (B.inclusion.map b) ⁻¹ᵁ U)
    (e : (smallEtaleBaseChange B a).obj (smallEtaleOpenObject B Y U) ≅
      (smallEtaleBaseChange B b).obj (smallEtaleOpenObject B Y U))
    (s : Γ(B.inclusion.obj Y, U))
    (h : (B.inclusion.map (pullback.fst (smallEtaleOpenObject B Y U).obj.hom b)).app ⊤
        ((U.ι.appLE U ⊤ (by simp)) s) =
      (B.inclusion.map ((SmallEtale.inclusion B X.obj X.property).map e.inv).left).app ⊤
        ((B.inclusion.map (pullback.fst (smallEtaleOpenObject B Y U).obj.hom a)).app ⊤
          ((U.ι.appLE U ⊤ (by simp)) s))) :
    (B.inclusion.obj X).presheaf.map (eqToHom hpre.symm).op ((B.inclusion.map a).app U s) =
      (B.inclusion.map b).app U s := by
  let W := (B.inclusion.map b) ⁻¹ᵁ U
  let qA := B.inclusion.map (pullback.snd (smallEtaleOpenObject B Y U).obj.hom a)
  let qB := B.inclusion.map (pullback.snd (smallEtaleOpenObject B Y U).obj.hom b)
  let φ := B.inclusion.map ((SmallEtale.inclusion B X.obj X.property).map e.inv).left
  have : IsOpenImmersion qB := isOpenImmersion_map_pullbackSnd B b U
  have hφ : φ ≫ qA = qB :=
    congrArg B.inclusion.map ((SmallEtale.inclusion B X.obj X.property).map e.inv).w
  have hqA : ⊤ ≤ qA ⁻¹ᵁ W := by
    show ⊤ ≤ qA ⁻¹ᵁ ((B.inclusion.map b) ⁻¹ᵁ U)
    rw [← hpre]
    exact top_le_preimage_map_pullbackSnd B a U
  have hqB : ⊤ ≤ qB ⁻¹ᵁ W := top_le_preimage_map_pullbackSnd B b U
  have htransport : qA.appLE W ⊤ hqA
      ((B.inclusion.obj X).presheaf.map (eqToHom hpre.symm).op ((B.inclusion.map a).app U s)) =
        qA.appLE ((B.inclusion.map a) ⁻¹ᵁ U) ⊤ (top_le_preimage_map_pullbackSnd B a U)
          ((B.inclusion.map a).app U s) := by
    simpa only [ConcreteCategory.comp_apply] using
      congrArg (fun g => g ((B.inclusion.map a).app U s))
        (Scheme.Hom.map_appLE' (f := qA) (top_le_preimage_map_pullbackSnd B a U) hpre.symm)
  have hc : qA.appLE W ⊤ hqA ≫ φ.app ⊤ = qB.appLE W ⊤ hqB := by
    rw [Scheme.Hom.app_eq_appLE (f := φ)]
    exact (Scheme.Hom.appLE_comp_appLE φ qA W ⊤ ⊤ hqA (fun _ _ => trivial)).trans
      (by congr 1)
  have hcomp (z) : φ.app ⊤ (qA.appLE W ⊤ hqA z) = qB.appLE W ⊤ hqB z :=
    congrArg (fun g => g z) hc
  have : IsIso (qB.appLE W ⊤ hqB) :=
    openImmersion_appLE_isIso qB W (opensRange_map_pullbackSnd B b U) hqB
  have hvalues : qB.appLE W ⊤ hqB ((B.inclusion.map b).app U s) = qB.appLE W ⊤ hqB
      ((B.inclusion.obj X).presheaf.map (eqToHom hpre.symm).op ((B.inclusion.map a).app U s)) := by
    rw [← app_top_map_pullbackFst B b U s, h, app_top_map_pullbackFst B a U s, ← htransport,
      hcomp]
  simpa using congrArg (fun z => (asIso (qB.appLE W ⊤ hqB)).inv z) hvalues.symm

/-- **Stacks 04LW.** Let `X` and `Y` be schemes. Two morphisms `a, b : X ⟶ Y` for which there
is a 2-isomorphism `(a_small, a_small^♯) ≅ (b_small, b_small^♯)` in the 2-category of ringed
topoi are equal.

The hypotheses are the data of such a 2-isomorphism: an isomorphism `t` of the direct images,
and the commutation of `t` with the two structure maps. -/
@[stacks 04LW]
public theorem eq_of_smallEtale_twoIso {X Y : B.Scheme} (a b : X ⟶ Y)
    (t : (smallEtaleBaseChange B a).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property) ≅
      (smallEtaleBaseChange B b).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property))
    (hsharp : ∀ (V : SmallEtale B Y.obj Y.property)
        (s : (SmallEtale.commRingStructureSheaf B Y.obj Y.property).obj.obj (op V)),
      (t.hom.app (setStructureSheaf B X.obj X.property)).hom.app (op V)
          ((structureSharp B a).hom.app (op V) s) =
        (structureSharp B b).hom.app (op V) s) :
    a = b := by
  have hpre : ∀ U : (B.inclusion.obj Y).Opens,
      (B.inclusion.map a) ⁻¹ᵁ U = (B.inclusion.map b) ⁻¹ᵁ U := fun U =>
    preimage_eq_of_iso B a b U
      (exists_iso_of_sheafPushforwardContinuous_iso _ _ _ _ t
        (smallEtaleOpenObject B Y U)).choose
  refine B.inclusion.map_injective (Scheme.Hom.ext (base_eq_of_preimage_eq hpre) fun U => ?_)
  ext s
  obtain ⟨e, he⟩ := exists_iso_of_sheafPushforwardContinuous_iso _ _ _ _ t
    (smallEtaleOpenObject B Y U)
  let sv := (U.ι.appLE U ⊤ (by simp)) s
  exact app_eq_of_baseChange_iso B a b U (hpre U) e s
    ((hsharp (smallEtaleOpenObject B Y U) sv).symm.trans
      (he (setStructureSheaf B X.obj X.property) _))

/-- **Stacks 04LW**, with the compatibility with the structure maps written as the commuting
triangle of a 2-morphism of ringed topoi: the composite of `a_small^♯` with `t`, evaluated at
the structure sheaf of `X`, is `b_small^♯`, after forgetting the ring structure of the two
structure sheaves, which is what a 2-morphism of topoi acts on. -/
@[stacks 04LW]
public theorem eq_of_smallEtale_twoIso_comm {X Y : B.Scheme} (a b : X ⟶ Y)
    (t : (smallEtaleBaseChange B a).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property) ≅
      (smallEtaleBaseChange B b).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property))
    (hsharp : (sheafCompose (SmallEtale.topology B Y.obj Y.property)
            (forget CommRingCat.{u})).map (structureSharp B a) ≫
          t.hom.app ((sheafCompose (SmallEtale.topology B X.obj X.property)
            (forget CommRingCat.{u})).obj
            (SmallEtale.commRingStructureSheaf B X.obj X.property)) =
        (sheafCompose (SmallEtale.topology B Y.obj Y.property)
          (forget CommRingCat.{u})).map (structureSharp B b)) :
    a = b :=
  eq_of_smallEtale_twoIso B a b t fun V s => congrArg (fun φ => φ s) (NatTrans.congr_app
    ((sheafToPresheaf (SmallEtale.topology B Y.obj Y.property) (Type u)).congr_map hsharp)
    (op V))

end AlgebraicGeometry

end
