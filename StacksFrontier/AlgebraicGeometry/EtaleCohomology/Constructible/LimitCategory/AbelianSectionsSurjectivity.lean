module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.AbelianLegComparison

/-!
# Sections of an inverse image of an abelian sheaf over a limit come from a stage

Let `X = lim X_i` be the limit of a directed inverse system of schemes with affine transition
morphisms inside a big étale site `B`, let `G` be an abelian sheaf on the small étale site of
Stacks 021B of a stage `X_i` and `U` a quasi-compact and quasi-separated object of that site.
Every section of `p_i⁻¹G` over `U ×_{X_i} X` comes, through the leg
`AlgebraicGeometry.smallEtaleStageLeg`, from a section of `f_{ji}⁻¹G` over `U ×_{X_i} X_j` for
some stage `j ≥ i`. This is the surjectivity half of the degree zero case of Stacks 09YQ
(Stacks 09YN) on the small étale sites of Stacks 021B.

It is deduced from the same statement on Mathlib's small étale sites,
`Stacks.EtaleCohomology.exists_pullbackSectionsMap_eq_of_isLimit`, through the comparison of the
two legs `AlgebraicGeometry.SmallEtale.smallEtaleStageLeg_restriction`.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_smallEtaleStageLeg_eq_of_restriction` — the statement for
  the restriction of an abelian sheaf on Mathlib's site.
* `AlgebraicGeometry.exists_smallEtaleStageLeg_eq_abelian` — the statement for an arbitrary
  abelian sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.SmallEtale

open Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u})
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (topology B S.obj S.property) (topology B T.obj T.property)).IsRightAdjoint]

/-- Equal morphisms of sheaves agree on sections. -/
private theorem sheaf_hom_apply_congr {A : Type*} [Category* A] {FA : A → A → Type*}
    {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    {C : Type*} [Category* C] {J : GrothendieckTopology C} {F G : Sheaf J A} {α β : F ⟶ G}
    (h : α = β) (U : Cᵒᵖ) (x : ToType (F.obj.obj U)) : α.hom.app U x = β.hom.app U x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg InducedCategory.Hom.hom h) U) x

/-- The inverse of an isomorphism of sheaves undoes it on sections. -/
theorem sheaf_iso_inv_hom_apply {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {F G : Sheaf J AddCommGrpCat.{u + 1}} (e : F ≅ G) (U : Cᵒᵖ) (x : ToType (F.obj.obj U)) :
    e.inv.hom.app U (e.hom.hom.app U x) = x :=
  (((sheafToPresheaf J AddCommGrpCat.{u + 1}).mapIso e).app U).hom_inv_id_apply x

/-- The isomorphism of sheaves undoes its inverse on sections. -/
theorem sheaf_iso_hom_inv_apply {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {F G : Sheaf J AddCommGrpCat.{u + 1}} (e : F ≅ G) (U : Cᵒᵖ) (x : ToType (G.obj.obj U)) :
    e.hom.hom.app U (e.inv.hom.app U x) = x :=
  (((sheafToPresheaf J AddCommGrpCat.{u + 1}).mapIso e).app U).inv_hom_id_apply x

/-- **Surjectivity of the legs transfers from Mathlib's presentation to the bounded one.** Let
`f ≫ g = h`, `H` an abelian sheaf on Mathlib's small étale site of `Z`, `U` an object of the
bounded site of `Z` and `s` a section of `h⁻¹(ρH)` over `U ×_Z X`. If the section of `h⁻¹H`
corresponding to `s` is, after the comparison of direct images, the image of a section under the
leg of Mathlib's presentation, then `s` is the image of a section under the leg of the bounded
presentation. -/
theorem exists_smallEtaleStageLeg_eq_of_restriction {X Y Z : B.Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : X ⟶ Z) (e : f ≫ g = h)
    (H : Sheaf Z.obj.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : SmallEtale B Z.obj Z.property)
    (s : ToType (((smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} h).obj
      ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} h).obj ((abRestriction B Z).obj H))).obj.obj
        (op U)))
    (hm : ∃ t' : ToType (((smallEtalePushforwardAb (B.inclusion.map g)).obj
        ((smallEtalePullbackAb (B.inclusion.map g)).obj H)).obj.obj
          (op ((toEtaleSite B Z.obj Z.property).obj U))),
      ((smallEtalePushforwardAb (B.inclusion.map g)).map
          (smallEtaleAbStageLeg (B.inclusion.map f) (B.inclusion.map g) (B.inclusion.map h)
            ((congrArg B.inclusion.map e).symm.trans (B.inclusion.map_comp f g)) H)).hom.app
          (op ((toEtaleSite B Z.obj Z.property).obj U)) t' =
        ((smallEtalePushforwardAbComp' (B.inclusion.map f) (B.inclusion.map g) (B.inclusion.map h)
          ((congrArg B.inclusion.map e).symm.trans (B.inclusion.map_comp f g))).inv.app
            ((smallEtalePullbackAb (B.inclusion.map h)).obj H)).hom.app
          (op ((toEtaleSite B Z.obj Z.property).obj U))
          (((toEtaleSitePushforwardBaseChangeIso B h AddCommGrpCat.{u + 1}).inv.app
              ((smallEtalePullbackAb (B.inclusion.map h)).obj H)).hom.app (op U)
            (((smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} h).map
              ((abRestrictionPullbackIso B h).hom.app H)).hom.app (op U) s))) :
    ∃ t : ToType (((smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} g).obj
        ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} g).obj
          ((abRestriction B Z).obj H))).obj.obj
          (op U)),
      ((smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} g).map
          (smallEtaleStageLeg B AddCommGrpCat.{u + 1} f g h e ((abRestriction B Z).obj H))).hom.app
          (op U) t =
        ((smallEtalePushforwardCompHom B AddCommGrpCat.{u + 1} f g h e).app
          ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} h).obj
            ((abRestriction B Z).obj H))).hom.app
          (op U) s := by
  obtain ⟨t', ht'⟩ := hm
  set K := (smallEtalePullbackAb (B.inclusion.map h)).obj H
  set βT := (abRestrictionPullbackIso B g).app H
  set βP := (abRestrictionPullbackIso B h).app H
  set Qg := smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} g
  set Qf := smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} f
  set τg := (toEtaleSitePushforwardBaseChangeIso B g AddCommGrpCat.{u + 1})
  set τf := (toEtaleSitePushforwardBaseChangeIso B f AddCommGrpCat.{u + 1})
  set τh := (toEtaleSitePushforwardBaseChangeIso B h AddCommGrpCat.{u + 1})
  set c := smallEtalePushforwardCompHom B AddCommGrpCat.{u + 1} f g h e
  set Λ := smallEtaleStageLeg B AddCommGrpCat.{u + 1} f g h e ((abRestriction B Z).obj H)
  set Λ' := smallEtaleAbStageLeg (B.inclusion.map f) (B.inclusion.map g) (B.inclusion.map h)
    ((congrArg B.inclusion.map e).symm.trans (B.inclusion.map_comp f g)) H
  -- the section `t`
  refine ⟨(Qg.map βT.inv).hom.app (op U)
    ((τg.hom.app ((smallEtalePullbackAb (B.inclusion.map g)).obj H)).hom.app (op U) t'), ?_⟩
  -- the injective map `γ`
  set γ := (Qg.map (Qf.map βP.hom)).hom.app (op U)
  have hγ : Function.Injective γ := by
    intro x y hxy
    have hinv : ∀ z, (Qg.map (Qf.map βP.inv)).hom.app (op U) (γ z) = z := fun z =>
      sheaf_iso_inv_hom_apply (Qg.mapIso (Qf.mapIso βP)) (op U) z
    rw [← hinv x, ← hinv y, hxy]
  apply hγ
  -- the main square, elementwise
  have hT : ∀ x, γ ((Qg.map Λ).hom.app (op U) x) =
      (Qg.map (τf.hom.app K)).hom.app (op U)
        ((Qg.map ((abRestriction B Y).map Λ')).hom.app (op U)
          ((Qg.map βT.hom).hom.app (op U) x)) := fun x =>
    (sheaf_hom_apply_congr (congrArg Qg.map (smallEtaleStageLeg_restriction B f g h e H))
      (op U) x).symm
  have hβ : ∀ z, (Qg.map βT.hom).hom.app (op U) ((Qg.map βT.inv).hom.app (op U) z) = z :=
    fun z => sheaf_iso_hom_inv_apply (Qg.mapIso βT) (op U) z
  have hnat : ∀ x, (Qg.map ((abRestriction B Y).map Λ')).hom.app (op U)
      ((τg.hom.app ((smallEtalePullbackAb (B.inclusion.map g)).obj H)).hom.app (op U) x) =
      (τg.hom.app ((smallEtalePushforwardAb (B.inclusion.map f)).obj K)).hom.app (op U)
        (((smallEtalePushforwardAb (B.inclusion.map g)).map Λ').hom.app
          (op ((toEtaleSite B Z.obj Z.property).obj U)) x) := fun x =>
    (sheaf_hom_apply_congr (τg.hom.naturality Λ') (op U) x).symm
  have hcomp : ∀ z, (Qg.map (τf.hom.app K)).hom.app (op U)
      ((τg.hom.app ((smallEtalePushforwardAb (B.inclusion.map f)).obj K)).hom.app (op U)
      (((smallEtalePushforwardAbComp' (B.inclusion.map f) (B.inclusion.map g) (B.inclusion.map h)
        ((congrArg B.inclusion.map e).symm.trans (B.inclusion.map_comp f g))).inv.app K).hom.app
          (op ((toEtaleSite B Z.obj Z.property).obj U)) z)) =
      (c.app ((abRestriction B X).obj K)).hom.app (op U) ((τh.hom.app K).hom.app (op U) z) :=
    sheaf_hom_apply_congr (abRestriction_pushforwardComp_compat B f g h e K) (op U)
  have hτh : ∀ z, (τh.hom.app K).hom.app (op U) ((τh.inv.app K).hom.app (op U) z) = z :=
    fun z => sheaf_iso_hom_inv_apply (τh.app K) (op U) z
  have hcnat : ∀ z, γ ((c.app _).hom.app (op U) z) =
      (c.app _).hom.app (op U) (((smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} h).map
        βP.hom).hom.app (op U) z) := fun z =>
    (sheaf_hom_apply_congr (c.naturality βP.hom) (op U) z).symm
  rw [hT, hβ]
  refine (congrArg (ConcreteCategory.hom ((Qg.map (τf.hom.app K)).hom.app (op U)))
    (hnat t')).trans ?_
  refine (congrArg (fun z => ConcreteCategory.hom ((Qg.map (τf.hom.app K)).hom.app (op U))
    (ConcreteCategory.hom
      ((τg.hom.app ((smallEtalePushforwardAb (B.inclusion.map f)).obj K)).hom.app
        (op U)) z)) ht').trans ?_
  refine (hcomp _).trans ?_
  refine (congrArg (ConcreteCategory.hom ((c.app ((abRestriction B X).obj K)).hom.app (op U)))
    (hτh _)).trans ?_
  exact (hcnat s).symm

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry

open Stacks.EtaleCohomology SmallEtale

section Transfer

variable (B : BigEtaleSite.{u}) {A : Type*} [Category* A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- The inverse of an isomorphism of sheaves undoes it on sections, for a concrete coefficient
category. -/
theorem sheaf_iso_inv_hom_apply' {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {F G : Sheaf J A} (e : F ≅ G) (U : Cᵒᵖ) (x : ToType (F.obj.obj U)) :
    e.inv.hom.app U (e.hom.hom.app U x) = x :=
  (((sheafToPresheaf J A).mapIso e).app U).hom_inv_id_apply x

/-- **Surjectivity of the legs is invariant under isomorphism of the sheaf.** If every section of
`h⁻¹G'` over `U ×_Z X` is hit by the leg after the comparison of direct images, the same holds
for any sheaf `G` isomorphic to `G'`. -/
theorem exists_smallEtaleStageLeg_eq_of_iso {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e : f ≫ g = h) {G G' : Sheaf (SmallEtale.topology B Z.obj Z.property) A}
    (ε : G ≅ G') (U : SmallEtale B Z.obj Z.property)
    (s : ToType (((smallEtaleSheafPushforward B A h).obj
        ((smallEtaleSheafPullback B A h).obj G)).obj.obj (op U)))
    (hs : ∃ t' : ToType (((smallEtaleSheafPushforward B A g).obj
          ((smallEtaleSheafPullback B A g).obj G')).obj.obj (op U)),
        ((smallEtaleSheafPushforward B A g).map (smallEtaleStageLeg B A f g h e G')).hom.app
            (op U) t' =
          ((smallEtalePushforwardCompHom B A f g h e).app
            ((smallEtaleSheafPullback B A h).obj G')).hom.app (op U)
            (((smallEtaleSheafPushforward B A h).map
              ((smallEtaleSheafPullback B A h).map ε.hom)).hom.app (op U) s)) :
    ∃ t : ToType (((smallEtaleSheafPushforward B A g).obj
        ((smallEtaleSheafPullback B A g).obj G)).obj.obj (op U)),
      ((smallEtaleSheafPushforward B A g).map (smallEtaleStageLeg B A f g h e G)).hom.app
          (op U) t =
        ((smallEtalePushforwardCompHom B A f g h e).app
          ((smallEtaleSheafPullback B A h).obj G)).hom.app (op U) s := by
  let Qg := smallEtaleSheafPushforward B A g
  let Qf := smallEtaleSheafPushforward B A f
  let Qh := smallEtaleSheafPushforward B A h
  let Pg := smallEtaleSheafPullback B A g
  let Ph := smallEtaleSheafPullback B A h
  let c := smallEtalePushforwardCompHom B A f g h e
  obtain ⟨t', ht'⟩ := hs
  refine ⟨(Qg.map (Pg.map ε.inv)).hom.app (op U) t', ?_⟩
  have hnat : ∀ x, (Qg.map (smallEtaleStageLeg B A f g h e G)).hom.app (op U)
      ((Qg.map (Pg.map ε.inv)).hom.app (op U) x) =
      (Qg.map (Qf.map (Ph.map ε.inv))).hom.app (op U)
        ((Qg.map (smallEtaleStageLeg B A f g h e G')).hom.app (op U) x) := fun x => by
    simpa only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.comp_apply] using sheaf_hom_apply_congr
        (congrArg Qg.map (smallEtaleStageLeg_naturality B A f g h e ε.inv)) (op U) x
  have hcnat : ∀ z, (Qg.map (Qf.map (Ph.map ε.inv))).hom.app (op U) ((c.app _).hom.app (op U) z) =
      (c.app _).hom.app (op U) ((Qh.map (Ph.map ε.inv)).hom.app (op U) z) := fun z => by
    simpa only [Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.comp_apply] using
      (sheaf_hom_apply_congr (c.naturality (Ph.map ε.inv)) (op U) z).symm
  refine (hnat t').trans ?_
  refine (congrArg (ConcreteCategory.hom ((Qg.map (Qf.map (Ph.map ε.inv))).hom.app (op U)))
    ht').trans ?_
  refine (hcnat _).trans ?_
  exact congrArg (ConcreteCategory.hom ((c.app _).hom.app (op U)))
    (sheaf_iso_inv_hom_apply' (Qh.mapIso (Ph.mapIso ε)) (op U) s)

end Transfer

section Limit

variable (B : BigEtaleSite.{u})
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- **Sections of an inverse image of an abelian sheaf over a limit come from a stage** (the
surjectivity half of Stacks 09YN, the degree zero case of Stacks 09YQ, on the small étale sites of
Stacks 021B). Let `X = lim X_i` be the limit of a directed inverse system of schemes with affine
transition morphisms, `G` an abelian sheaf on the small étale site of a stage `X_i` and `U` a
quasi-compact and quasi-separated object of that site. Every section of `p_i⁻¹G` over
`U ×_{X_i} X`, read through the comparison of direct images, is the image under the leg
`AlgebraicGeometry.smallEtaleStageLeg` of a section of `f_{ji}⁻¹G` over `U ×_{X_i} X_j` for some
`j ≥ i`. -/
theorem exists_smallEtaleStageLeg_eq_abelian (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e))) {i : I}
    (G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      AddCommGrpCat.{u + 1})
    (U : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    [CompactSpace ((SmallEtale.toScheme B _ _).obj U)]
    [QuasiSeparatedSpace ((SmallEtale.toScheme B _ _).obj U)]
    (s : ToType (((smallEtaleSheafPushforward B AddCommGrpCat.{u + 1}
        (coneStageHom B Dg c hX i)).obj
      ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} (coneStageHom B Dg c hX i)).obj G)).obj.obj
        (op U))) :
    ∃ (j : I) (hij : i ≤ j)
      (t : ToType (((smallEtaleSheafPushforward B AddCommGrpCat.{u + 1}
          (systemStageHom B Dg hij)).obj
        ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} (systemStageHom B Dg hij)).obj G)).obj.obj
          (op U))),
      ((smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} (systemStageHom B Dg hij)).map
          (smallEtaleStageLeg B AddCommGrpCat.{u + 1} (coneStageHom B Dg c hX j)
            (systemStageHom B Dg hij) (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX hij)
            G)).hom.app (op U) t =
        ((smallEtalePushforwardCompHom B AddCommGrpCat.{u + 1} (coneStageHom B Dg c hX j)
          (systemStageHom B Dg hij) (coneStageHom B Dg c hX i)
          (coneStageHom_comp B Dg c hX hij)).app
            ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1}
              (coneStageHom B Dg c hX i)).obj G)).hom.app
          (op U) s := by
  have : Nonempty I := ⟨i⟩
  have : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom ((Dg ⋙ B.inclusion).map e) := fun e => haff e
  let H :=
    (sheafEquiv B (Dg.obj (op i)).obj (Dg.obj (op i)).property AddCommGrpCat.{u + 1}).functor.obj G
  let ε : G ≅ (abRestriction B (Dg.obj (op i))).obj H :=
    asIso ((toEtaleSiteRestrictionAdjunction B AddCommGrpCat.{u + 1} (Dg.obj (op i))).unit.app G)
  let V₀ := (toEtaleSite B (Dg.obj (op i)).obj (Dg.obj (op i)).property).obj U
  have : CompactSpace V₀.left := ‹CompactSpace ((SmallEtale.toScheme B _ _).obj U)›
  have : QuasiSeparatedSpace V₀.left := ‹QuasiSeparatedSpace ((SmallEtale.toScheme B _ _).obj U)›
  let s₂ := ((toEtaleSitePushforwardBaseChangeIso B (coneStageHom B Dg c hX i)
      AddCommGrpCat.{u + 1}).inv.app
        ((smallEtalePullbackAb (B.inclusion.map (coneStageHom B Dg c hX i))).obj H)).hom.app (op U)
    (((smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} (coneStageHom B Dg c hX i)).map
      ((abRestrictionPullbackIso B (coneStageHom B Dg c hX i)).hom.app H)).hom.app (op U)
      (((smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} (coneStageHom B Dg c hX i)).map
        ((smallEtaleSheafPullback B AddCommGrpCat.{u + 1} (coneStageHom B Dg c hX i)).map
          ε.hom)).hom.app (op U) s))
  obtain ⟨j', e', t'', ht''⟩ := exists_pullbackSectionsMap_eq_of_isLimit (D := Dg ⋙ B.inclusion)
    hc (i := op i) H V₀ s₂
  obtain ⟨j⟩ := j'
  have hij : i ≤ j := leOfHom e'.unop
  obtain rfl : e' = (homOfLE hij).op := Subsingleton.elim _ _
  refine ⟨j, hij, ?_⟩
  refine exists_smallEtaleStageLeg_eq_of_iso B _ _ _ (coneStageHom_comp B Dg c hX hij) ε U s ?_
  refine SmallEtale.exists_smallEtaleStageLeg_eq_of_restriction B _ _ _
    (coneStageHom_comp B Dg c hX hij) H U _ ⟨t'', ?_⟩
  rw [smallEtalePushforwardAbComp'_inv_app_hom_app]
  refine Eq.trans ?_ (congrArg (ConcreteCategory.hom
    (((smallEtalePullbackAb (c.π.app (op i))).obj H).obj.map
      ((smallEtaleBaseChangeComp' (c.π.app (op j)) ((Dg ⋙ B.inclusion).map (homOfLE hij).op)
        (c.π.app (op i)) (c.w (homOfLE hij).op).symm).inv.app V₀).op)) ht'')
  exact ((((smallEtalePullbackAb (c.π.app (op i))).obj H).obj.mapIso
    ((smallEtaleBaseChangeComp' (c.π.app (op j)) ((Dg ⋙ B.inclusion).map (homOfLE hij).op)
        (c.π.app (op i)) (c.w (homOfLE hij).op).symm).app V₀).op).hom_inv_id_apply _).symm

end Limit

end AlgebraicGeometry
